/*
 * windows backend for libusb 1.0
 * Copyright © 2009-2012 Pete Batard <pete@akeo.ie>
 * With contributions from Michael Plante, Orin Eman et al.
 * Parts of this code adapted from libusb-win32-v1 by Stephan Meyer
 * HID Reports IOCTLs inspired from HIDAPI by Alan Ott, Signal 11 Software
 * Hash table functions adapted from glibc, by Ulrich Drepper et al.
 * Major code testing contribution by Xiaofan Chen
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include <config.h>
#include <stdio.h>
#include <inttypes.h>
#include <process.h>


#include "libusbi.h"
#include "windows_common.h"
#include "windows_nt_common.h"

// Global variables
const uint64_t epoch_time = UINT64_C(116444736000000000);	// 1970.01.01 00:00:000 in MS Filetime

// Global variables for clock_gettime mechanism
uint64_t hires_ticks_to_ps;
uint64_t hires_frequency;
volatile LONG request_count[2] = { 0, 1 };	// last one must be > 0
HANDLE timer_request[2] = { NULL, NULL };
HANDLE timer_response = NULL;
HANDLE timer_mutex = NULL;
struct timespec timer_tp;
// Timer thread
// NB: index 0 is for monotonic and 1 is for the thread exit event
HANDLE timer_thread = NULL;

static unsigned __stdcall win_clock_gettime_threaded(void* param);

/*
* Converts a windows error to human readable string
* uses retval as errorcode, or, if 0, use GetLastError()
*/
#if defined(ENABLE_LOGGING)
char *windows_error_str(uint32_t retval)
{
    static char err_string[ERR_BUFFER_SIZE];

    DWORD size;
    ssize_t i;
    uint32_t error_code, format_error;

    error_code = retval ? retval : GetLastError();

    safe_sprintf(err_string, ERR_BUFFER_SIZE, "[%u] ", error_code);

    // Translate codes returned by SetupAPI. The ones we are dealing with are either
    // in 0x0000xxxx or 0xE000xxxx and can be distinguished from standard error codes.
    // See http://msdn.microsoft.com/en-us/library/windows/hardware/ff545011.aspx
    switch (error_code & 0xE0000000) {
    case 0:
        error_code = HRESULT_FROM_WIN32(error_code);	// Still leaves ERROR_SUCCESS unmodified
        break;
    case 0xE0000000:
        error_code = 0x80000000 | (FACILITY_SETUPAPI << 16) | (error_code & 0x0000FFFF);
        break;
    default:
        break;
    }

    size = FormatMessageA(FORMAT_MESSAGE_FROM_SYSTEM, NULL, error_code,
        MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), &err_string[safe_strlen(err_string)],
        ERR_BUFFER_SIZE - (DWORD)safe_strlen(err_string), NULL);
    if (size == 0) {
        format_error = GetLastError();
        if (format_error)
            safe_sprintf(err_string, ERR_BUFFER_SIZE,
            "Windows error code %u (FormatMessage error code %u)", error_code, format_error);
        else
            safe_sprintf(err_string, ERR_BUFFER_SIZE, "Unknown error code %u", error_code);
    }
    else {
        // Remove CR/LF terminators
        for (i = safe_strlen(err_string) - 1; (i >= 0) && ((err_string[i] == 0x0A) || (err_string[i] == 0x0D)); i--) {
            err_string[i] = 0;
        }
    }
    return err_string;
}
#endif

/* Hash table functions - modified From glibc 2.3.2:
   [Aho,Sethi,Ullman] Compilers: Principles, Techniques and Tools, 1986
   [Knuth]            The Art of Computer Programming, part 3 (6.4)  */
typedef struct htab_entry {
	unsigned long used;
	char* str;
} htab_entry;
htab_entry* htab_table = NULL;
usbi_mutex_t htab_write_mutex = NULL;
unsigned long htab_size, htab_filled;

/* For the used double hash method the table size has to be a prime. To
   correct the user given table size we need a prime test.  This trivial
   algorithm is adequate because the code is called only during init and
   the number is likely to be small  */
static int isprime(unsigned long number)
{
	// no even number will be passed
	unsigned int divider = 3;

	while((divider * divider < number) && (number % divider != 0))
		divider += 2;

	return (number % divider != 0);
}

/* Before using the hash table we must allocate memory for it.
   We allocate one element more as the found prime number says.
   This is done for more effective indexing as explained in the
   comment for the hash function.  */
int htab_create(struct libusb_context *ctx, unsigned long nel)
{
	if (htab_table != NULL) {
		usbi_err(ctx, "hash table already allocated");
	}

	// Create a mutex
	usbi_mutex_init(&htab_write_mutex, NULL);

	// Change nel to the first prime number not smaller as nel.
	nel |= 1;
	while(!isprime(nel))
		nel += 2;

	htab_size = nel;
	usbi_dbg("using %d entries hash table", nel);
	htab_filled = 0;

	// allocate memory and zero out.
	htab_table = (htab_entry*) calloc(htab_size + 1, sizeof(htab_entry));
	if (htab_table == NULL) {
		usbi_err(ctx, "could not allocate space for hash table");
		return 0;
	}

	return 1;
}

/* After using the hash table it has to be destroyed.  */
void htab_destroy(void)
{
	size_t i;
	if (htab_table == NULL) {
		return;
	}

	for (i=0; i<htab_size; i++) {
		if (htab_table[i].used) {
			safe_free(htab_table[i].str);
		}
	}
	usbi_mutex_destroy(&htab_write_mutex);
	safe_free(htab_table);
}

/* This is the search function. It uses double hashing with open addressing.
   We use an trick to speed up the lookup. The table is created with one
   more element available. This enables us to use the index zero special.
   This index will never be used because we store the first hash index in
   the field used where zero means not used. Every other value means used.
   The used field can be used as a first fast comparison for equality of
   the stored and the parameter value. This helps to prevent unnecessary
   expensive calls of strcmp.  */
unsigned long htab_hash(char* str)
{
	unsigned long hval, hval2;
	unsigned long idx;
	unsigned long r = 5381;
	int c;
	char* sz = str;

	if (str == NULL)
		return 0;

	// Compute main hash value (algorithm suggested by Nokia)
	while ((c = *sz++) != 0)
		r = ((r << 5) + r) + c;
	if (r == 0)
		++r;

	// compute table hash: simply take the modulus
	hval = r % htab_size;
	if (hval == 0)
		++hval;

	// Try the first index
	idx = hval;

	if (htab_table[idx].used) {
		if ( (htab_table[idx].used == hval)
		  && (safe_strcmp(str, htab_table[idx].str) == 0) ) {
			// existing hash
			return idx;
		}
		usbi_dbg("hash collision ('%s' vs '%s')", str, htab_table[idx].str);

		// Second hash function, as suggested in [Knuth]
		hval2 = 1 + hval % (htab_size - 2);

		do {
			// Because size is prime this guarantees to step through all available indexes
			if (idx <= hval2) {
				idx = htab_size + idx - hval2;
			} else {
				idx -= hval2;
			}

			// If we visited all entries leave the loop unsuccessfully
			if (idx == hval) {
				break;
			}

			// If entry is found use it.
			if ( (htab_table[idx].used == hval)
			  && (safe_strcmp(str, htab_table[idx].str) == 0) ) {
				return idx;
			}
		}
		while (htab_table[idx].used);
	}

	// Not found => New entry

	// If the table is full return an error
	if (htab_filled >= htab_size) {
		usbi_err(NULL, "hash table is full (%d entries)", htab_size);
		return 0;
	}

	// Concurrent threads might be storing the same entry at the same time
	// (eg. "simultaneous" enums from different threads) => use a mutex
	usbi_mutex_lock(&htab_write_mutex);
	// Just free any previously allocated string (which should be the same as
	// new one). The possibility of concurrent threads storing a collision
	// string (same hash, different string) at the same time is extremely low
	safe_free(htab_table[idx].str);
	htab_table[idx].used = hval;
	htab_table[idx].str = (char*) malloc(safe_strlen(str)+1);
	if (htab_table[idx].str == NULL) {
		usbi_err(NULL, "could not duplicate string for hash table");
		usbi_mutex_unlock(&htab_write_mutex);
		return 0;
	}
	memcpy(htab_table[idx].str, str, safe_strlen(str)+1);
	++htab_filled;
	usbi_mutex_unlock(&htab_write_mutex);

	return idx;
}

bool win_init_clock(struct libusb_context *ctx)
{
    // Because QueryPerformanceCounter might report different values when
    // running on different cores, we create a separate thread for the timer
    // calls, which we glue to the first core always to prevent timing discrepancies.

    int i;
    for (i = 0; i < 2; i++) {
        timer_request[i] = CreateEvent(NULL, TRUE, FALSE, NULL);
        if (timer_request[i] == NULL) {
            usbi_err(ctx, "could not create timer request event %d - aborting", i);
            //goto init_exit;
            return false;
        }
    }
    timer_response = CreateSemaphore(NULL, 0, MAX_TIMER_SEMAPHORES, NULL);
    if (timer_response == NULL) {
        usbi_err(ctx, "could not create timer response semaphore - aborting");
        //goto init_exit;
        return false;
    }
    timer_mutex = CreateMutex(NULL, FALSE, NULL);
    if (timer_mutex == NULL) {
        usbi_err(ctx, "could not create timer mutex - aborting");
        //goto init_exit;
        return false;
    }
    timer_thread = (HANDLE)_beginthreadex(NULL, 0, win_clock_gettime_threaded, NULL, 0, NULL);
    if (timer_thread == NULL) {
        usbi_err(ctx, "Unable to create timer thread - aborting");
        //goto init_exit;
        return false;
    }
    SetThreadAffinityMask(timer_thread, 0);

    // Wait for timer thread to init before continuing.
    if (WaitForSingleObject(timer_response, INFINITE) != WAIT_OBJECT_0) {
        usbi_err(ctx, "Failed to wait for timer thread to become ready - aborting");
        //goto init_exit;
        return false;
    }

    return true;
}

void win_destroy_clock()
{
    int i;

    if (timer_thread) {
        SetEvent(timer_request[1]); // actually the signal to quit the thread.
        if (WAIT_OBJECT_0 != WaitForSingleObject(timer_thread, INFINITE)) {
            usbi_dbg("could not wait for timer thread to quit");
            TerminateThread(timer_thread, 1);
        }
        CloseHandle(timer_thread);
        timer_thread = NULL;
    }

    for (i = 0; i < 2; i++) {
        if (timer_request[i]) {
            CloseHandle(timer_request[i]);
            timer_request[i] = NULL;
        }
    }
    if (timer_response) {
        CloseHandle(timer_response);
        timer_response = NULL;
    }
    if (timer_mutex) {
        CloseHandle(timer_mutex);
        timer_mutex = NULL;
    }
}

/*
* Monotonic and real time functions
*/
static unsigned __stdcall win_clock_gettime_threaded(void* param)
{
    LARGE_INTEGER hires_counter, li_frequency;
    LONG nb_responses;
    int timer_index;

    UNREFERENCED_PARAMETER(param);

    // Init - find out if we have access to a monotonic (hires) timer
    if (!QueryPerformanceFrequency(&li_frequency)) {
        usbi_dbg("no hires timer available on this platform");
        hires_frequency = 0;
        hires_ticks_to_ps = UINT64_C(0);
    }
    else {
        hires_frequency = li_frequency.QuadPart;
        // The hires frequency can go as high as 4 GHz, so we'll use a conversion
        // to picoseconds to compute the tv_nsecs part in clock_gettime
        hires_ticks_to_ps = UINT64_C(1000000000000) / hires_frequency;
        usbi_dbg("hires timer available (Frequency: %"PRIu64" Hz)", hires_frequency);
    }

    // Signal windows_init() that we're ready to service requests
    if (ReleaseSemaphore(timer_response, 1, NULL) == 0) {
        usbi_dbg("unable to release timer semaphore: %s", windows_error_str(0));
    }

    // Main loop - wait for requests
    while (1) {
        timer_index = WaitForMultipleObjects(2, timer_request, FALSE, INFINITE) - WAIT_OBJECT_0;
        if ((timer_index != 0) && (timer_index != 1)) {
            usbi_dbg("failure to wait on requests: %s", windows_error_str(0));
            continue;
        }
        if (request_count[timer_index] == 0) {
            // Request already handled
            ResetEvent(timer_request[timer_index]);
            // There's still a possiblity that a thread sends a request between the
            // time we test request_count[] == 0 and we reset the event, in which case
            // the request would be ignored. The simple solution to that is to test
            // request_count again and process requests if non zero.
            if (request_count[timer_index] == 0)
                continue;
        }
        switch (timer_index) {
        case 0:
            WaitForSingleObject(timer_mutex, INFINITE);
            // Requests to this thread are for hires always
            if ((QueryPerformanceCounter(&hires_counter) != 0) && (hires_frequency != 0)) {
                timer_tp.tv_sec = (long)(hires_counter.QuadPart / hires_frequency);
                timer_tp.tv_nsec = (long)(((hires_counter.QuadPart % hires_frequency) / 1000) * hires_ticks_to_ps);
            }
            else {
                // Fallback to real-time if we can't get monotonic value
                // Note that real-time clock does not wait on the mutex or this thread.
                win_clock_gettime(USBI_CLOCK_REALTIME, &timer_tp);
            }
            ReleaseMutex(timer_mutex);

            nb_responses = InterlockedExchange((LONG*)&request_count[0], 0);
            if ((nb_responses)
                && (ReleaseSemaphore(timer_response, nb_responses, NULL) == 0)) {
                usbi_dbg("unable to release timer semaphore: %s", windows_error_str(0));
            }
            continue;
        case 1: // time to quit
            usbi_dbg("timer thread quitting");
            return 0;
        }
    }
}

int win_clock_gettime(int clk_id, struct timespec *tp)
{
    FILETIME filetime;
    ULARGE_INTEGER rtime;
    DWORD r;
    switch (clk_id) {
    case USBI_CLOCK_MONOTONIC:
        if (hires_frequency != 0) {
            while (1) {
                InterlockedIncrement((LONG*)&request_count[0]);
                SetEvent(timer_request[0]);
                r = WaitForSingleObject(timer_response, TIMER_REQUEST_RETRY_MS);
                switch (r) {
                case WAIT_OBJECT_0:
                    WaitForSingleObject(timer_mutex, INFINITE);
                    *tp = timer_tp;
                    ReleaseMutex(timer_mutex);
                    return LIBUSB_SUCCESS;
                case WAIT_TIMEOUT:
                    usbi_dbg("could not obtain a timer value within reasonable timeframe - too much load?");
                    break; // Retry until successful
                default:
                    usbi_dbg("WaitForSingleObject failed: %s", windows_error_str(0));
                    return LIBUSB_ERROR_OTHER;
                }
            }
        }
        // Fall through and return real-time if monotonic was not detected @ timer init
    case USBI_CLOCK_REALTIME:
        // We follow http://msdn.microsoft.com/en-us/library/ms724928%28VS.85%29.aspx
        // with a predef epoch_time to have an epoch that starts at 1970.01.01 00:00
        // Note however that our resolution is bounded by the Windows system time
        // functions and is at best of the order of 1 ms (or, usually, worse)
        GetSystemTimeAsFileTime(&filetime);
        rtime.LowPart = filetime.dwLowDateTime;
        rtime.HighPart = filetime.dwHighDateTime;
        rtime.QuadPart -= epoch_time;
        tp->tv_sec = (long)(rtime.QuadPart / 10000000);
        tp->tv_nsec = (long)((rtime.QuadPart % 10000000) * 100);
        return LIBUSB_SUCCESS;
    default:
        return LIBUSB_ERROR_INVALID_PARAM;
    }
}

void win_handle_callback(struct usbi_transfer *itransfer, uint32_t io_result, uint32_t io_size)
{
    struct libusb_transfer *transfer = USBI_TRANSFER_TO_LIBUSB_TRANSFER(itransfer);

    switch (transfer->type) {
    case LIBUSB_TRANSFER_TYPE_CONTROL:
    case LIBUSB_TRANSFER_TYPE_BULK:
    case LIBUSB_TRANSFER_TYPE_INTERRUPT:
    case LIBUSB_TRANSFER_TYPE_ISOCHRONOUS:
        win_transfer_callback(itransfer, io_result, io_size);
        break;
    case LIBUSB_TRANSFER_TYPE_BULK_STREAM:
        usbi_warn(ITRANSFER_CTX(itransfer), "bulk stream transfers are not yet supported on this platform");
        break;
    default:
        usbi_err(ITRANSFER_CTX(itransfer), "unknown endpoint type %d", transfer->type);
    }
}

void win_transfer_callback(struct usbi_transfer *itransfer, uint32_t io_result, uint32_t io_size)
{
    int status, istatus;

    usbi_dbg("handling I/O completion with errcode %d, size %d", io_result, io_size);

    switch (io_result) {
    case NO_ERROR:
        status = win_backend_copy_transfer_data(itransfer, io_size);
        break;
    case ERROR_GEN_FAILURE:
        usbi_dbg("detected endpoint stall");
        status = LIBUSB_TRANSFER_STALL;
        break;
    case ERROR_SEM_TIMEOUT:
        usbi_dbg("detected semaphore timeout");
        status = LIBUSB_TRANSFER_TIMED_OUT;
        break;
    case ERROR_OPERATION_ABORTED:
        istatus = win_backend_copy_transfer_data(itransfer, io_size);
        if (istatus != LIBUSB_TRANSFER_COMPLETED) {
            usbi_dbg("Failed to copy partial data in aborted operation: %d", istatus);
        }
        if (itransfer->flags & USBI_TRANSFER_TIMED_OUT) {
            usbi_dbg("detected timeout");
            status = LIBUSB_TRANSFER_TIMED_OUT;
        }
        else {
            usbi_dbg("detected operation aborted");
            status = LIBUSB_TRANSFER_CANCELLED;
        }
        break;
    default:
        usbi_err(ITRANSFER_CTX(itransfer), "detected I/O error %d: %s", io_result, windows_error_str(io_result));
        status = LIBUSB_TRANSFER_ERROR;
        break;
    }
    win_backend_clear_transfer_priv(itransfer);	// Cancel polling
    usbi_handle_transfer_completion(itransfer, (enum libusb_transfer_status)status);
}

int win_handle_events(struct libusb_context *ctx, struct pollfd *fds, POLL_NFDS_TYPE nfds, int num_ready)
{
    POLL_NFDS_TYPE i = 0;
    bool found = false;
    struct usbi_transfer *transfer;
    struct winfd *pollable_fd = NULL;
    DWORD io_size, io_result;

    usbi_mutex_lock(&ctx->open_devs_lock);
    for (i = 0; i < nfds && num_ready > 0; i++) {

        usbi_dbg("checking fd %d with revents = %04x", fds[i].fd, fds[i].revents);

        if (!fds[i].revents) {
            continue;
        }

        num_ready--;

        // Because a Windows OVERLAPPED is used for poll emulation,
        // a pollable fd is created and stored with each transfer
        usbi_mutex_lock(&ctx->flying_transfers_lock);
        found = false;
        list_for_each_entry(transfer, &ctx->flying_transfers, list, struct usbi_transfer) {
            pollable_fd = win_backend_get_fd(transfer);
            if (pollable_fd->fd == fds[i].fd) {
                found = true;
                break;
            }
        }
        usbi_mutex_unlock(&ctx->flying_transfers_lock);

        if (found) {
            win_backend_get_overlapped_result(transfer, pollable_fd, &io_result, &io_size);

            usbi_remove_pollfd(ctx, pollable_fd->fd);
            // let handle_callback free the event using the transfer wfd
            // If you don't use the transfer wfd, you run a risk of trying to free a
            // newly allocated wfd that took the place of the one from the transfer.
            win_handle_callback(transfer, io_result, io_size);
        }
        else {
            usbi_mutex_unlock(&ctx->open_devs_lock);
            usbi_err(ctx, "could not find a matching transfer for fd %x", fds[i]);
            return LIBUSB_ERROR_NOT_FOUND;
        }
    }

    usbi_mutex_unlock(&ctx->open_devs_lock);
    return LIBUSB_SUCCESS;
}
