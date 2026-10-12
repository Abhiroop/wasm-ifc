/* The password checker as a service: it accepts one connection on the socket the host listens
 * on for it (descriptor 3), reads a password from the connection, answers on the connection
 * whether the password is weak, and reports on its standard output, which the operator reads,
 * that it served a request. The socket is secret (`listen ADDRESS : H` in the policy), so the
 * connection is too, and the password must not reach the standard output.
 *
 * As in password.c, the code that handles the password asks the host directly
 * (__wasi_sock_recv, __wasi_sock_send), so that the status of a call (public) and the count of
 * bytes (secret like the connection) stay two values, and it does not branch on the password.
 *
 * LEAK selects a variant that leaks:
 *   (none)          the report says only that a request was served
 *   LEAK_CONTROL    the report says whether the password was weak, chosen by a branch (which
 *                   the compiler turns into a choice of the report's length)
 *   LEAK_MEMORY     the report contains the password's hash, through a buffer in memory
 */
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <wasi/api.h>

/* djb2 hashes of the dictionary's weak passwords: "123456", "password", "qwerty", "letmein". */
static const uint32_t weak[] = {0x7dd1705au, 0x17f6dc38u, 0x1818ae71u, 0x715ae1b3u};
#define ENTRIES (sizeof weak / sizeof weak[0])
#define CAPACITY 64

static char password[CAPACITY];
static char report[64];
static const char verdicts[] = "ok\n\0\0weak\n"; /* "ok\n" at 0, "weak\n" at 5 */

/* The djb2 hash of the first length bytes, computed over the whole buffer. */
static uint32_t djb2(const char *text, uint32_t length) {
    uint32_t h = 5381;
    for (uint32_t i = 0; i < CAPACITY; i++) {
        uint32_t keep = -(uint32_t)(i < length);
        uint32_t next = h * 33 + (unsigned char)text[i];
        h = (next & keep) | (h & ~keep);
    }
    return h;
}

/* Write a decimal number into the report at position at; return the new position. */
static int put_number(int at, uint32_t n) {
    char digits[10];
    int count = 0;
    do {
        digits[count++] = (char)('0' + n % 10);
        n /= 10;
    } while (n != 0);
    while (count > 0) report[at++] = digits[--count];
    return at;
}

/* Accept a connection; its descriptor, or -1. The host stores the descriptor in memory, and it
   is public. This is a function of its own so that the load of it is not one of main's, which
   the policy declares secret as a whole (`load-default func`). */
__attribute__((noinline)) static int accept_connection(void) {
    __wasi_fd_t connection;
    if (__wasi_sock_accept(3, 0, &connection) != 0) return -1;
    return (int)connection;
}

/* Start the report to the operator; the position after it. Again a function of its own: the
   compiler copies the text from the module's data by loads, which in main would be secret. */
__attribute__((noinline)) static int begin_report(void) {
    memcpy(report, "served 1 request", 16);
    return 16;
}

/* End the report at the position given and write it to the standard output. */
__attribute__((noinline)) static void end_report(int at) {
    report[at++] = '\n';
    write(1, report, (size_t)at);
}

int main(void) {
    int accepted = accept_connection();
    if (accepted < 0) return 1;
    __wasi_fd_t connection = (__wasi_fd_t)accepted;

    __wasi_iovec_t buffer = {(uint8_t *)password, sizeof password};
    __wasi_size_t count;
    __wasi_roflags_t flags;
    if (__wasi_sock_recv(connection, &buffer, 1, 0, &count, &flags) != 0) return 1;

    /* Drop one trailing newline. */
    uint32_t length = (uint32_t)count;
    uint32_t last = (unsigned char)password[(length - 1) % CAPACITY];
    length -= (uint32_t)(length > 0) & (uint32_t)(last == '\n');

    uint32_t hash = djb2(password, length);
    uint32_t matched = 0;
    for (unsigned i = 0; i < ENTRIES; i++) matched |= (uint32_t)(hash == weak[i]);

    __wasi_ciovec_t verdict = {(const uint8_t *)verdicts + 5 * matched, 3 + 2 * matched};
    __wasi_size_t sent;
    if (__wasi_sock_send(connection, &verdict, 1, 0, &sent) != 0) return 1;
    (void)__wasi_sock_shutdown(connection, __WASI_SDFLAGS_RD | __WASI_SDFLAGS_WR);
    (void)__wasi_fd_close(connection);

    int at = begin_report();
#if defined(LEAK_CONTROL)
    if (matched) {
        memcpy(report + at, ", weak", 6);
        at += 6;
    }
#elif defined(LEAK_MEMORY)
    report[at++] = ' ';
    at = put_number(at, hash);
#else
    (void)put_number;
#endif
    end_report(at);
    return 0;
}
