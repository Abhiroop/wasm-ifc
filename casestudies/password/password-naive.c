/* The password checker of the paper's overview (section 3): it reads a password from a file
 * in /secrets, compares a hash of it with a dictionary of weak passwords, shows the verdict on
 * its standard output, and appends a record of the run to a log in /log that is shared with
 * the developer. The password must not reach the log.
 *
 * LEAK selects a variant that leaks, one per place the paper says a leak is caught:
 *   (none)          the log records only public information: the number of entries checked
 *   LEAK_CONTROL    the log records whether the password was weak (a flow through control)
 *   LEAK_MEMORY     the log records the hash, through a buffer in memory (a flow through memory)
 */
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

/* djb2 hashes of the dictionary's weak passwords: "123456", "password", "qwerty", "letmein". */
static const uint32_t weak[] = {0x7dd1705au, 0x17f6dc38u, 0x1818ae71u, 0x715ae1b3u};
#define ENTRIES (sizeof weak / sizeof weak[0])

uint32_t hash;    /* the hash of the password: secret */
int matched;      /* whether the password is weak */
static char password[64];
static char record[64];

static uint32_t djb2(const char *text, int length) {
    uint32_t h = 5381;
    for (int i = 0; i < length; i++) h = h * 33 + (unsigned char)text[i];
    return h;
}

static void check(uint32_t entry) {
    if (hash == entry) matched = 1;
}

/* Write a decimal number into the record at position at; return the new position. */
static int put_number(int at, uint32_t n) {
    char digits[10];
    int count = 0;
    do {
        digits[count++] = (char)('0' + n % 10);
        n /= 10;
    } while (n != 0);
    while (count > 0) record[at++] = digits[--count];
    return at;
}

int main(void) {
    int in = open("/secrets/password", O_RDONLY);
    if (in < 0) return 1;
    int length = (int)read(in, password, sizeof password);
    close(in);
    if (length < 0) return 1;
    while (length > 0 && (password[length - 1] == '\n' || password[length - 1] == '\r')) length--;

    hash = djb2(password, length);
    for (unsigned i = 0; i < ENTRIES; i++) check(weak[i]);

    if (matched)
        write(1, "weak\n", 5);
    else
        write(1, "ok\n", 3);

    int log = open("/log/runs.log", O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (log < 0) return 1;
    memcpy(record, "checked ", 8);
    int at = put_number(8, ENTRIES);
#if defined(LEAK_CONTROL)
    memcpy(record + at, matched ? " weak" : " ok", matched ? 5 : 3);
    at += matched ? 5 : 3;
#elif defined(LEAK_MEMORY)
    record[at++] = ' ';
    at = put_number(at, hash);
#endif
    record[at++] = '\n';
    write(log, record, (size_t)at);
    close(log);
    return 0;
}
