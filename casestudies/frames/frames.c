/* A helper with a stack frame of its own, called only if a secret says so. A C function that
 * needs a frame and calls another function lowers the shadow-stack pointer (the WebAssembly
 * global 0) on entry and raises it on exit, so calling one under a secret pc writes a public
 * global there. The rules
 * reject that write unless the policy declares the global preserved; the machine then checks
 * that the pointer is back where it was when the secret part of the code ends.
 *
 * The program reads a key from /secrets, folds it with the helper if its first byte is odd,
 * keeps the result in memory, and reports on its standard output that it is done, which says
 * nothing about the key.
 */
#include <fcntl.h>
#include <unistd.h>

static char key[16];
static unsigned digest;

__attribute__((noinline)) static unsigned step(unsigned h, const volatile unsigned char *byte) {
    return h * 33 + *byte;
}

/* Not inlined, with an array, and not a leaf: a leaf function may use the stack below the
 * pointer without moving it, and only a function that calls another has to lower it. */
__attribute__((noinline)) static unsigned fold(const char *text) {
    volatile unsigned char block[32];
    for (int i = 0; i < 32; i++) block[i] = (unsigned char)(text[i % 16] + i);
    unsigned h = 5381;
    for (int i = 0; i < 32; i++) h = step(h, &block[i]);
    return h;
}

int main(void) {
    int in = open("/secrets/key", O_RDONLY);
    if (in < 0) return 1;
    read(in, key, sizeof key);
    close(in);

    if (key[0] & 1) digest = fold(key); /* a call under a secret pc */

    write(1, "done\n", 5);
    return 0;
}
