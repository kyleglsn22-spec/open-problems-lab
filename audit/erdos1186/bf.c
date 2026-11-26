/* Independent brute-force m4(Z_p,c): counts all (a,d) in Z_p^2 (d=0 included).
   usage: bf p b K table01string   (c(x) = table[(x mod b)*K + floor(K x / p)]) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  long p = atol(argv[1]); int b = atoi(argv[2]), K = atoi(argv[3]); const char *T = argv[4];
  if ((long)strlen(T) != (long)b * K) { fprintf(stderr, "bad table\n"); return 1; }
  unsigned char *c = malloc(4 * p);
  for (long x = 0; x < p; x++) {
    long j = (long)((__int128)K * x / p);
    c[x] = T[(x % b) * K + j] - '0';
  }
  for (long x = p; x < 4 * p; x++) c[x] = c[x - p];
  long long cnt = 0;
  for (long d = 0; d < p; d++) {
    const unsigned char *c1 = c + d, *c2 = c + 2 * d, *c3 = c + 3 * d;
    long long s = 0;
    for (long a = 0; a < p; a++) {
      unsigned char v = c[a];
      s += (v == c1[a]) & (v == c2[a]) & (v == c3[a]);
    }
    cnt += s;
  }
  printf("%lld %.12f\n", cnt, (double)cnt / ((double)p * p));
  return 0;
}
