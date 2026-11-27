/* Force-included when cross-compiling Z3 4.12.2 with a new glibc.
   _GNU_SOURCE redirects strtol to __isoc23_strtol (GLIBC_2.38). Turning the
   C2x redirects off keeps the shared library on the older symbol versions.
   features.h is include-guarded, so this has to run before any libc header. */
#include <features.h>
#undef __GLIBC_USE_ISOC2X
#define __GLIBC_USE_ISOC2X 0
#undef __GLIBC_USE_C2X_STRTOL
#define __GLIBC_USE_C2X_STRTOL 0
