
#include "..\string_util.h"

/*@
   requires tosize > 0 && \valid_range(to, 0, toSize-1) && valid_string(from);
   assigns to[0..toSize -1];
   ensures toSize <= strlen(from) ==> strlen(to) == toSize && \forall unsigned int k; 0 <= k < toSize && to[k] == from[k];
   ensures toSize > strlen(from) ==> strlen(to) == strlen(from) && \forall unsigned int k; 0 <= k <= strlen(from) && to[k] == from[k];
   ensures \result == to;
 */
char *strcpy (char *to, unsigned int toSize, const char *from);

/*@
  requires \valid_range(to, 0, toSize-1) && valid_string(from);
  requires toSize > 0 && (toSize >= strlen(to) + strlen(from));
  assigns to[0..toSize-1];
  ensures strlen(to) == \old(strlen(to)) + strlen(from);
  ensures \forall unsigned int k; 0 <= k < \old(strlen(to)) && to[k] == \at(to[k], Old);
  ensures \forall unsigned int k; \old(strlen(to)) <= k < strlen(to) && to[k] == from[k-\old(strlen(to))];
  ensures \result == to;
 */
char *strncat (char *to, unsigned int toSize, const char *from);
