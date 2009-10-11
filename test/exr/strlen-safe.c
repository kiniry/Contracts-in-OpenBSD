// Safe version of string length that takes a max length parameter and requires the string to be null-terminated.

#pragma JessieIntegerModel(exact)

#include "strings.h"
/*@
   requires sizeMax > 0 && sizeMax < INT_MAX;
   requires \valid_range(s, 0, sizeMax);
   requires valid_string(s);
   assigns \nothing;
   ensures strlen(s) <= sizeMax ==> \result == strlen(s);
   ensures strlen(s) > sizeMax ==> \result == sizeMax;
 */
 unsigned int strlen_safe(const char *s, unsigned int sizeMax)
 {
	 unsigned int i = 0;

     //@ loop invariant 0 <= i <= sizeMax && \valid(s + i) && i <= strlen(s);
     while (i < sizeMax && s[i] != '\0')
     	i++;
     return i;
 }



