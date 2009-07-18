// Safe version of string length that takes a max length parameter and requires the string to be null-terminated.

/*@
   requires sizeMax > 0 && sizeMax < INT_MAX;
   requires \valid_range(s, 0, sizeMax-1);
   requires \exists int k;0 <= k < sizeMax && s[k] == '\0'; // null_terminated.
   assigns \nothing;
   ensures \result <= sizeMax;
 */
 unsigned int strlen(const char *s, unsigned int sizeMax)
 {
     unsigned int i = 0;
     //@ loop invariant 0 <= i <= sizeMax;
     while (i < sizeMax && s[i] != '\0')
     	i++;
     return i;
 }



