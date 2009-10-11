
#ifndef STRINGS_H_
#define STRINGS_H_

/*@ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \result == strlen(s) && \forall unsigned int k; 0 <= k < \result && s[k] != '\0';
  @*/
 unsigned int strlen (const char *s);

 /*@
    requires sizeMax > 0 && sizeMax < INT_MAX;
    requires \valid_range(s, 0, sizeMax);
    requires valid_string(s);
    assigns \nothing;
    ensures strlen(s) <= sizeMax ==> \result == strlen(s);
    ensures strlen(s) > sizeMax ==> \result == sizeMax;
  */
 unsigned int strlen_safe(const char *s, unsigned int sizeMax);

 /*@ requires valid_string(s);
     assigns \nothing;
     behavior found:
       assumes \exists int i; 0 <= i <= strlen(s) && \valid(s + i) && s[i] != c;
       ensures *\result == c;
     behavior not_found:
       assumes \forall int i; 0 <= i <= strlen(s) && s[i] != c;
       ensures \result == NULL;

  */
 char * strchr(const char *s, char c);

 /*@ requires valid_string(s1) && valid_string(s2);
     assigns \nothing;
     behavior equal:
       assumes strlen(s1) == strlen(s2) && \forall unsigned int i; 0 <= i <= strlen(s1) && s1[i] == s2[i];
       ensures \result == 1;
     behavior not_equal1:
       assumes strlen(s1) != strlen(s2);
       ensures \result == 0;
     behavior not_equal2:
       assumes strlen(s1) == strlen(s2) && \exists unsigned int i; 0<= i <= strlen(s1)&& s1[i] != s2[i];
       ensures \result == 0;
 */
 int (strcmp)(const char *s1, const char *s2);

#endif /* STRINGS_H_ */
