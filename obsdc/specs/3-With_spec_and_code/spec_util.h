/*
 * spec_util.h
 *
 *  Created on: 28-Dec-2009
 *      Author: mstr-kul
 */

#ifndef SPEC_UTIL_H_
#define SPEC_UTIL_H_

#include "limits.h"


/*@ axiomatic MemCmp {
  @
  @ logic integer memcmp{L}(char *s1, char *s2, integer n);
  @ // reads s1[0..n - 1], s2[0..n - 1];
  @
  @ axiom memcmp_range{L}:
  @   \forall char *s1, *s2; \forall integer n;
  @      INT_MIN <= memcmp(s1,s2,n) <= INT_MAX;
  @
  @ axiom memcmp_zero{L}:
  @   \forall char *s1, *s2; \forall integer n;
  @      memcmp(s1,s2,n) == 0
  @      <==> \forall integer i; 0 <= i < n ==> s1[i] == s2[i];
  @
  @ }
  @*/

/*@ axiomatic StrLen {
  @ logic integer strlen{L}(char *s);
  @ // reads s[0..];
  @
  @ axiom strlen_pos_or_null{L}:
  @   \forall char* s; \forall integer i;
  @      (0 <= i <= INT_MAX
  @       && (\forall integer j; 0 <= j < i ==> s[j] != '\0')
  @       && s[i] == 0) ==> strlen(s) == i;
  @
  @ axiom strlen_neg{L}:
  @   \forall char* s;
  @      (\forall integer i; 0 <= i <= INT_MAX ==> s[i] != '\0')
  @      ==> strlen(s) < 0;
  @
  @ axiom strlen_range{L}:
  @   \forall char* s; strlen(s) <= INT_MAX;
  @
  @ axiom strlen_before_null{L}:
  @   \forall char* s; \forall integer i; 0 <= i < strlen(s) ==> s[i] != '\0';
  @
  @ axiom strlen_at_null{L}:
  @   \forall char* s; 0 <= strlen(s) ==> s[strlen(s)] == '\0';
  @
  @ axiom strlen_not_zero{L}:
  @   \forall char* s; \forall integer i;
  @      0 <= i <= strlen(s) && s[i] != '\0' ==> i < strlen(s);
  @
  @ axiom strlen_zero{L}:
  @   \forall char* s; \forall integer i;
  @      0 <= i <= strlen(s) && s[i] == '\0' ==> i == strlen(s);
  @
  @ axiom strlen_sup{L}:
  @   \forall char* s; \forall integer i;
  @      0 <= i && s[i] == '\0' ==> 0 <= strlen(s) <= i;
  @
  @ axiom strlen_shift{L}:
  @   \forall char* s; \forall integer i;
  @      0 <= i <= strlen(s) ==> strlen(s + i) == strlen(s) - i;
  @
  @ axiom strlen_create{L}:
  @   \forall char* s; \forall integer i;
  @      0 <= i <= INT_MAX && s[i] == '\0' ==> 0 <= strlen(s) <= i;
  @
  @ axiom strlen_create_shift{L}:
  @   \forall char* s; \forall integer i; \forall integer k;
  @      0 <= k <= i <= INT_MAX && s[i] == '\0' ==> 0 <= strlen(s+k) <= i - k;
  @
  @ axiom memcmp_strlen_left{L}:
  @   \forall char *s1, *s2; \forall integer n;
  @      memcmp(s1,s2,n) == 0 && strlen(s1) < n ==> strlen(s1) == strlen(s2);
  @
  @ axiom memcmp_strlen_right{L}:
  @   \forall char *s1, *s2; \forall integer n;
  @      memcmp(s1,s2,n) == 0 && strlen(s2) < n ==> strlen(s1) == strlen(s2);
  @
  @ axiom memcmp_strlen_shift_left{L}:
  @   \forall char *s1, *s2; \forall integer k, n;
  @      memcmp(s1,s2 + k,n) == 0 && 0 <= k && strlen(s1) < n ==>
  @        0 <= strlen(s2) <= k + strlen(s1);
  @
  @ axiom memcmp_strlen_shift_right{L}:
  @   \forall char *s1, *s2; \forall integer k, n;
  @      memcmp(s1 + k,s2,n) == 0 && 0 <= k && strlen(s2) < n ==>
  @        0 <= strlen(s1) <= k + strlen(s2);
  @
  @ }
  @*/

/*@ logic integer minimum(integer i, integer j) = i < j ? i : j;
  @ logic integer maximum(integer i, integer j) = i < j ? j : i;
  @*/

/*@ predicate valid_string{L}(char *s) =
  @   0 <= strlen(s) && \valid_range(s,0,strlen(s));
  @
  @*/


#endif /* SPEC_UTIL_H_ */
