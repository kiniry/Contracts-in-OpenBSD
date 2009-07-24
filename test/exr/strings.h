
#ifndef STRINGS_H_
#define STRINGS_H_

#include "string_util.h"


 unsigned int strlen (const char *s);
 unsigned int strlen_safe(const char *s, unsigned int sizeMax);
 char * strchr(const char *s, char c);
 int (strcmp)(const char *s1, const char *s2);

#endif /* STRINGS_H_ */
