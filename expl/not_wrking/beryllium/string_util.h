

/*@ logic integer strlen(char *s) reads s[0..];
  @
  @ predicate valid_string(char *s) =
  @   0 <= strlen(s) && \valid_range(s,0,strlen(s));
  @
  @ axiom strlen_before_null:
  @   \forall char* s; \forall int i; 0 <= i < strlen(s) ==> s[i] != '\0';
  @
  @ axiom strlen_at_null:
  @   \forall char* s; s[strlen(s)] == '\0';
  @
  @ axiom strlen_not_zero:
  @   \forall char* s; \forall int i;
  @      0 <= i <= strlen(s) && s[i] != '\0' ==> i < strlen(s);
  @
  @ axiom strlen_zero:
  @   \forall char* s; \forall int i;
  @      0 <= i <= strlen(s) && s[i] == '\0' ==> i == strlen(s);
  @
  @ axiom strlen_sup:
  @   \forall char* s; \forall int i;
  @      0 <= i && s[i] == '\0' ==> 0 <= strlen(s) <= i;
  @
  @ axiom strlen_shift:
  @   \forall char* s; \forall int i;
  @      0 <= i <= strlen(s) ==> strlen(s+i) == strlen(s)-i;
  @
  @ axiom strlen_create:
  @   \forall char* s; \forall int i;
  @      0 <= i && s[i] == '\0' ==> 0 <= strlen(s) <= i;
  @
  @ axiom strlen_create_shift:
  @   \forall char* s; \forall int i; \forall int k;
  @      0 <= k <= i && s[i] == '\0' ==> 0 <= strlen(s+k) <= i - k;
  @*/
