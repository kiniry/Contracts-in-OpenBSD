/*@ lemma mean : \forall int x, y; x <= y ==> x <= (x+y)/2 <= y; */
/*@ requires
  @   n >= 0 && \valid_range(t,0,n-1) &&
  @   \forall int k1, int k2; 0 <= k1 <= k2 <= n-1 ==> t[k1] <= t[k2];
  @ behavior success:
  @   assumes \exists int k; 0 <= k <= n-1 && t[k] == v;
  @   ensures 0 <= \result <= n-1;
  @ behavior failure:
  @   assumes \forall int k; 0 <= k <= n-1 ==> t[k] < v || t[k] > v;
  @   ensures \result == -1;
@*/
int binary_search5(int* t, int n, int v) {
  int l = 0, u = n-1, p = -1;
  /*@ loop invariant
    @ 0 <= l && u <= n-1 && -1 <= p <= n-1
    @ && (p == -1 ==> \forall int k; 0 <= k < n ==> t[k] == v ==> l <= k <= u)
    @ && (p >= 0 ==> t[p]==v);
    @*/
  while (l <= u) {
    int m = l + (u - l) / 2;
    if (t[m] < v)
      l = m + 1;
    else if (t[m] > v)
      u = m - 1;
    else {
      p = m; break;
    }
  }
  return p;
}

