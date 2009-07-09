int binary_search(int* t, int n, int v) {
int l = 0, u = n-1, p = -1;
while (l <= u) {
int m = (l + u) / 2;
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

