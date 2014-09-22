int good(int *p) {
  return p && *p == 0;
}

struct ure {
  int n;
};

int bad(struct ure *sp) {
  return sp && sp->n == 0;
}
