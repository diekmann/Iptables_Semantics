typedef struct {
  int x;
  char y;
} s_t;

s_t *s;

int f(void)
{
  int * const p = &(s->x);
  return *p;
}
