unsigned char uc;
signed char sc;
unsigned int ui;
int si;
unsigned long ul;
long sl;

signed char *retptr(void)
{
  return &sc;
}

void doit(void)
{
  uc++;
  sc++;
  ui++;
  si++;
  ul++;
  sl++;
  (*retptr())++;
  sl--;
  uc--;
}

