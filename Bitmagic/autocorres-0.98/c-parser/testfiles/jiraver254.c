int f(int x)
{
  _Bool b = (x < 10);
  return (b == 0);
}

int g(_Bool b2)
{
  return b2 > 3;
}

_Bool h(_Bool b3)
{
  return !b3;
}

/* pointers convert to bool, being 1 if non-null, 0 otherwise */
_Bool ptrconversion(char *ptr)
{
  return ptr;
}
