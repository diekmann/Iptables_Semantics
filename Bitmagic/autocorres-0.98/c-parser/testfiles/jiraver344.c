struct __s {
  int fld;
  int __fld;
};

typedef struct __s __t;

int _f(int i)
{
  return i + 1;
}

int g(struct __s *sptr, __t *__x)
{
  return sptr->__fld + __x->__fld;
}
