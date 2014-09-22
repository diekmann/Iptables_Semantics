int x /** OWNED_BY foo */, y /** OWNED_BY bar */, z;

/* reads/writes x, writes z */
int f(int i)
{
  x += i;
  z++;
  return x;
}

/* reads x & z, writes y */
int g(int i)
{
  y++;
  return x + i + z;
}
