

struct node {
    struct node *next;
    int v;
};

int f(struct node *n)
{
    return n->next->next->next->v;
}

unsigned g (unsigned **ptr)
{
  return **ptr;
}
