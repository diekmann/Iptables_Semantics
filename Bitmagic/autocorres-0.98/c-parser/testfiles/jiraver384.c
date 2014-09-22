int global;
void foo(void)
{
  void bar(void);
  bar();
}

/** FNSPEC
      some_external_spec: "\<Gamma> \<turnstile> {} Call some_external_'proc {}"
*/
int some_external(void);
