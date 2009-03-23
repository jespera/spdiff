int foo(void) {
  int x;
  f(x);
  x = f(x, 42);
  x = h(g(117));
  return x+x;
}
