int foo(void) {
  int x;
  f(x);
  x = f(x);
  x = g(117);
  return x;
}
