int foo(void) {
  int x;
  f(x);
  x = f(x, 42);
  x = h(g(117));
  return x+x;
}

int bar(int y) {
  int a;
  a = f(a,42);
  a = f(a)+g(y,y);
  return a+a;
}

int smoz(int y) {
  int z;
  z = f(z, 42);
	somecall();
  return z+z;
}
