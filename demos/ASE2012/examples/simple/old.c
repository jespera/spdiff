int foo(void) {
  int x;
  f(x);
  x = f(x);
  x = g(117);
  return x;
}

int bar(int y) {
  int a;
  a = f(a);
  a = f(a)+g(y);
  return a;
}

int smoz(int y) {
  int z;
  z = f(z);
	somecall();
  return z;
}
