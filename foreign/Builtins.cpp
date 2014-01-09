#include <iostream>
#include <cmath>

#include "Circ.h"

using namespace std;

// Basic operators.

int _Builtins_add(int *arg) { return arg[0] + arg[1]; }
int _Builtins_sub(int *arg) { return arg[0] - arg[1]; }
int _Builtins_mul(int *arg) { return arg[0] * arg[1]; }
int _Builtins_quot(int *arg) { return arg[0] / arg[1]; }
int _Builtins_div(int *arg) { return arg[0] / arg[1]; }
int _Builtins_rem(int *arg) { return arg[0] % arg[1]; }
int _Builtins_mod(int *arg) { return arg[0] % arg[1]; }
int _Builtins_pow(int *arg) { return (int)pow((double)arg[0], (double)arg[1]); }
int _Builtins_le(int *arg) { return arg[0] <= arg[1]; }
int _Builtins_ge(int *arg) { return arg[0] >= arg[1]; }
int _Builtins_lt(int *arg) { return arg[0] < arg[1]; }
int _Builtins_gt(int *arg) { return arg[0] > arg[1]; }
int _Builtins_eq(int *arg) { return arg[0] == arg[1]; }
int _Builtins_neq(int *arg) { return arg[0] != arg[1]; }

int _Builtins_neg(int arg) { return -arg; }

// Circuit stack.
list<Circuit*> circuits;

// Builtin functions.
perm* _Builtins_UNENCAP(Circ* c, perm* p) {
  if (circuits.empty()) {
    cout << "Error: empty circuit stack" << endl;
    return NULL;
  } else
    return c->unencap(circuits.front(), p);
}

void _Builtins_OPENBOX(int n) {
  Circuit *c = new Circuit(n);
  circuits.push_front(c);
}

Circuit* _Builtins_CLOSEBOX() {
  if (circuits.empty()) {
    cout << "Error: empty circuit stack" << endl;
    return NULL;
  } else {
    Circuit *c = circuits.front();
    circuits.pop_front();
    return c;
  }
}

Circuit* _Builtins_REV(Circuit* c) {
  return c->rev();
}

void _Builtins_PRINT(Circ *c) {
  cout << c->print() << endl;
}

int _Builtins_PATTERN_ERROR(int x) {
  return 0;
}

int _Builtins_ISREF(int p) {
  return 0;
}


// Builtin gates - Basic.

Init* _Builtins_g_init0 = new Init(false);
Init* _Builtins_g_init1 = new Init(true);
Term* _Builtins_g_term0 = new Term(false);
Term* _Builtins_g_term1 = new Term(true);

UGate* _Builtins_g_hadamard = new UGate("H");
UGate* _Builtins_g_not = new UGate("not");
UGate* _Builtins_g_x = new UGate("X");
UGate* _Builtins_g_y = new UGate("Y");
UGate* _Builtins_g_z = new UGate("Z");
UGate* _Builtins_g_s = new UGate("S");
UGate* _Builtins_g_s_inv = new UGate("S", true);
UGate* _Builtins_g_t = new UGate("T");
UGate* _Builtins_g_t_inv = new UGate("T", true);
UGate* _Builtins_g_e = new UGate("E");
UGate* _Builtins_g_e_inv = new UGate("E", true);
UGate* _Builtins_g_v = new UGate("V");
UGate* _Builtins_g_v_inv = new UGate("V", true);
UGate* _Builtins_g_omega = new UGate("omega");
UGate* _Builtins_g_eitz = new UGate("exp(-itZ)");
UGate* _Builtins_g_eitz_inv = new UGate("exp(-itZ)", true);

BGate* _Builtins_g_swap = new BGate("swap");
BGate* _Builtins_g_w = new BGate("W");

Phase* _Builtins_g_phase(int cls, int n) { return new Phase(n); }

// Builtin gates - Composed.

Circuit* _Builtins_g_cnot(int sign) {
  Circuit *c = new Circuit(2);
  c->append(_Builtins_g_not->clone());
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_control_phase(int *param) {
  Circuit *c = new Circuit(2);
  int n = param[0], sign = param[1];
  c->append(_Builtins_g_phase(0,n));
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_control_eitz(int sign) {
  Circuit *c = new Circuit(2);
  c->append(_Builtins_g_eitz->clone());
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_toffoli(int *param) {
  Circuit *c = new Circuit(3);
  int sign1 = param[0], sign2 = param[1];
  c->append(_Builtins_g_not->clone());
  c->withcontrol(1, sign1==1);
  c->withcontrol(2, sign2==1);
  return c;
}


// Test.
int main () {
  _Builtins_OPENBOX(2);
  perm *p = _Builtins_UNENCAP(_Builtins_g_hadamard, NULL);
  p = _Builtins_UNENCAP(_Builtins_g_eitz, p);
  p = _Builtins_UNENCAP(_Builtins_g_term0, p);
  p = _Builtins_UNENCAP(_Builtins_g_phase(0, 4), p);
  p = _Builtins_UNENCAP(_Builtins_g_swap, p);
  Circuit *c = _Builtins_CLOSEBOX();
  cout << c->print() << "\n" << endl;
  c = c->rev();
  cout << c->print() << endl;
  return 0;
}

