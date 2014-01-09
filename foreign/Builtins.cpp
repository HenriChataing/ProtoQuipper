#include <iostream>

#include "Circ.h"

using namespace std;


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


// Builtin gates.
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

// The closure as argument...(fake).
Phase* _Builtins_g_phase(int cls, int n) {
  return new Phase(n);
}
inline Circuit* create_cnot() {
  Circuit* c = new Circuit(2);
  c->append(_Builtins_g_not->clone());
  c->withcontrol(1,true);
  return c;
}
Circuit* _Builtins_g_cnot = create_cnot();


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

