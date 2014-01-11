#include <iostream>
#include <cmath>

#include "Builtins.h"

using namespace std;

inline string inttostr(size_t i) {
  stringstream ss;
  ss << i;
  return ss.str();
}

// Permutations.

int app_perm(perm* p, size_t x) {
  if (p == NULL)
    return x;
  else if (p->_q == x)
    return p->_assoc;
  else
    return app_perm(p->_rem, x);
}

perm* append(size_t q, size_t assoc, perm *p) {
  perm *pp = (perm*)malloc(sizeof(perm));
  pp->_q = q;
  pp->_assoc = assoc;
  pp->_rem = p;
  return pp;
}

perm* remove(size_t x, perm* p) {
  if (p == NULL)
    return NULL;
  else if (p->_q == x) {
    free(p);
    return NULL;
  } else {
    perm* r = remove(x, p->_rem);
    p->_rem = r;
    return p;
  }
}

// Parent class.

void Circ::withcontrol(size_t w, bool s) {
  ctrl c;
  c._wire = w;
  c._sign = s;
  _controls.push_front(c);
}

string Circ::controls() {
  if (_controls.empty())
    return "";
  else {
    list<ctrl>::iterator it = _controls.begin();
    stringstream ctrls;
    ctrls << " with controls=[" << (it->_sign? "+": "-") << it->_wire;
    it++;
    for (; it!=_controls.end(); it++)
      ctrls << ", " << (it->_sign? "+": "-") << it->_wire;
    ctrls << "]";
    return ctrls.str();
  }
}

void Circ::app_perm_to_controls(perm *p) {
  list<ctrl>::iterator it=_controls.begin();
  for (; it!=_controls.end(); it++)
    it->_wire = app_perm(p, it->_wire);
}


// Definition of the basic gates.

string Init::print() {
  if (_val)
    return "QInit1(" + inttostr(_output) + ")" + controls();
  else
    return "QInit0(" + inttostr(_output) + ")" + controls();
}

perm* Init::unencap(Circuit* c, perm* p) {
  size_t q = c->init();
  Init* cpy = clone();
  cpy->app_perm_to_controls(p);
  perm *pp = append(_output, q, p);
  cpy->_output = q;
  c->append(cpy);
  return pp;
}

Circ* Init::rev() {
  Term *rev = new Term(_val, _output);
  delete this;
  return rev;
}

string Term::print() {
  if (_val)
    return "QTerm1(" + inttostr(_input) + ")" + controls();
  else
    return "QTerm0(" + inttostr(_input) + ")" + controls();
}

perm* Term::unencap(Circuit* c, perm* p) {
  size_t q = app_perm(p, _input);
  Term* cpy = clone();
  cpy->app_perm_to_controls(p);
  perm *pp = remove(_input, p);
  cpy->_input = q;
  c->term(q);
  c->append(cpy);
  return pp;
}

Circ* Term::rev() {
  Init *rev = new Init(_val, _input);
  delete this;
  return rev;
}

string UGate::print() {
  if (_inv)
    return "QGate[" + _name + "]*(" + inttostr(_wire) + ")" + controls();
  else
    return "QGate[" + _name + "](" + inttostr(_wire) + ")" + controls();
}

perm* UGate::unencap(Circuit* c, perm* p) {
  UGate *cpy = clone();
  cpy->app_perm_to_controls(p);
  cpy->_wire = app_perm(p, _wire);
  c->append(cpy);
  return p;
}

string BGate::print() {
  if (_inv)
    return "QGate[" + _name + "]*(" + inttostr(_wire0) + ", " + inttostr(_wire1) + ")" + controls();
  else
    return "QGate[" + _name + "](" + inttostr(_wire0) + ", " + inttostr(_wire1) + ")" + controls();
}

perm* BGate::unencap(Circuit *c, perm *p) {
  BGate *cpy = clone();
  cpy->app_perm_to_controls(p);
  cpy->_wire0 = app_perm(p, _wire0);
  cpy->_wire1 = app_perm(p, _wire1);
  c->append(cpy);
  return p;
}

string Phase::print() {
  return "QRot[R(2pi/" + inttostr(2*_val) + ")](" + inttostr(_wire) + ")" + controls();
}

perm* Phase::unencap(Circuit *c, perm *p) {
  Phase *cpy = clone();
  cpy->_wire = app_perm(p, _wire);
  c->append(cpy);
  return p;
}

// Definition of a circuit.

// Circuit initialized with n wires.
Circuit::Circuit(size_t n): _qid(n) {
  for (size_t i=0; i<n; i++)
    _input.push_back(i);
  _output = _input;
}

Circuit::Circuit(const Circuit& cpy): Circ(cpy), _input(cpy._input), _output(cpy._output), _qid(cpy._qid) {
  for (list<Circ*>::iterator it=_gates.begin(); it!=_gates.end(); it++) {
    Circ* cp = (*it)->clone();
    _gates.push_back(cp);
  }
}

Circuit::~Circuit() {
  for (list<Circ*>::iterator it=_gates.begin(); it!=_gates.end(); it++)
    delete (*it);
}

string Circuit::print() {
  stringstream doc;
  // Inputs.
  doc << "Inputs: ";
  if (_input.empty())
    doc << "none";
  else {
    list<size_t>::iterator it=_input.begin();
    doc << *it << ":Qbit";
    it++;
    for (; it!=_input.end(); it++)
      doc << ", " << *it << ":Qbit";
  }
  doc << endl;
  // Gates.
  for (list<Circ*>::iterator it=_gates.begin(); it!=_gates.end(); it++)
    doc << (*it)->print() << endl;
  // Outputs.
  doc << "Outputs: ";
  if (_output.empty())
    doc << "none";
  else {
    list<size_t>::iterator it=_output.begin();
    doc << *it << ":Qbit";
    it++;
    for (; it!=_output.end(); it++)
      doc << ", " << *it << ":Qbit";
  }
  // Return.
  return doc.str();
}

size_t Circuit::init() {
  size_t q = _qid;
  _qid++;
  _output.push_front(q);
  return q;
}

void Circuit::term(size_t q) {
  _output.remove(q);
}

void Circuit::append(Circ* g) {
  _gates.push_back(g);
}

void Circuit::withcontrol(size_t w, bool s) {
  for (list<Circ*>::iterator it=_gates.begin(); it!=_gates.end(); it++)
    (*it)->withcontrol(w,s);
}

perm* Circuit::unencap(Circuit* c, perm* p) {
  perm* pp = p;
  for(list<Circ*>::iterator it=_gates.begin(); it != _gates.end(); it++) {
    pp = (*it)->unencap(c, pp);
  }
  return pp;
}

Circuit* Circuit::rev() {
  list<Circ*> reversed;
  for (list<Circ*>::iterator it=_gates.begin(); it!=_gates.end(); it++)
    reversed.push_front((*it)->rev());
  _gates = reversed;
  return this;
}

// Circuit stack.
list<Circuit*> circuits = list<Circuit*>(1,new Circuit(0));

extern "C" {

// Basic operators.

size_t _Builtins_add(size_t cls, size_t *arg) { return arg[0] + arg[1]; }
size_t _Builtins_sub(size_t cls, size_t *arg) { return arg[0] - arg[1]; }
size_t _Builtins_mul(size_t cls, size_t *arg) { return arg[0] * arg[1]; }
size_t _Builtins_quot(size_t cls, size_t *arg) { return arg[0] / arg[1]; }
size_t _Builtins_div(size_t cls, size_t *arg) { return arg[0] / arg[1]; }
size_t _Builtins_rem(size_t cls, size_t *arg) { return arg[0] % arg[1]; }
size_t _Builtins_mod(size_t cls, size_t *arg) { return arg[0] % arg[1]; }
size_t _Builtins_pow(size_t cls, size_t *arg) { return (size_t)pow((double)arg[0], (double)arg[1]); }
size_t _Builtins_le(size_t cls, size_t *arg) { return arg[0] <= arg[1]; }
size_t _Builtins_ge(size_t cls, size_t *arg) { return arg[0] >= arg[1]; }
size_t _Builtins_lt(size_t cls, size_t *arg) { return arg[0] < arg[1]; }
size_t _Builtins_gt(size_t cls, size_t *arg) { return arg[0] > arg[1]; }
size_t _Builtins_eq(size_t cls, size_t *arg) { return arg[0] == arg[1]; }
size_t _Builtins_neq(size_t cls, size_t *arg) { return arg[0] != arg[1]; }

size_t _Builtins_neg(size_t cls, size_t arg) { return -arg; }

// Printing.

size_t _Builtins_print_int(size_t cls, size_t arg) { cout << arg; return 0; }
size_t _Builtins_print_newline(size_t cls, size_t arg) { cout << endl; return 0; }

// Builtin functions.
perm* _Builtins_UNENCAP(size_t cls, size_t **arg) {
  if (circuits.empty()) {
    cout << "Error: empty circuit stack" << endl;
    return NULL;
  } else {
    Circ *c = (Circ*)arg[0];
    perm *p = (perm*)arg[1];
    return c->unencap(circuits.front(), p);
  }
}

void _Builtins_OPENBOX(size_t cls, size_t n) {
  Circuit *c = new Circuit(n);
  circuits.push_front(c);
}

Circuit* _Builtins_CLOSEBOX(size_t cls, size_t arg) {
  if (circuits.empty()) {
    cout << "Error: empty circuit stack" << endl;
    return NULL;
  } else {
    Circuit *c = circuits.front();
    circuits.pop_front();
    return c;
  }
}

Circuit* _Builtins_REV(size_t cls, Circuit* c) {
  return c->rev();
}

size_t _Builtins_PRINT(size_t cls, Circ *c) {
  cout << c->print() << endl;
  return 0;
}

size_t _Builtins_ERROR(size_t cls, size_t x) {
  return 0;
}

size_t _Builtins_ISREF(size_t cls, size_t p) {
  return 0;
}

size_t _Builtins_APPBIND(size_t cls, size_t **arg) {
  perm *p = (perm*)arg[0];
  size_t q = (size_t)arg[1];
  return app_perm(p,q);
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

Phase* _Builtins_g_phase(size_t cls, size_t n) { return new Phase(n); }

// Builtin gates - Composed.

Circuit* _Builtins_g_cnot(size_t cls, size_t sign) {
  Circuit *c = new Circuit(2);
  c->append(_Builtins_g_not->clone());
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_control_phase(size_t cls, size_t *param) {
  Circuit *c = new Circuit(2);
  size_t n = param[0], sign = param[1];
  c->append(_Builtins_g_phase(0,n));
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_control_eitz(size_t cls, size_t sign) {
  Circuit *c = new Circuit(2);
  c->append(_Builtins_g_eitz->clone());
  c->withcontrol(1, sign==1);
  return c;
}

Circuit* _Builtins_g_toffoli(size_t cls, size_t *param) {
  Circuit *c = new Circuit(3);
  size_t sign1 = param[0], sign2 = param[1];
  c->append(_Builtins_g_not->clone());
  c->withcontrol(1, sign1==1);
  c->withcontrol(2, sign2==1);
  return c;
}

// Init function (necessary to link with quipper binaries).

size_t InitBuiltins() {
  return 0;
}

}

/* Test.
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
*/

