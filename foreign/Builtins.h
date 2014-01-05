#include <cstdlib>
#include <sstream>

#include <list>
#include <string>

using namespace std;

class Circuit;

// Permutations.
struct perm {
  int _q;
  int _assoc;
  perm* _rem;
};

int app_perm(perm*, int);        // Apply a permutation to a point.
perm* append(int, int, perm*);   // Add a new binding to the permutation.
perm* remove(int, perm*);        // Remove a binding from the permutation.

// Controls.
typedef struct {
  int _wire;
  bool _sign;
} ctrl;


// Definition of a basic diagram with input and output wires.
class Circ {
  public:
    Circ() {};
    Circ(Circ& cpy): _controls(cpy._controls) {};
    // Unencap the current gate/circuit on the given circuit,
    // not the converse.
    virtual perm* unencap(Circuit*, perm*) =0;
    virtual string print() =0;
    virtual Circ* clone() { return this; };
    virtual void withcontrol(int, bool);
    string controls();
  protected:
    list<ctrl> _controls;
    void app_perm_to_controls(perm*);
};

// Implementation of some gates.
class Init: public Circ {
  public:
    Init(bool b): _val(b), _output(0) {};
    Init(Init& cpy): Circ(cpy), _val(cpy._val), _output(cpy._output) {};
    ~Init() {};
    perm* unencap(Circuit*, perm*);
    string print();
    Init* clone() { return (new Init(*this)); };
  private:
    bool _val;
    int _output;
};

class Term: public Circ {
  public:
    Term(bool b): _val(b), _input(0) {};
    Term(Term& cpy): Circ(cpy), _val(cpy._val), _input(cpy._input) {};
    ~Term() {};
    perm* unencap(Circuit*, perm*);
    string print();
    Term* clone() { return (new Term(*this)); };
  private:
    bool _val;
    int _input;
};

class UGate: public Circ {
  public:
    UGate(string name, bool inv=false): _name(name), _wire(0), _inv(inv) {};
    UGate(UGate& cpy): Circ(cpy), _name(cpy._name), _wire(cpy._wire), _inv(cpy._inv) {};
    ~UGate() {};
    perm* unencap(Circuit*, perm*);
    string print();
    UGate* clone() { return (new UGate(*this)); };
  private:
    string _name;
    int _wire;
    bool _inv;
};

class BGate: public Circ {
  public:
    BGate(string name, bool inv=false): _name(name), _wire0(0), _wire1(1), _inv(inv) {};
    BGate(BGate& cpy): Circ(cpy), _name(cpy._name), _wire0(cpy._wire0),
      _wire1(cpy._wire1), _inv(cpy._inv) {};
    ~BGate() {};
    perm* unencap(Circuit*, perm*);
    string symbol() { return ""; };
    string print();
    BGate* clone() { return (new BGate(*this)); };
  private:
    string _name;
    int _wire0;
    int _wire1;
    bool _inv;
};

class Phase: public Circ {
  public:
    Phase(int n): _val(n), _wire(0) {};
    Phase(Phase& cpy): Circ(cpy), _val(cpy._val), _wire(cpy._wire) {};
    ~Phase() {};
    perm* unencap(Circuit*, perm*);
    string print();
    Phase* clone() { return (new Phase(*this)); };
  private:
    int _wire;
    int _val;
};

// Implementation of a circuit as a list of gates (or circuits).
class Circuit: public Circ {
  public:
    Circuit(): _qid(0) {};
    Circuit(int);
    Circuit(Circuit&);
    ~Circuit();
    perm* unencap(Circuit*, perm*);
    void withcontrol(int,bool);
    void append(Circ*);
    int init();          // Create a new qubit.
    void term(int);      // Delete a qubit.
    string print();
    Circuit* clone() { return (new Circuit(*this)); };
  private:
    list<int> _input;
    list<int> _output;
    list<Circ*> _gates;
    int _qid;
};

