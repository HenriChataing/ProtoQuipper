#include <cstdlib>
#include <sstream>

#include <list>
#include <string>

class Circuit;


// Permutations.
// The definition is given in the module Compiler.Circ
struct perm {
  intptr_t _tag;
  intptr_t _q;
  intptr_t _assoc;
  perm* _rem;
};

int app_perm(perm*, int);        // Apply a permutation to a point.
perm* append(int, int, perm*);   // Add a new binding to the permutation.
perm* remove(int, perm*);        // Remove a binding from the permutation.
void print(perm*);

// Controls.
typedef struct ctrl {
  intptr_t _wire;
  bool _sign;
} ctrl;


// Definition of a basic diagram with input and output wires.
class Circ {
  public:
    Circ() {};
    Circ(const Circ& cpy): _controls(cpy._controls) {};
    virtual ~Circ() {};
    // Unencap the current gate/circuit on the given circuit,
    // not the converse.
    virtual perm* unencap(Circuit*, perm*) =0;
    virtual std::string print() =0;
    virtual Circ* clone() =0;
    virtual Circ* rev() =0;
    virtual void withcontrol(intptr_t, bool);
    std::string controls();
  protected:
    std::list<ctrl> _controls;
    void app_perm_to_controls(perm*);
};



// Implementation of some gates.
class Init: public Circ {
  public:
    Init(bool b, intptr_t w=0): _val(b), _output(w) {};
    Init(const Init& cpy): Circ(cpy), _val(cpy._val), _output(cpy._output) {};
    ~Init() {};
    perm* unencap(Circuit*, perm*);
    std::string print();
    Init* clone() { return (new Init(*this)); };
    Circ* rev();
  private:
    bool _val;
    intptr_t _output;
};

class Term: public Circ {
  public:
    Term(bool b, intptr_t w=0): _val(b), _input(w) {};
    Term(const Term& cpy): Circ(cpy), _val(cpy._val), _input(cpy._input) {};
    ~Term() {};
    perm* unencap(Circuit*, perm*);
    std::string print();
    Term* clone() { return (new Term(*this)); };
    Circ* rev();
  private:
    bool _val;
    intptr_t _input;
};

class UGate: public Circ {
  public:
    UGate(std::string name, bool inv=false): _name(name), _wire(0), _inv(inv) {};
    UGate(const UGate& cpy): Circ(cpy), _name(cpy._name), _wire(cpy._wire), _inv(cpy._inv) {};
    ~UGate() {};
    perm* unencap(Circuit*, perm*);
    std::string print();
    UGate* clone() { return (new UGate(*this)); };
    UGate* rev() { _inv=not _inv; return this; };
  private:
    std::string _name;
    intptr_t _wire;
    bool _inv;
};

class BGate: public Circ {
  public:
    BGate(std::string name, bool inv=false): _name(name), _wire0(0), _wire1(1), _inv(inv) {};
    BGate(const BGate& cpy): Circ(cpy), _name(cpy._name), _wire0(cpy._wire0),
      _wire1(cpy._wire1), _inv(cpy._inv) {};
    ~BGate() {};
    perm* unencap(Circuit*, perm*);
    std::string symbol() { return ""; };
    std::string print();
    BGate* clone() { return (new BGate(*this)); };
    BGate* rev() { _inv=not _inv; return this; };
  private:
    std::string _name;
    intptr_t _wire0;
    intptr_t _wire1;
    bool _inv;
};

class Phase: public Circ {
  public:
    Phase(int n): _val(n), _wire(0) {};
    Phase(const Phase& cpy): Circ(cpy), _val(cpy._val), _wire(cpy._wire) {};
    ~Phase() {};
    perm* unencap(Circuit*, perm*);
    std::string print();
    Phase* clone() { return (new Phase(*this)); };
    Phase* rev() { return this; }
  private:
    intptr_t _wire;
    intptr_t _val;
};

// Implementation of a circuit as a std::list of gates (or circuits).
class Circuit: public Circ {
  public:
    Circuit(): _qid(0) {};
    Circuit(intptr_t);
    Circuit(const Circuit&);
    ~Circuit();
    perm* unencap(Circuit*, perm*);
    void withcontrol(intptr_t,bool);
    void append(Circ*);
    intptr_t init();          // Create a new qubit.
    void term(intptr_t);      // Delete a qubit.
    std::string print();
    Circuit* clone() { return (new Circuit(*this)); };
    Circuit* rev();
  private:
    std::list<intptr_t> _input;
    std::list<intptr_t> _output;
    std::list<Circ*> _gates;
    intptr_t _qid;
};

