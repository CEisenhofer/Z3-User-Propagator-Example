#include <iostream>
#include <stack>
#include <unordered_map>
#include <vector>
#include "z3++.h"
#define WriteLine(x) std::cout << (x) << std::endl

typedef std::vector<unsigned> model;

namespace std {

    template<>
    struct hash<z3::expr> {
        std::size_t operator()(const z3::expr &k) const {
          return k.hash();
        }
    };

    // Do not use Z3's == operator in the hash table
    template<>
    struct equal_to<z3::expr> {
        bool operator()(const z3::expr &lhs, const z3::expr &rhs) const {
          return z3::eq(lhs, rhs);
        }
    };
}

class test_propagator final : public z3::user_propagator_base {

    int nesting;

    std::unordered_map<z3::expr, z3::expr_vector> argToFcts;
    std::unordered_map<z3::expr, z3::expr> funcToArg;

    std::unordered_map<z3::expr, unsigned> currentModel;
    z3::expr_vector fixedValues;
    std::stack<unsigned> fixedCnt;

    std::vector<test_propagator *> childPropagators;

public:

    test_propagator(z3::context &c, int nesting) : z3::user_propagator_base(c), nesting(nesting), fixedValues(c) {
      register_fixed();
      register_created();
      register_final();
    }

    test_propagator(z3::solver *s) : z3::user_propagator_base(s), nesting(0), fixedValues(s->ctx()) {
      register_fixed();
      register_created();
      register_final();
    }

    ~test_propagator() {
      for (auto &child: childPropagators) {
        delete child;
      }
    }

    void final() override {
      WriteLine("Final (" + to_string(nesting) + ")");
      int j = 0;
      for (uint64_t i = 0; i < 100000000ull; i++) j++; // Delay this step
    }

    void push() override {
      WriteLine("Push (" + to_string(nesting) + ")");
      fixedCnt.push((unsigned) fixedValues.size());
    }

    void pop(unsigned num_scopes) override {
      WriteLine("Pop (" + to_string(nesting) + ")");
      for (unsigned i = 0; i < num_scopes; i++) {
        unsigned lastCnt = fixedCnt.top();
        fixedCnt.pop();
        for (auto j = fixedValues.size(); j > lastCnt; j--) {
          currentModel.erase(fixedValues[j - 1]);
        }
        fixedValues.resize(lastCnt);
      }
    }

    bool isValidAssignment(bool expectedResult, unsigned arg) {
      return expectedResult == ((arg & 1) == 1); // is odd
    }

    user_propagator_base *fresh(z3::context &ctx) override {
      WriteLine("Fresh context (" + to_string(nesting + 1) + "): " + to_string((uint64_t)(_Z3_context *)ctx));
      test_propagator *child = new test_propagator(ctx, nesting + 1);
      childPropagators.push_back(child);
      return child;
    }

    void fixed(const z3::expr &expr, const z3::expr &value) override {
      WriteLine("Fixed (" + to_string(nesting) + ") " + expr.to_string() + " to " + value.to_string());
      unsigned v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
      currentModel[expr] = value;
      fixedValues.push_back(expr);

      if (funcToArg.contains(expr)) {
        // is function
        z3::expr arg = funcToArg.at(expr);
        if (!arg.is_numeral() && !currentModel.contains(arg))
          return;
        unsigned argValue;
        if (arg.is_numeral()) {
          argValue = arg.get_numeral_uint();
        }
        else {
          argValue = currentModel[arg];
        }
        if (!isValidAssignment((bool) v, argValue)) {
          z3::expr_vector conflict(ctx());
          conflict.push_back(expr);
          conflict.push_back(arg);
          this->conflict(conflict);
        }
      }
      else if (argToFcts.contains(expr)) {
        // is argument
        z3::expr_vector fcts = argToFcts.at(expr);
        for (unsigned i = 0; i < fcts.size(); i++) {
          z3::expr fct = fcts[i];
          if (!currentModel.contains(fct))
            return;
          unsigned fctValue = currentModel[fct];
          if (!isValidAssignment((bool) fctValue, v)) {
            z3::expr_vector conflict(ctx());
            conflict.push_back(fct);
            conflict.push_back(expr);
            this->conflict(conflict);
          }
        }
      }
      else {
        WriteLine("Unexpected expression!");
      }
    }

    void created(const z3::expr &func) override {
      WriteLine("Created (" + to_string(nesting) + "): " + func.to_string());
      int argCnt = func.num_args();
      for (int i = 0; i < argCnt; i++) {
        z3::expr arg = func.arg(i);
        if (!arg.is_numeral()) {
          WriteLine("Registered " + arg.to_string());
          this->add(arg);
        }
        else {
          // WriteLine("Skipped registering " + arg.to_string());
        }

        funcToArg.emplace(std::make_pair(func, arg));
        argToFcts.try_emplace(arg, ctx()).first->second.push_back(func);
      }
    }
};

int main() {

  z3::set_param("smt.ematching", "false");
  z3::set_param("smt.mbqi", "true");
  z3::set_param("smt.mbqi.max_iterations", "1000000");

  z3::context context;
  z3::solver s(context, z3::solver::simple());
  test_propagator propagator(&s);
  WriteLine("Initial context: " + to_string((uint64_t)(_Z3_context *)context));

  const int size = 2;

  z3::sort_vector domain(context);
  domain.push_back(context.bv_sort(size));
  auto func = context.user_propagate_function(context.str_symbol("f"), domain, context.bool_sort());

  z3::expr x = context.constant("x", domain[0]);
  z3::expr y = context.constant("y", domain[0]);
  s.add(func(y) && z3::forall(x, implies(((x & 1) == 1), func(x))));

  Z3_enable_trace("model_checker");
  Z3_enable_trace("model");
  Z3_enable_trace("model_verbose");
  Z3_enable_trace("proto_model");
  WriteLine("Problem: " + s.assertions().to_string());
  s.check();
  WriteLine("Model: " + s.get_model().to_string());
  return 13;
}
