#include <algorithm>
#include <chrono>
#include <iostream>
#include <random>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cstring>
// Add the Z3 API location to the compilers additional include directories
// Furthermore add the Z3 library
#include <c++/z3++.h>

using namespace std::string_literals;
using namespace std::chrono;
using std::to_string;

#define QUEEN
#define REPETITIONS 5

#ifndef QUEEN
#define ROOK
#endif

#define SIZE(x) std::extent<decltype(x)>::value

#if LOG
#define WriteEmptyLine std::cout << std::endl
#define WriteLine(x) std::cout << (x) << std::endl
#define Write(x) std::cout << x
#else
#define WriteEmptyLine
#define WriteLine(x)
#define Write(x)
#endif

class model {

public:

    unsigned int *values;
    int cnt;

    model(int cnt) : cnt(cnt), values(nullptr) {
        values = (unsigned int *) malloc(sizeof(unsigned int) * cnt);
    }

    ~model() {
        free(values);
        values = nullptr;
    }

    unsigned int &operator[](const int id) {
        return values[id];
    }

    void set(unsigned int pos, unsigned int value) const {
        values[pos] = value;
    }

    bool operator==(const model &other) const {
        if (cnt != other.cnt) {
            return false;
        }
        for (int i = 0; i < cnt; i++) {
            if (values[i] != other.values[i]) {
                return false;
            }
        }
        return true;
    }

    bool operator!=(const model &other) const {
        return !this->operator==(other);
    }

    std::string toString() {
        std::stringstream out;
        for (int i = 0; i < cnt; i++) {
            out << "q" << i + 1 << " = " << values[i] << "\n";
        }

        return out.str();
    }

    model *clone() {
        model *newModel = new model(cnt);
        memcpy(newModel->values, values, sizeof(unsigned int) * cnt);
        return newModel;
    }
};

struct model_hash_function {
    std::size_t operator()(const model &m) const {
        size_t hash = 0;
        for (int i = 0; i < m.cnt; i++) {
            hash *= m.cnt;
            hash += m.values[i];
        }
        return hash;
    }
};

class user_propagator : public z3::user_propagator_base {

protected:

    std::unordered_map<unsigned int, unsigned int> *id_mapping;
    model *currentModel;
    std::unordered_set<model, model_hash_function> modelSet;
    std::vector<unsigned int> fixedValues;
    std::stack<int> fixedCnt;
    int board;

    int solutionId = 1;

public:

    int getModelCount() const {
        return solutionId - 1;
    }

    void final() {
        this->conflict(fixedValues.size(), fixedValues.data());
        if (modelSet.find(*currentModel) != modelSet.end()) {
            WriteLine("Got already computed model");
            return;
        }
        Write("Model #" << solutionId << ":\n");
        solutionId++;
        for (int i = 0; i < fixedValues.size(); i++) {
            unsigned int id = fixedValues[i];
            WriteLine("q" + std::to_string((*id_mapping)[id]) + " = " + std::to_string((*currentModel)[id]));
        }
        modelSet.insert(*currentModel);
        WriteEmptyLine;

        currentModel = currentModel->clone();
    }

    static unsigned int bvToInt(z3::expr e) {
        return (unsigned int) e.get_numeral_int();
    }

    virtual void fixed(unsigned int id, z3::expr const &e) {
        fixedValues.push_back(id);
        unsigned int value = bvToInt(e);
        currentModel->set((*id_mapping)[id], value);
    }

    user_propagator(z3::solver *s, std::unordered_map<unsigned int, unsigned int> *idMapping, int board)
            : user_propagator_base(s), id_mapping(idMapping), board(board) {

        currentModel = new model(board);

        std::function<void(unsigned, z3::expr const &)> f1 = [this](unsigned id, z3::expr e) {
            fixed(id, e);
        };
        std::function<void()> f2 = [this]() {
            final();
        };
        this->register_fixed(f1);
        this->register_final(f2);
    }

    ~user_propagator() {
        delete currentModel;
        currentModel = nullptr;
    }

    void push() override {
        fixedCnt.push(fixedValues.size());
    }

    void pop(unsigned num_scopes) override {
        for (int i = 0; i < num_scopes; i++) {
            int lastCnt = fixedCnt.top();
            fixedCnt.pop();
            for (int j = fixedValues.size(); j > lastCnt; j--) {
                currentModel->set(fixedValues[j - 1], -1);
            }
            fixedValues.resize(lastCnt);
        }
    }

    user_propagator_base *fresh(Z3_context ctx) override { return this; }
};

class user_propagator_with_theory : public user_propagator {

public:

    void fixed(unsigned int id, z3::expr const &e) override {
        unsigned int queenId = (*id_mapping)[id];
        unsigned int queenPos = bvToInt(e);

        if (queenPos >= board) {
            this->conflict(1, &id);
            return;
        }

        for (unsigned int fixed : fixedValues) {
            int otherId = (*id_mapping)[fixed];
            int otherPos = (*currentModel)[fixed];

            if (queenPos == otherPos) {
                const unsigned int conflicting[] = {id, fixed};
                this->conflict(2, conflicting);
                continue;
            }
#ifdef QUEEN
            int diffY = abs((int) queenId - otherId);
            int diffX = abs((int) queenPos - otherPos);
            if (diffX == diffY) {
                const unsigned int conflicting[] = {id, fixed};
                this->conflict(2, conflicting);
            }
#endif
        }

        fixedValues.push_back(id);
        currentModel->set((*id_mapping)[id], queenPos);
    }

    user_propagator_with_theory(z3::solver *s, std::unordered_map<unsigned int, unsigned int> *idMapping, int board)
            : user_propagator(s, idMapping, board) {}
};

int log2i(int n) {
    if (n <= 0) {
        return 0;
    }
    if (n <= 2) {
        return 1;
    }
    int l = 1;
    int i = 0;
    while (l < n) {
        l <<= 1;
        i++;
    }
    return i;
}

std::vector<z3::expr> createQueens(z3::context &context, int num) {
    std::vector<z3::expr> queens;
    int bits = log2i(num) + 1 /*to detect potential overflow in the diagonal*/;
    for (int i = 0; i < num; i++) {
        queens.push_back(context.bv_const(("q"s + to_string(i)).c_str(), bits));
    }
    return queens;
}

void createConstraints(z3::context &context, z3::solver &solver, const std::vector<z3::expr> &queens) {
    for (int i = 0; i < queens.size(); i++) {
        // assert column range
        solver.add(z3::uge(queens[i], 0));
        solver.add(z3::ule(queens[i], queens.size() - 1));
    }

    z3::expr_vector distinct(context);
    for (const z3::expr & queen : queens) {
        distinct.push_back(queen);
    }

    solver.add(z3::distinct(distinct));

#ifdef QUEEN
    for (int i = 0; i < queens.size(); i++) {
        for (int j = i + 1; j < queens.size(); j++) {
            solver.add((j - i) != (queens[j] - queens[i]));
            solver.add((j - i) != (queens[i] - queens[j]));
        }
    }
#endif
}

int test01(int num, bool simple) {
    z3::context context;
    z3::solver solver(context, !simple ? Z3_mk_solver(context) : Z3_mk_simple_solver(context));

    std::vector<z3::expr> queens = createQueens(context, num);

    createConstraints(context, solver, queens);

    int solutionId = 1;

    while (true) {
        z3::check_result res = solver.check();

        if (res != z3::check_result::sat) {
            break;
        }

        z3::model model = solver.get_model();

        WriteLine("Model #" + std::to_string(solutionId) + ":");
        solutionId++;

        z3::expr_vector blocking(context);

        for (int i = 0; i < num; i++) {
            z3::expr eval = model.eval(queens[i]);
            WriteLine(("q" + std::to_string(i + 1) + " = " + std::to_string(eval.get_numeral_int())));
            blocking.push_back(queens[i] != eval);
        }

        solver.add(z3::mk_or(blocking));

        WriteEmptyLine;
    }
    return solutionId - 1;
}

inline int test0(int num) {
    return test01(num, false);
}

inline int test1(int num) {
    return test01(num, true);
}

int test23(int num, bool withTheory) {
    z3::context context;
    z3::solver solver(context, Z3_mk_simple_solver(context));
    std::unordered_map<unsigned int, unsigned int> idMapping;

    user_propagator *propagator;
    if (!withTheory) {
        propagator = new(alloca(sizeof(user_propagator))) user_propagator(&solver, &idMapping, num);
    }
    else {
        propagator = new(alloca(sizeof(user_propagator_with_theory))) user_propagator_with_theory(&solver, &idMapping, num);
    }

    std::vector<z3::expr> queens = createQueens(context, num);

    for (int i = 0; i < queens.size(); i++) {
        unsigned int id = propagator->add(queens[i]);
        idMapping[id] = i;
    }

    if (!withTheory) {
        createConstraints(context, solver, queens);
    }

    solver.check();
    int res = propagator->getModelCount();
    propagator->~user_propagator();
    return res;
}

inline int test2(int num) {
    return test23(num, false);
}

inline int test3(int num) {
    return test23(num, true);
}

int main() {

    for (int num = 4; num <= 12; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        unsigned int seed = high_resolution_clock::now().time_since_epoch().count();
        const char *testName[] =
                {
                        "Blocking clauses (Default solver)",
                        "Blocking clauses (Simple solver)",
                        "Adding conflicts",
                        "Custom theory + conflicts",
                };
        int permutation[4] =
                {
                        0,
                        1,
                        2,
                        3,
                };
        double timeResults[REPETITIONS * SIZE(permutation)];

        for (int rep = 0; rep < REPETITIONS; rep++) {
            // Execute strategies in a randomised order
            std::shuffle(&permutation[0], &permutation[SIZE(permutation) - 1], std::default_random_engine(seed));

            for (int i : permutation) {
                int modelCount = -1;

                auto now1 = high_resolution_clock::now();

                switch (i) {
                    case 0:
                        modelCount = test0(num);
                        break;
                    case 1:
                        modelCount = test1(num);
                        break;
                    case 2:
                        modelCount = test2(num);
                        break;
                    case 3:
                        modelCount = test3(num);
                        break;
                    default:
                        WriteLine("Unknown case");
                        break;
                }
                auto now2 = high_resolution_clock::now();
                duration<double, std::milli> ms = now2 - now1;
                std::cout << testName[i] << " took " << ms.count() << "ms (" << modelCount << " models)" << std::endl;
                timeResults[rep * SIZE(permutation) + i] = ms.count();
                WriteLine("-------------");
            }
        }

        std::cout << "\n" << std::endl;

        for (int i = 0; i < SIZE(permutation); i++) {
            std::cout << testName[i];
            double sum = 0;
            for (int j = 0; j < REPETITIONS; j++) {
                std::cout << " " << timeResults[j * SIZE(permutation) + i] << "ms";
                sum += timeResults[j * SIZE(permutation) + i];
            }
            std::cout << " | avg: " << sum / REPETITIONS << "ms" << std::endl;
        }

        std::cout << std::endl;
    }
}