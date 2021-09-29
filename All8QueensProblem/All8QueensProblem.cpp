#include <conio.h>
#include <iostream>
#include <stack>
#include <unordered_map>
#include <vector>
#include <z3++.h>

using namespace std::string_literals;
using std::to_string;


struct user_propagator : z3::user_propagator_base {

	std::vector<int> lim;
	std::vector<int> trail;
        std::vector<unsigned> ids;
        std::vector<z3::expr> values;

        void _final() {
            std::cout << "Final" << std::endl;
#if 0
            // for some reason this doesn't work:
            for (auto & e : values)
                std::cout << "value: " << e << "\n";
#endif
            this->conflict(ids.size(), ids.data());
        }

	void _fixed(unsigned id, z3::expr const& e) {
            std::cout << "Fixed " << id << " = " << e << std::endl;
            values[id] = e;
	}

	user_propagator(z3::solver* s) : user_propagator_base(s) {
		std::cout << "Init" << std::endl;
		std::function<void(unsigned, z3::expr const&)> f1 = [this](auto&& PH1, auto&& PH2)
		{
			_fixed(std::forward<decltype(PH1)>(PH1), std::forward<decltype(PH2)>(PH2));
		};
		std::function<void()> f2 = [this]() {
			_final();
		};
		this->fixed(f1);
		this->register_final(f2);
	}

	void push() override {
		std::cout << "Push" << std::endl;
		lim.push_back(trail.size());
	}
	void pop(unsigned num_scopes) override {
		std::cout << "Pop" << std::endl;
		int lim_sz = lim.size() - num_scopes;
		lim = std::vector<int>(lim.begin(), lim.begin() + lim_sz);
	}

	user_propagator_base* fresh(Z3_context ctx) override {
		std::cout << "Fresh" << std::endl;
		return this;
	}
};

int main() {

	std::cout << "Size (n x n): ";

	std::string line;
	std::getline(std::cin, line);

	char* endptr;
	int num = strtol(line.c_str(), &endptr, 10);

	if (endptr == nullptr || endptr == line.c_str() || num < 4) {
		std::cout << "Invalid number: " << line << std::endl;
		exit(1);
	}

	std::vector<int*> solutions;

	z3::context context;
	z3::solver solver(context, z3::solver::simple());

	std::vector<z3::expr> queens;

	for (int i = 0; i < num; i++) {
		queens.push_back(context.bv_const(("q"s + to_string(i)).c_str(), num));
		// assert column range
		solver.add(z3::uge(queens.back(), 0));
		solver.add(z3::ult(queens.back(), num));
	}

	z3::expr_vector distinct(context);
	for (int i = 0; i < num; i++) {
            distinct.push_back(queens[i]);
	}

	solver.add(z3::distinct(distinct));

	for (int i = 0; i < num; i++) {
		for (int j = i - 1, k = -1; j >= 0; j--, k--) {
			solver.add(queens[i] + k != queens[j]);
		}
		for (int j = i - 1, k = 1; j >= 0; j--, k++) {
			solver.add(queens[i] + k != queens[j]);
		}
		for (int j = i + 1, k = -1; j < num; j++, k--) {
			solver.add(queens[i] + k != queens[j]);
		}
		for (int j = i + 1, k = 1; j < num; j++, k++) {
			solver.add(queens[i] + k != queens[j]);
		}
	}

	// std::cout << "Encoding: " << solver.to_smt2() << std::endl;

	user_propagator propagator(&solver);

        for (auto q : queens) {
            auto id = propagator.add(q);
            std::cout << "id " << id << " -> " << q << "\n";
            propagator.ids.push_back(id);
            propagator.values.push_back(q);
        }

	int solutionId = 1;

	while(true) {
		z3::check_result res = solver.check();

		if (res != z3::check_result::sat) {
			std::cout << "No more solution" << std::endl;
			break;
		}

		z3::model model = solver.get_model();

		std::cout << "Model #" << solutionId++ << ": " << model.to_string() << std::endl;

		z3::expr_vector blocking(context);

		for (int i = 0; i < num; i++) {
			blocking.push_back(queens[i] != model.eval(queens[i]));
		}

		solver.add(z3::mk_or(blocking));

		std::cout << std::endl;
	}

	_getch();

	return 0;
}
