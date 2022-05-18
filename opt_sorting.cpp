#include <initializer_list>
#include "common.h"

class NetworkConstructor {

    z3::context& context;

    z3::expr_vector sorted;
    
protected:

    z3::expr_vector in, out;
    std::vector<std::pair<z3::expr, z3::expr>> decisionExpressions;

    unsigned lines;

public:

    NetworkConstructor(z3::context& context, unsigned lines) :
        context(context),
        sorted(context),
        in(context),
        out(context),
        lines(lines) {

        for (unsigned i = 0; i < lines; i++) {
            in.push_back(context.bv_const(("in" + std::to_string(i)).c_str(), 1));
            out.push_back(context.bv_const(("out" + std::to_string(i)).c_str(), 1));
        }

        for (unsigned i = 1; i < lines; i++) {
            sorted.push_back(z3::ule(out[i - 1], out[i]));
        }
    }

    virtual ~NetworkConstructor() = default;

    NetworkConstructor(z3::solver& s, unsigned lines, unsigned depth, bool usesQuantifiers) :
        NetworkConstructor(s.ctx(), lines) {
        s.add(buildAbstractNetwork(depth, usesQuantifiers ? CompleteQuantified : OnlyPreconditions));
    }

    enum NetworkType {
        CompleteQuantified,
        BodyUnquantified,
        OnlyPreconditions,
    };

    std::pair<z3::expr, z3::expr> addMultiComparator(z3::context& ctx, z3::expr_vector assertions, z3::expr_vector& premisses,
        const z3::expr_vector& in, z3::expr_vector& out, const unsigned id, NetworkType type) const {

        unsigned cnt = in.size();

        if (out.empty()) {
            for (unsigned i = 0; i < cnt; i++) {
                if (type == CompleteQuantified) {
                    out.push_back(ctx.constant(("x_" + std::to_string(id) + "_" + std::to_string(i)).c_str(), in[i].get_sort()));
                }
                else {
                    const z3::expr e = z3::expr(ctx, 
                        Z3_mk_fresh_const(ctx, 
                            ("x_" + std::to_string(id) + "_" + std::to_string(i)).c_str(), 
                            in[i].get_sort()));
                    out.push_back(e);
                }
            }
        }
        else {
            assert(in.size() == out.size());
        }

        //unsigned bits = log2i((cnt * cnt - cnt) / 2);
        unsigned bits = log2i(cnt);
        z3::expr from = type != BodyUnquantified ? ctx.bv_const(("from" + std::to_string(id)).c_str(), bits) : decisionExpressions[id].first;
        z3::expr to = type != BodyUnquantified ? ctx.bv_const(("to" + std::to_string(id)).c_str(), bits) : decisionExpressions[id].second;

        if (type != OnlyPreconditions) {
            for (unsigned i = 0; i < cnt; i++) {
                for (unsigned j = i + 1; j < cnt; j++) {

                    z3::expr_vector assignment(ctx);

                    // copy all except two
                    for (unsigned k = 0; k < cnt; k++) {
                        if (k == i || k == j) continue;
                        assignment.push_back(in[k] == out[k]);
                    }
                    assignment.push_back(z3::ite(
                        z3::ule(in[i], in[j]),
                        in[i] == out[i] && in[j] == out[j],
                        in[i] == out[j] && in[j] == out[i]));
                    premisses.push_back(z3::implies(from == (signed)i && to == (signed)j, z3::mk_and(assignment)));
                }
            }
        }
        if (type != BodyUnquantified) {
            assertions.push_back(z3::ult(from, to));
            assertions.push_back(z3::ule(to, cnt - 1));
        }
        return { from, to };
    }

    z3::expr buildAbstractNetwork(unsigned depth, z3::expr_vector& in, z3::expr_vector& out, NetworkType type) {

        assert(in.size() == lines);

        z3::expr_vector in2(context);
        z3::expr_vector* _in1 = &in, * _in2 = &in2;
        z3::expr_vector premisses(context), bound(context);
        z3::expr_vector assertions(context);

        if (type == CompleteQuantified) {
            for (unsigned i = 0; i < in.size(); i++) {
                bound.push_back(in[i]);
                bound.push_back(out[i]);
            }
        }

        for (unsigned i = 0; i < depth - 1; i++) {

            auto decision = addMultiComparator(context, assertions, premisses, *_in1, *_in2, i, type);

        	if (type != BodyUnquantified) {
                decisionExpressions.push_back(decision);
            }

            if (type == CompleteQuantified) {
                for (const auto& v : *_in2)
                    bound.push_back(v);
            }

            _in1->resize(0);
            const auto swp = _in1;
            _in1 = _in2;
            _in2 = swp;
        }

        auto decision = addMultiComparator(context, assertions, premisses, *_in1, out, depth - 1, type);

    	if (type != BodyUnquantified) {
            decisionExpressions.push_back(decision);
        }

        switch (type) {
            case CompleteQuantified:
                assertions.push_back(z3::forall(bound, z3::implies(mk_and(premisses), z3::mk_and(sorted))));
                break;
            case BodyUnquantified:
                assertions.push_back(!z3::mk_and(premisses));
                break;
            case OnlyPreconditions:
            default:
                // do this check in the final callback
                break;
        }

        return mk_and(assertions);
    }

    z3::expr buildAbstractNetwork(unsigned depth, NetworkType type) {
        z3::expr_vector in_cpy(context);
        for (const auto& v : in) {
            in_cpy.push_back(v);
        }
        return buildAbstractNetwork(depth, in_cpy, out, type);
    }

    // creates a concrete network without preconditions and negated
    std::vector<z3::expr_vector> buildConcreteNetwork(z3::solver& solver, const std::vector<unsigned>& connections) const {

        assert(lines == in.size());
        assert((connections.size() & 1) == 0);

        std::vector<z3::expr_vector> intermediates;
        for (unsigned i = 0; i < in.size(); i++) {
            intermediates.emplace_back(solver.ctx());
            intermediates.back().push_back(in[i]);
        }

        z3::expr_vector assertions(solver.ctx());

        for (unsigned i = 0; i < connections.size(); i += 2) {
            unsigned i1 = connections[i];
            unsigned i2 = connections[i + 1];
            z3::expr x = solver.ctx().constant(("x_" + std::to_string(i >> 1)).c_str(), in[i1].get_sort());
            z3::expr y = solver.ctx().constant(("y_" + std::to_string(i >> 1)).c_str(), in[i2].get_sort());

            assertions.push_back(
                z3::ite(
                    z3::ule(intermediates[i1].back(), intermediates[i2].back()),
                    intermediates[i1].back() == x && intermediates[i2].back() == y,
                    intermediates[i1].back() == y && intermediates[i2].back() == x)
            );
            intermediates[i1].push_back(x);
            intermediates[i2].push_back(y);
        }

        for (unsigned i = 0; i < intermediates.size(); i++) {
            assertions.push_back(intermediates[i].back() == out[i]);
        }

        const z3::expr assertion = z3::mk_and(assertions) && !z3::mk_and(sorted);
        solver.add(assertion);

        return intermediates;
    }


    const std::vector<std::pair<z3::expr, z3::expr>>& getDecisionVariables() const {
        return decisionExpressions;
    }
};

class OptSortedPropagator2 : public NetworkConstructor, z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<unsigned> fixedIndexes;
    simple_model model;

    std::unordered_map<z3::expr, unsigned> exprToId; // first bit: from (0) or to (1). remaining bits: index
    std::unordered_map<unsigned, z3::expr> idToExpr; // --||--

    std::vector<unsigned> occurrences; // number
    std::unordered_map<z3::expr, z3::expr_vector> bitvectorToBit;

    std::unordered_set<simple_model> allSolutions; // for all_sat

    z3::solver* const subSolver;

    const unsigned depth;
    const unsigned lines;
    const unsigned bitCnt;

    const Params params;
    
    unsigned getOtherIndex(unsigned x) const {
        return x ^ 1;
    }

    bool getNext(unsigned x, unsigned& next) const {
        next = x + 2;
        return next < (depth << 1);
    }

    bool getPrev(unsigned x, unsigned& prev) const {
        if (x < 2)
            return false;
        prev = x - 2;
        return true;
    }

    bool has(unsigned idx, unsigned& v) const {
        v = model[idx];
        return v != -1;
    }

    void conflicting(std::initializer_list<unsigned> args) {
        conflicting(std::vector(args.begin(), args.end()));
    }

    void conflicting(std::vector<unsigned> args) {
        z3::expr_vector conflicting(ctx());
        for (const auto& arg : args) {
            z3::expr e = idToExpr.at(arg);
            conflicting.push_back(e);
        }
        this->conflict(conflicting);
    }

    std::string draw() const {
        const std::string sep = "--";
        std::string s;
        const unsigned lineSize = sep.size() * (depth + 1) /*sep*/ + depth /*|+?*/ + 1 /*\n*/;
        s.reserve(lineSize * lines);

        for (unsigned i = 0; i < lines; i++) {
            for (unsigned j = 0; j < depth; j++) {
                s += sep + "-";
            }
            s += sep + "\n";
            assert(s.length() == (i + 1) * lineSize);
        }

        for (unsigned i = 0; i < depth; i++) {
            unsigned v1, v2;
            if (has(i << 1, v1) & has(getOtherIndex(i << 1), v2)) {
                for (unsigned j = 0; j < lines; j++) {
                    if (j == v1 || j == v2)
                        s[j * lineSize + sep.size() * (i + 1) + i] = '+';
                    else if (j > MIN(v1, v2) && j < MAX(v1, v2))
                        s[j * lineSize + sep.size() * (i + 1) + i] = '|';
                }
            }
            else {
                for (unsigned j = 0; j < lines; j++) {
                    if (j == v1 || j == v2)
                        s[j * lineSize + sep.size() * (i + 1) + i] = '+';
                    else
                        s[j * lineSize + sep.size() * (i + 1) + i] = '?';
                }
            }
        }
        return s;
    }

    void checkNext(unsigned idx1, unsigned idx2, unsigned v1, unsigned v2) {
        if (!params.adjacent)
            return;
        unsigned idx3;
        unsigned v3, v4;
        if (getNext(idx1, idx3) && has(idx3, v3) && has(getOtherIndex(idx3), v4)) {
            if (v1 == v3 && v2 == v4) {
                // std::cout << "Exit early (1)" << std::endl;
                conflicting({ idx1, idx2, idx3, getOtherIndex(idx3) });
            }
        }
    }

    void checkPrev(unsigned idx1, unsigned idx2, unsigned v1, unsigned v2) {
        if (!params.adjacent)
            return;
        unsigned idx3;
        unsigned v3, v4;
        if (getPrev(idx1, idx3) && has(idx3, v3) && has(getOtherIndex(idx3), v4)) {
            if (v1 == v3 && v2 == v4) {
                // std::cout << "Exit early (2)" << std::endl;
                conflicting({ idx1, idx2, idx3, getOtherIndex(idx3) });
            }
        }
    }

    unsigned singleBitIndexStart() const {
        return 2 * decisionExpressions.size();
    }

    std::vector<std::vector<unsigned>> distance;

    unsigned maxDistanceIndex() const {
        return (depth + 1) * lines; // input & output inclusive
    }


    unsigned flatten(unsigned dep, unsigned line) const {
        // dep = 0 ==> input
        assert(dep < depth + 1);
        return dep * lines;
    }

    std::pair<unsigned, unsigned> decompose(unsigned index) const {
        assert(index < maxDistanceIndex());
        unsigned line = index % lines;
        unsigned dep = index / lines;
        return std::make_pair(dep, line);
    }

    std::string distanceMatrixToString() const {
        auto indexToString = [this](unsigned idx) -> std::string {
            const auto d = decompose(idx);
            if (d.first == 0) {
                return "in" + std::to_string(d.second);
            }
            return "decision line " + std::to_string(d.second) + " node " + std::to_string(d.first - 1);
        };

        std::string s;
        for (unsigned i = 0; i < distance.size(); i++) {
            std::string node1 = indexToString(i);
            s += "Reachable from " + node1 + ":\n";
            for (unsigned j = 0; j < distance.size(); j++) {
                std::string node2 = indexToString(j);
                s += "\t" + node2 + ": " + 
                    (distance[i][j] == (unsigned)-1 ? "unreachable" : std::to_string(distance[i][j])) + "\n";
            }
        }
        return s;
    }

    void floydWarshall() {

        const unsigned mi = maxDistanceIndex();
        distance.clear();
        distance.reserve(mi);
        // build first distance matrix
        for (unsigned i = 0; i < mi /*the last node does not lead anywhere*/; i++) {
            distance.emplace_back();
            distance.reserve(mi);
            std::pair<unsigned, unsigned> p1 = decompose(i);
            for (unsigned j = 0; j < mi; j++) {
                std::pair<unsigned, unsigned> p2 = decompose(j);
                unsigned v1, v2;
                if (p1.second == p2.second) { // same line
                    if (p1.first == p2.first) {
                        distance.back().push_back(0); // same element
                    }
                    else if (p1.first < p2.first) {
                        distance.back().push_back(p2.first - p1.first); // same element
                    }
                    else {
                        distance.back().push_back((unsigned)-1); // element before the other
                    }
                }
                else if (p1.first == p2.first) {
                    // two elements on different lines but same position cannot be connected
                    // ==> optimization: We rather connect diagonal than vertical (does not change anything
                    // but we avoid 0-length jumps to another line in case they are connected)
                    distance.back().push_back((unsigned)-1);
                    // So we have
                    // -----------
                    //       /
                    //      1
                    //     /
                    // -----------
                    // instead of 
                    // -----------
                    //     |
                    //     0
                    //     |
                    // -----------
                    // as each depth has at most one connection
                    // (so we cannot move over multiple connections at once anyway)
                }
                else if (p1.first < p2.first &&
                    p2.first - p1.first == 1 &&
                    has(p1.first << 1, v1) &&
                    has(getOtherIndex(p1.first << 1), v2) && (
                        (v1 == p1.second && v2 == p2.second) ||
                        (v1 == p2.second && v2 == p1.second)
                        )) { // same depth
                    distance.back().push_back(1); // connected lines
                }
                else {
                    distance.back().push_back((unsigned)-1); // don't know
                }
            }
        }

        for (unsigned i = 0; i < mi; i++) {
            for (unsigned j = 0; j < mi; j++) {
                for (unsigned k = 0; k < mi; k++) {
                    if (distance[j][i] != (unsigned)-1 && 
                        distance[i][k] != (unsigned)-1 && 
                        distance[j][k] > distance[j][i] + distance[i][k]) {

                        distance[j][k] = distance[j][i] + distance[i][k];
                    }
                }
            }
        }
    }

    void checkReachability() {

        if (!params.connected || fixedIndexes.size() < 2 * depth) {
            return;
        }

        if (distance.empty())
            floydWarshall();

        // std::cout << draw() << std::endl;
        // std::cout << distanceMatrixToString() << std::endl;

        for (unsigned i = 0; i < lines; i++) {
            for (unsigned j = 0; j < lines; j++) {
                if (distance[i][lines * depth + j] == (unsigned)-1) {
                    // std::cout << "Cannot reach " << j << " from " << i << std::endl;
                    // assert that at least one element k that is reachable from i is connected to j
                    z3::expr_vector correction(ctx());

                    for (unsigned k = 0; k < depth * lines; k++) {
                        if (distance[i][k] != (unsigned)-1) {
                            auto d = decompose(k);
                            if (d.second < j) {
                                correction.push_back(
                                    decisionExpressions[d.first].first == (signed)d.second &&
                                    decisionExpressions[d.first].second == (signed)j
                                );
                            }
                            else {
                                correction.push_back(
                                    decisionExpressions[d.first].first == (signed)j &&
                                    decisionExpressions[d.first].second == (signed)d.second
                                );
                            }
                        }
                    }

                    z3::expr_vector empty(ctx());
                    z3::expr conseq = z3::mk_or(correction);
                    // std::cout << "Propagated: " << conseq.to_string() << std::endl;
                    this->propagate(empty, conseq);
                    if (!params.connected_all)
                        return;
                }
            }
        }
    }

public:

    OptSortedPropagator2(z3::solver& s, unsigned lines, unsigned depth, Params params) :
            NetworkConstructor(s, lines, depth, !params.simulate_quantifier),
            user_propagator_base(&s),
            subSolver(params.simulate_quantifier ? new z3::solver(ctx(), z3::solver::simple()) : nullptr),
            depth(depth),
            lines(lines),
            bitCnt(decisionExpressions[0].first.get_sort().bv_size()),
            params(params) {

        this->register_fixed();
        if (params.simulate_quantifier)
            this->register_final();
        if (params.decide)
            this->register_decide();
        
        for (unsigned i = 0; i < depth; i++) {
            this->add(decisionExpressions[i].first);
            exprToId.emplace(decisionExpressions[i].first, i << 1);
            idToExpr.emplace(i << 1, decisionExpressions[i].first);
            
            this->add(decisionExpressions[i].second);
            exprToId.emplace(decisionExpressions[i].second, (i << 1) | 1);
            idToExpr.emplace((i << 1) | 1, decisionExpressions[i].second);

            model.push_back((unsigned)-1);
            model.push_back((unsigned)-1);
        }

        if (params.decide_occurences) {

            for (unsigned i = 0; i < lines; i++) {
                occurrences.push_back(0);
            }

            // model must contain the individual bits
            for (unsigned i = 0; i < depth; i++) {
                z3::expr_vector bits1(ctx()), bits2(ctx());
                for (unsigned j = 0; j < bitCnt; j++) {
                    z3::expr e1 = decisionExpressions[i].first.bit2bool(j);
                    z3::expr e2 = decisionExpressions[i].second.bit2bool(j);
                    unsigned id = decisionExpressions.size() + i * bitCnt + j;
                    this->add(e1);
                    this->add(e2);
                    bits1.push_back(e1);
                    bits2.push_back(e2);
                    model.push_back((unsigned)-1);
                    model.push_back((unsigned)-1);
                    exprToId.emplace(e1, (id << 1) | 0);
                    idToExpr.emplace((id << 1) | 0, e1);
                    exprToId.emplace(e2, (id << 1) | 1);
                    idToExpr.emplace((id << 1) | 1, e2);
                }
                bitvectorToBit.emplace(decisionExpressions[i].first, bits1);
                bitvectorToBit.emplace(decisionExpressions[i].second, bits2);
            }
        }
    }

    ~OptSortedPropagator2() override {
        delete subSolver;
    }

    void push() override {
        prevFixedCnt.push(fixedIndexes.size());
    }

    void pop(unsigned int num_scopes) override {
        // std::cout << "Popped " << num_scopes << " levels" << std::endl;
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedIndexes.size(); j > prevFixed; j--) {
                if (params.decide_occurences && fixedIndexes[j - 1] < singleBitIndexStart())
                    occurrences[model[fixedIndexes[j - 1]]]--;

                model[fixedIndexes[j - 1]] = (unsigned)-1;
                // std::cout << "Popped: " << idToExpr.at(fixedIndexes[j - 1]).to_string() << std::endl;
                fixedIndexes.pop_back();
            }
        }
    }

    unsigned lastIndex = (unsigned)-1;
    unsigned setTo = (unsigned)-1;

    void fixed(const z3::expr &ast, const z3::expr &value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        std::cout << "Fixed " + ast.to_string() + " to " + value.to_string() << std::endl;
        if (!exprToId.contains(ast))
            return;
        distance.clear();
        unsigned v1 = value.is_true() ? 1 : value.is_false() ? 0 : value.get_numeral_uint();
        unsigned v2;
        unsigned idx1 = exprToId.at(ast);
        unsigned idx2 = getOtherIndex(idx1);

        fixedIndexes.push_back(idx1);
        model[idx1] = v1;

        if (idx1 >= singleBitIndexStart())
            // just a single bit
            return;

        setTo = (unsigned)-1;

        if (params.decide_occurences)
            occurrences[v1]++;

        if (!has(idx2, v2)) {
            return;
        }

        checkNext(idx1, idx2, v1, v2);
        checkPrev(idx1, idx2, v1, v2);
        checkReachability();
    }

    void final() override {
        if (!params.simulate_quantifier)
            return;

        simple_model m;
        m.reserve(singleBitIndexStart());
        for (unsigned i = 0; i < singleBitIndexStart(); i++) {
            m.push_back(model[i]);
        }
        if (params.all_sat && allSolutions.contains(m))
            return;

        subSolver->push();
        auto intermediate = buildConcreteNetwork(*subSolver, m);

        z3::check_result result = subSolver->check();
        if (result == z3::check_result::unknown) {
            throw z3::exception("Unknown");
        }
        if (result == z3::check_result::sat) {
            z3::model couterexample = subSolver->get_model();
            z3::expr_vector new_in(ctx());
            z3::expr_vector new_out(ctx());
            std::cout << draw() << std::endl;
            std::cout << "Sorted:";
            for (unsigned i = 0; i < in.size(); i++) {
                new_in.push_back(couterexample.eval(in[i]));
                std::cout << " " << couterexample.eval(in[i]).to_string();
            }
            std::cout << "\nto: ";
            for (unsigned i = 0; i < out.size(); i++) {
                new_out.push_back(couterexample.eval(out[i]));
                std::cout << " " << couterexample.eval(out[i]).to_string();
            }
            std::cout << std::endl;

            z3::expr_vector empty(ctx());
            const z3::expr prop = buildAbstractNetwork(depth, new_in, new_out, BodyUnquantified);
            this->propagate(empty, prop);
        }
        else if (params.all_sat) {
            allSolutions.emplace(m);
            conflicting(m);
        }
        subSolver->pop();
    }

    bool setLast(unsigned i, z3::expr& val, unsigned& bit, Z3_lbool& is_pos) {
        if (model[i] == (unsigned)-1) {
            val = idToExpr.at(i);
            bit = 0;
            if (params.decide_random)
                is_pos = (rand() % 2 == 0) ? Z3_L_FALSE : Z3_L_TRUE;
            else
                is_pos = Z3_L_UNDEF;
            lastIndex = i;
            WriteLine("Changed to: " + val.to_string());
            return true;
        }
        if (model[getOtherIndex(i)] == (unsigned)-1) {
            val = idToExpr.at(getOtherIndex(i));
            bit = 0;
            if (params.decide_random)
                is_pos = (rand() % 2 == 0) ? Z3_L_FALSE : Z3_L_TRUE;
            else
                is_pos = Z3_L_UNDEF;
            lastIndex = getOtherIndex(i);
            WriteLine("Changed to: " + val.to_string());
            return true;
        }
        return false;
    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        WriteLine("Decide: " + val.to_string() + " bit: " + std::to_string(bit) + " = " + (is_pos == Z3_L_FALSE ? "false" : "true"));
        std::cout << "Decide: " + val.to_string() + " bit: " + std::to_string(bit) + " = " + (is_pos == Z3_L_FALSE ? "false" : "true") << std::endl;
        if (lastIndex == (unsigned)-1) {
            lastIndex = exprToId.at(val);
        }
        if (lastIndex >= singleBitIndexStart()) {
            lastIndex = (((lastIndex - singleBitIndexStart()) >> 1) / bitCnt) << 1 | (lastIndex & 1);
        }
        setLast(lastIndex, val, bit, is_pos);

        if (params.decide_occurences) {
            unsigned other = model[getOtherIndex(lastIndex)];
            // choose minimal
            setTo = 0;
            for (unsigned i = 1; i < occurrences.size(); i++) {
                if (i != other /*avoid setting both from/to to the same value*/ && 
                    occurrences[setTo] > occurrences[i] /*it should be the least occurrence*/)
                    setTo = i;
            }
            // setTo has the least occurrences
            
            // get least unassigned bit of val
            unsigned j =
                (singleBitIndexStart() + (((lastIndex >> 1) * bitCnt) << 1)) | (lastIndex & 1);

            for (unsigned i = 0; i < bitCnt; i++) {
                if (model[j + 2 * i] == (unsigned)-1) {
                    val = idToExpr.at(j + 2 * i);
                    // set this bit to the i^th bit of the least occurring element
                    bit = 0;
                    is_pos = ((1 << i) & setTo) ? Z3_L_TRUE : Z3_L_FALSE;
                    // std::cout << "Decide: " + val.to_string() + " = " + (is_pos == Z3_L_FALSE ? "false" : "true") << std::endl;
                    return;
                }
            }
            assert(false);
        }
    }

    user_propagator_base *fresh(z3::context &ctx) override {
        return nullptr;
    }

    std::vector<simple_model> getSolutions() const {
        std::vector<simple_model> models;
        models.reserve(allSolutions.size());
        for (const auto& solution : allSolutions) {
            models.push_back(solution);
        }
        return models;
    }

};

void decodeValue(unsigned id, unsigned cnt, unsigned &v1, unsigned &v2) {
    for (unsigned i = 0; i < cnt; i++) {
        for (unsigned j = i + 1; j < cnt; j++, id--) {
            if (id == 0) {
                v1 = i;
                v2 = j;
                return;
            }
        }
    }
    assert(false);
}

int opt_sorting(unsigned* args, Params params) {
    
    unsigned start = args[1];
    bool down = args[2];
    
    if (start == 0) 
        return -1;

    assert(!params.all_sat || params.propagator);
    assert(!params.all_sat || params.simulate_quantifier);
    
    z3::context context;
    
    std::vector<simple_model> all_models;
    std::vector<std::pair<z3::expr, z3::expr>> decisions;
    const z3::model* m = nullptr;
    
    unsigned depth = start;
    while (depth > 0) {
        z3::solver s(context, params.propagator ? Z3_mk_simple_solver(context) : Z3_mk_solver(context));

        NetworkConstructor* constructor;
        if (params.propagator) {
            constructor = new OptSortedPropagator2(s, args[0], depth, params);
        }
        else {
            constructor = new NetworkConstructor(s, args[0], depth, true);
        }

        decisions = constructor->getDecisionVariables();
        
        std::cout << "Checking if solvable with depth: " << depth << std::endl;
        // std::cout << "F: " << s.assertions().to_string() << std::endl;
        
        z3::check_result result = s.check();
        
        std::cout << (result == z3::check_result::sat ? "SAT" : (result == z3::check_result::unsat ? "UNSAT" : "UNKNOWN")) << std::endl;

        if (params.all_sat) {
            all_models = ((OptSortedPropagator2*)constructor)->getSolutions();
        }
        delete constructor;
        
        if (result == z3::sat) {
            delete m;
            m = new z3::model(s.get_model());
            if (!down)
                break;
            m = nullptr;
        }
        else if (result == z3::unsat) {
            if (down)
                break;
            if (params.all_sat && !all_models.empty())
                break;
        }
        else {
            std::cout << s.reason_unknown() << std::endl;
            return -1;
        }
        
        if (down)
            depth--;
        else
            depth++;
    }

    if (!params.all_sat) {
        std::cout << "Model: " << m->to_string() << std::endl;
        for (unsigned i = 0; i < decisions.size(); i++) {
            unsigned v1 = m->eval(decisions[i].first).get_numeral_uint(), v2 = m->eval(decisions[i].second).get_numeral_uint();
            std::cout << "Compare: " << v1 << " and " << v2 << std::endl;
        }
    }
    else {
        std::cout << all_models.size() << " Models:" << std::endl;
        for (unsigned i = 0; i < all_models.size(); i++) {
            std::cout << "Model " << (i + 1) << ":" << std::endl;
            std::vector<unsigned> model = all_models[i];
            for (unsigned j = 0; j < model.size(); j += 2) {
                std::cout << model[j] << "-" << model[j + 1] << std::endl;
            }
        }
    }
    delete m;
    return (signed)(depth + down);
}