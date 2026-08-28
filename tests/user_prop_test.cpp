/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "gtest/gtest.h"

#include <cstdio>
#include <vector>

#include "cryptominisat5/cryptominisat.h"
#include "cryptominisat5/user_prop.h"
#include "src/solver.h"
#include "src/solverconf.h"
#include "test_helper.h"

using namespace CMSat;
using std::vector;

namespace {

// A propagator that does nothing at all: the solver must behave exactly as if
// no propagator were connected.
class NoopPropagator : public ExternalPropagator
{
public:
    uint32_t num_assignment_notifications = 0;
    uint32_t num_new_level_notifications = 0;
    uint32_t num_backtrack_notifications = 0;
    uint32_t num_model_checks = 0;

    void notify_assignment(const vector<Lit>&) override {
        num_assignment_notifications++;
    }
    void notify_new_decision_level() override { num_new_level_notifications++; }
    void notify_backtrack(size_t) override { num_backtrack_notifications++; }
    bool cb_check_found_model(const vector<Lit>&) override {
        num_model_checks++;
        return true;
    }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }
};

// Rebuilds the trail from notifications alone and compares it, at every point
// where the two are required to agree, with what the solver actually has.
// This is the whole of the notification contract in one object.
class MirrorPropagator : public ExternalPropagator
{
public:
    Solver* s = nullptr;
    vector<vector<Lit>> stack;   // stack[i] holds the observed literals of level i
    vector<char> assigned;       // indexed by outer var
    vector<lbool> value_of;      // indexed by outer var, from notifications alone
    uint32_t num_comparisons = 0;
    uint32_t num_backtracks = 0;
    uint32_t max_level_seen = 0;

    void start(Solver* _s, uint32_t nvars) {
        s = _s;
        stack.assign(1, {});
        assigned.assign(nvars, 0);
        value_of.assign(nvars, l_Undef);
    }

    /// The truth value of an outer literal, as the propagator sees it.
    lbool val(const Lit l) const {
        const lbool v = value_of[l.var()];
        if (v == l_Undef) return l_Undef;
        return l.sign() ? (v == l_True ? l_False : l_True) : v;
    }

    void notify_assignment(const vector<Lit>& lits) override {
        EXPECT_FALSE(lits.empty());
        for(const Lit l: lits) {
            EXPECT_TRUE(s->is_observed_var(l.var()))
                << "notified about unobserved var " << l.var()+1;
            EXPECT_FALSE(assigned[l.var()])
                << "var " << l.var()+1 << " assigned twice without a backtrack";
            assigned[l.var()] = 1;
            value_of[l.var()] = l.sign() ? l_False : l_True;
            stack.back().push_back(l);
        }
    }

    void notify_new_decision_level() override {
        stack.push_back({});
        max_level_seen = std::max<uint32_t>(max_level_seen, stack.size()-1);
        compare();
    }

    void notify_backtrack(size_t new_level) override {
        // must always pop at least one level
        ASSERT_LT(new_level + 1, stack.size());
        for(size_t i = new_level+1; i < stack.size(); i++) {
            for(const Lit l: stack[i]) {
                assigned[l.var()] = 0;
                value_of[l.var()] = l_Undef;
            }
        }
        stack.resize(new_level + 1);
        num_backtracks++;
        compare();
    }

    bool cb_check_found_model(const vector<Lit>&) override { compare(); return true; }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }

    void compare() {
        vector<vector<Lit>> expected;
        // false: notifications are still owed, the two are allowed to differ
        if (!s->ext_get_observed_trail(expected)) return;
        num_comparisons++;

        vector<vector<Lit>> mine = stack;
        // the order within the root prefix carries no meaning
        std::sort(mine[0].begin(), mine[0].end());
        ASSERT_EQ(mine, expected);
    }
};

// Holds a set of clauses and hands them to the solver during the search, one
// at a time, instead of adding them up front. The answer must not change.
// Inherits the mirror's checks, so the notification contract is still tested
// while clauses are being woven into the trail.
class OraclePropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> to_hand_over;   // OUTER numbering
    bool forgettable = false;
    size_t next_clause = 0;
    size_t next_lit = 0;
    size_t num_handed_over = 0;

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = forgettable;
        return next_clause < to_hand_over.size();
    }

    Lit cb_add_external_clause_lit() override {
        assert(next_clause < to_hand_over.size());
        const vector<Lit>& cl = to_hand_over[next_clause];
        if (next_lit == cl.size()) {
            next_lit = 0;
            next_clause++;
            num_handed_over++;
            return lit_Undef;
        }
        return cl[next_lit++];
    }
};

// Owns a set of clauses that the solver never sees, and acts as a complete
// unit propagation engine over them: cb_propagate() hands back an implied
// literal and cb_add_reason_clause_lit() explains it. Reasoning is done purely
// over the trail the mirror has reconstructed from notifications.
class UnitPropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> theory;      // OUTER numbering
    // The clause that implied each literal, recorded when the propagation is
    // made rather than when it is asked about: with lazy reasons the question
    // comes much later, during conflict analysis.
    vector<size_t> reason_for_lit;   // indexed by Lit::toInt()
    size_t cur_clause = 0;
    size_t cur_lit = 0;
    size_t num_propagations = 0;
    size_t num_explanations = 0;

    void start_theory(Solver* _s, uint32_t nvars) {
        start(_s, nvars);
        reason_for_lit.assign(2*nvars, 0);
    }

    Lit cb_propagate() override {
        for(size_t i = 0; i < theory.size(); i++) {
            Lit implied = lit_Undef;
            bool satisfied = false;
            uint32_t num_free = 0;
            for(const Lit l: theory[i]) {
                const lbool v = val(l);
                if (v == l_True) { satisfied = true; break; }
                if (v == l_Undef) { num_free++; implied = l; }
            }
            if (satisfied) continue;
            // Unit, or already falsified: in the latter case hand back one of
            // its literals -- the solver will see the clause is conflicting.
            if (num_free == 1 || num_free == 0) {
                const Lit ret = (num_free == 1) ? implied : theory[i][0];
                reason_for_lit[ret.toInt()] = i;
                num_propagations++;
                return ret;
            }
        }
        return lit_Undef;
    }

    Lit cb_add_reason_clause_lit(Lit propagated_lit) override {
        if (cur_lit == 0) {
            cur_clause = reason_for_lit[propagated_lit.toInt()];
            num_explanations++;
        }
        const vector<Lit>& cl = theory[cur_clause];
        if (cur_lit == cl.size()) { cur_lit = 0; return lit_Undef; }
        return cl[cur_lit++];
    }
};

// Overrides the solver's branching completely: always decides the lowest
// unassigned observed variable, with a fixed polarity.
class DecidingPropagator : public MirrorPropagator
{
public:
    uint32_t nvars = 0;
    bool sign = false;
    uint32_t num_decisions = 0;
    bool check_is_decision = false;

    Lit cb_decide() override {
        for(uint32_t v = 0; v < nvars; v++) {
            if (val(Lit(v, false)) != l_Undef) continue;
            num_decisions++;
            return Lit(v, sign);
        }
        return lit_Undef;
    }

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        if (check_is_decision) {
            // Every literal we decided is reported as a decision; propagated
            // ones are not.
            for(const Lit l: model) {
                if (s->ext_is_decision(l)) { EXPECT_EQ(l.sign(), sign); }
            }
        }
        return true;
    }
};

// Enumerates models: rejects each complete assignment and blocks it with its
// own negation, until the problem becomes unsatisfiable.
class EnumeratingPropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> models;      // one literal per observed var
    vector<vector<Lit>> blocking;
    size_t next_clause = 0;
    size_t next_lit = 0;

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        models.push_back(model);
        vector<Lit> block;
        block.reserve(model.size());
        for(const Lit l: model) block.push_back(~l);
        blocking.push_back(block);
        return false;
    }

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return next_clause < blocking.size();
    }

    Lit cb_add_external_clause_lit() override {
        const vector<Lit>& cl = blocking[next_clause];
        if (next_lit == cl.size()) { next_lit = 0; next_clause++; return lit_Undef; }
        return cl[next_lit++];
    }
};

// Everything at once, driven by a deterministic pseudo-random stream: observes
// variables late, propagates sometimes, hands over clauses sometimes, forces
// backtracking sometimes, and rejects any model that violates the theory it
// holds. The answer must still be the one you get by simply adding all the
// clauses up front.
class AdversarialPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    vector<vector<Lit>> theory;      // sound clauses the solver never sees
    vector<size_t> reason_for_lit;   // indexed by Lit::toInt()
    vector<size_t> queued;           // theory clauses waiting to be handed over
    size_t cur_clause = 0;
    size_t cur_lit = 0;
    uint32_t backtrack_budget = 0;
    uint64_t rnd_state = 1;
    size_t num_propagations = 0;
    size_t num_clauses_given = 0;
    size_t num_forced_backtracks = 0;
    size_t num_late_observes = 0;
    size_t num_rejected_models = 0;

    uint32_t next() {
        rnd_state = rnd_state * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(rnd_state >> 33);
    }
    bool chance(uint32_t percent) { return (next() % 100) < percent; }

    void start_adversary(Solver* _s, uint32_t nvars, uint32_t seed) {
        raw = _s;
        start(_s, nvars);
        reason_for_lit.assign(2*nvars, 0);
        rnd_state = seed * 2862933555777941757ULL + 3037000493ULL;
    }

    bool all_observed(const vector<Lit>& cl) const {
        for(const Lit l: cl) if (!raw->is_observed_var(l.var())) return false;
        return true;
    }

    // Satisfied / falsified / unit under the propagator's own view.
    bool is_satisfied(const vector<Lit>& cl) const {
        for(const Lit l: cl) if (val(l) == l_True) return true;
        return false;
    }

    Lit cb_propagate() override {
        if (!chance(60)) return lit_Undef;
        for(size_t i = 0; i < theory.size(); i++) {
            if (!all_observed(theory[i])) continue;
            Lit implied = lit_Undef;
            bool satisfied = false;
            uint32_t num_free = 0;
            for(const Lit l: theory[i]) {
                const lbool v = val(l);
                if (v == l_True) { satisfied = true; break; }
                if (v == l_Undef) { num_free++; implied = l; }
            }
            if (satisfied || num_free > 1) continue;
            const Lit ret = (num_free == 1) ? implied : theory[i][0];
            reason_for_lit[ret.toInt()] = i;
            num_propagations++;
            return ret;
        }
        return lit_Undef;
    }

    Lit cb_add_reason_clause_lit(Lit propagated_lit) override {
        if (cur_lit == 0) cur_clause = reason_for_lit[propagated_lit.toInt()];
        const vector<Lit>& cl = theory[cur_clause];
        if (cur_lit == cl.size()) { cur_lit = 0; return lit_Undef; }
        return cl[cur_lit++];
    }

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = chance(50);
        if (!queued.empty()) return true;
        // occasionally volunteer a clause nobody asked for
        if (!chance(10)) return false;
        for(uint32_t tries = 0; tries < 4; tries++) {
            const size_t i = next() % theory.size();
            if (all_observed(theory[i])) { queued.push_back(i); return true; }
        }
        return false;
    }

    Lit cb_add_external_clause_lit() override {
        const vector<Lit>& cl = theory[queued.front()];
        if (cur_lit == cl.size()) {
            cur_lit = 0;
            queued.erase(queued.begin());
            num_clauses_given++;
            return lit_Undef;
        }
        return cl[cur_lit++];
    }

    Lit cb_decide() override {
        if (backtrack_budget > 0 && stack.size() > 3 && chance(20)) {
            backtrack_budget--;
            num_forced_backtracks++;
            raw->ext_force_backtrack((uint32_t)(next() % (stack.size()-1)));
        }
        return lit_Undef;
    }

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        (void)model;

        // The whole theory has to be expressible before it can be checked, so
        // observe whatever is still missing. That backtracks, and the solver
        // notices and carries on searching.
        bool observed_something = false;
        for(const auto& cl: theory) {
            for(const Lit l: cl) {
                if (!raw->is_observed_var(l.var())) {
                    raw->add_observed_var(l.var());
                    num_late_observes++;
                    observed_something = true;
                }
            }
        }
        if (observed_something) return false;

        for(size_t i = 0; i < theory.size(); i++) {
            if (is_satisfied(theory[i])) continue;
            queued.push_back(i);
            num_rejected_models++;
            return false;
        }
        return true;
    }
};

// Forces the solver back to the root every time the trail gets deep, a fixed
// number of times, and then gets out of the way.
class BacktrackingPropagator : public MirrorPropagator
{
public:
    SATSolver* api = nullptr;
    Solver* raw = nullptr;
    uint32_t budget = 0;
    uint32_t num_forced = 0;

    Lit cb_decide() override {
        if (budget > 0 && stack.size() > 4) {
            budget--;
            num_forced++;
            raw->ext_force_backtrack(1);
        }
        return lit_Undef;
    }
};

}

TEST(user_prop_connect, connect_and_disconnect)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2"));
    s.add_clause(str_to_cl("-1, 3"));

    s.connect_external_propagator(&p);
    EXPECT_EQ(s.solve(), l_True);
    s.disconnect_external_propagator();

    // and the solver is still usable afterwards
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_connect, no_propagator_no_change)
{
    // The exact same problem with and without a no-op propagator must give the
    // same answer.
    for(int with_prop = 0; with_prop < 2; with_prop++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(5);
        s.add_clause(str_to_cl("1, 2, 3"));
        s.add_clause(str_to_cl("-1, -2"));
        s.add_clause(str_to_cl("-2, -3"));
        s.add_clause(str_to_cl("-1, -3"));
        if (with_prop) s.connect_external_propagator(&p);
        EXPECT_EQ(s.solve(), l_True);
    }
}

TEST(user_prop_observe, observe_and_unobserve)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(6);
    s.connect_external_propagator(&p);

    EXPECT_FALSE(s.is_observed_var(0));
    s.add_observed_var(0);
    s.add_observed_var(3);
    EXPECT_TRUE(s.is_observed_var(0));
    EXPECT_TRUE(s.is_observed_var(3));
    EXPECT_FALSE(s.is_observed_var(1));

    // observing twice is idempotent
    s.add_observed_var(0);
    EXPECT_TRUE(s.is_observed_var(0));

    s.remove_observed_var(0);
    EXPECT_FALSE(s.is_observed_var(0));
    EXPECT_TRUE(s.is_observed_var(3));

    s.reset_observed_vars();
    EXPECT_FALSE(s.is_observed_var(3));
}

TEST(user_prop_observe, disconnect_resets_observed)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(6);
    s.connect_external_propagator(&p);
    s.add_observed_var(2);
    EXPECT_TRUE(s.is_observed_var(2));

    s.disconnect_external_propagator();
    EXPECT_FALSE(s.is_observed_var(2));
}

TEST(user_prop_observe, observe_var_added_after_connect)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(2);
    s.connect_external_propagator(&p);
    s.new_vars(3);
    s.add_observed_var(4);
    EXPECT_TRUE(s.is_observed_var(4));
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_phase, forced_phase_shows_in_model)
{
    // With no constraints at all, every variable is decided, so a forced phase
    // fully determines the model.
    for(int polarity = 0; polarity < 2; polarity++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(8);
        s.connect_external_propagator(&p);
        for(uint32_t i = 0; i < 8; i++) s.phase(Lit(i, polarity == 0));

        EXPECT_EQ(s.solve(), l_True);
        const auto& model = s.get_model();
        for(uint32_t i = 0; i < 8; i++) {
            EXPECT_EQ(model[i], polarity == 0 ? l_False : l_True);
        }
    }
}

TEST(user_prop_phase, unphase_gives_control_back)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(4);
    s.connect_external_propagator(&p);
    s.phase(Lit(0, false));
    s.unphase(0);
    // Nothing to assert about the polarity now, but it must still solve.
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_is_decision, unassigned_is_not_a_decision)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(3);
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    EXPECT_FALSE(s.is_decision(Lit(0, false)));
}

TEST(user_prop_is_decision, root_level_unit_is_not_a_decision)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(3);
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    s.add_clause(str_to_cl("1"));
    EXPECT_EQ(s.solve(), l_True);
    EXPECT_FALSE(s.is_decision(Lit(0, false)));
}

////////////////////////////
// WP1: observed variables are frozen
////////////////////////////

TEST(user_prop_freeze, observed_var_survives_bve)
{
    // Variable 3 occurs only in the two clauses below, so BVE would resolve it
    // away. Observing it must keep it.
    for(int observe = 0; observe < 2; observe++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(10);
        s.connect_external_propagator(&p);
        if (observe) s.add_observed_var(2);

        s.add_clause(str_to_cl("1, 3"));
        s.add_clause(str_to_cl("2, -3"));
        s.add_clause(str_to_cl("4, 5"));
        s.add_clause(str_to_cl("-4, 6"));
        std::string strategy = "occ-bve";
        EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);

        if (observe) { EXPECT_FALSE(s.removed_var(2)); }
        else { EXPECT_TRUE(s.removed_var(2)); }
    }
}

TEST(user_prop_freeze, observed_var_not_replaced)
{
    // 1 <-> 2, so SCC-based equivalent literal replacement would merge them,
    // and one of the two would stop existing in the search.
    for(int observe = 0; observe < 2; observe++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(6);
        s.connect_external_propagator(&p);
        if (observe) {
            s.add_observed_var(0);
            s.add_observed_var(1);
        }

        s.add_clause(str_to_cl("1, -2"));
        s.add_clause(str_to_cl("-1, 2"));
        s.add_clause(str_to_cl("1, 3, 4"));
        s.add_clause(str_to_cl("-3, 5"));
        std::string strategy = "must-scc-vrepl";
        EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);

        const bool merged = s.removed_var(0) || s.removed_var(1);
        EXPECT_EQ(merged, observe == 0);
    }
}

TEST(user_prop_freeze, eliminated_var_is_uneliminated_when_observed)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(10);
    s.add_clause(str_to_cl("1, 3"));
    s.add_clause(str_to_cl("2, -3"));
    s.add_clause(str_to_cl("4, 5"));
    std::string strategy = "occ-bve";
    EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);
    ASSERT_TRUE(s.removed_var(2));

    s.connect_external_propagator(&p);
    s.add_observed_var(2);
    EXPECT_FALSE(s.removed_var(2));
    EXPECT_TRUE(s.is_observed_var(2));
    EXPECT_EQ(s.solve(), l_True);
}

// A random-ish 3-SAT instance, deterministic across runs.
static void add_random_3sat(Solver* s, uint32_t nvars, uint32_t ncls, uint32_t seed)
{
    uint64_t st = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    auto next = [&st]() {
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(st >> 33);
    };
    s->new_vars(nvars);
    for(uint32_t i = 0; i < ncls; i++) {
        vector<Lit> cl;
        while(cl.size() < 3) {
            const uint32_t v = next() % nvars;
            bool dup = false;
            for(const Lit l: cl) if (l.var() == v) dup = true;
            if (!dup) cl.push_back(Lit(v, next() & 1));
        }
        s->add_clause_outside(cl);
        if (!s->okay()) return;
    }
}

namespace CMSat {

struct UserPropFreezeTest : public ::testing::Test {
    UserPropFreezeTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropFreezeTest() { delete s; }

    SolverConf conf;
    Solver* s = nullptr;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropFreezeTest, no_chrono_backtracking_with_propagator)
{
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    add_random_3sat(s, 120, 520, 42);
    must_inter.store(false, std::memory_order_relaxed);
    s->solve_with_assumptions();
    EXPECT_EQ(s->chrono_backtrack, 0U);
    EXPECT_GT(s->non_chrono_backtrack, 0U);
}

TEST_F(UserPropFreezeTest, no_gauss_jordan_matrices_with_propagator)
{
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->conf.doFindXors = true;
    s->connect_external_propagator(&p);
    s->new_vars(30);
    // A set of XORs over the same variables: normally a Gauss-Jordan matrix.
    for(uint32_t i = 0; i + 3 < 24; i += 2) {
        vector<uint32_t> vars = {i, i+1, i+2, i+3};
        s->add_xor_clause_outside(vars, (i/2) % 2 == 0);
    }
    s->solve_with_assumptions();
    EXPECT_TRUE(s->gmatrices.empty());
}

}

////////////////////////////
// WP2: trail notifications
////////////////////////////

namespace CMSat {

struct UserPropNotifyTest : public ::testing::Test {
    UserPropNotifyTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropNotifyTest() { delete s; }

    // Observe every third variable, mirror the trail, and check it at every
    // point where the propagator and the solver must agree.
    void run_mirror(uint32_t nvars, uint32_t ncls, uint32_t seed, uint32_t observe_every)
    {
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        add_random_3sat(s, nvars, ncls, seed);
        for(uint32_t v = 0; v < nvars; v += observe_every) s->add_observed_var(v);
        p.start(s, nvars);

        // solve_with_assumptions() raises the interrupt flag on the way out
        must_inter.store(false, std::memory_order_relaxed);
        const lbool ret = s->solve_with_assumptions();
        EXPECT_NE(ret, l_Undef);
        EXPECT_GT(p.num_comparisons, 0U) << "the mirror never got to compare anything";
        delete s;
        s = nullptr;
    }

    SolverConf conf;
    Solver* s = nullptr;
    MirrorPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropNotifyTest, mirror_small_sat)
{
    run_mirror(40, 130, 7, 3);
    EXPECT_GT(p.max_level_seen, 0U);
}

TEST_F(UserPropNotifyTest, mirror_larger_with_inprocessing)
{
    // Big enough to trigger restarts, clause cleaning, simplification and
    // renumbering -- all of which move the trail around behind the propagator.
    run_mirror(200, 860, 11, 2);
    EXPECT_GT(p.num_backtracks, 0U);
}

TEST_F(UserPropNotifyTest, mirror_unsat)
{
    run_mirror(30, 220, 23, 1);
}

TEST_F(UserPropNotifyTest, mirror_all_observed)
{
    run_mirror(120, 500, 5, 1);
}

TEST_F(UserPropNotifyTest, mirror_seeds)
{
    for(uint32_t seed = 1; seed <= 12; seed++) {
        run_mirror(60, 240, seed, 2);
    }
}

TEST_F(UserPropNotifyTest, mirror_survives_incremental_solving)
{
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    add_random_3sat(s, 60, 150, 3);
    for(uint32_t v = 0; v < 60; v += 2) s->add_observed_var(v);
    p.start(s, 60);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    const uint32_t after_first = p.num_comparisons;
    EXPECT_GT(after_first, 0U);

    // Solve again: the propagator keeps its level-0 view across the calls.
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, after_first);
}

TEST_F(UserPropNotifyTest, observing_an_already_fixed_variable)
{
    // The units are on the trail before the variables become observed, so the
    // notification cursor has to hand them over exactly once.
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(8);
    s->add_clause_outside(str_to_cl("1"));
    s->add_clause_outside(str_to_cl("-2"));
    s->add_clause_outside(str_to_cl("3, 4"));
    for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);
    p.start(s, 8);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, 0U);
}

TEST_F(UserPropNotifyTest, observing_a_fixed_variable_after_a_solve)
{
    // By now renumbering has wiped the literals of the level-0 trail, so the
    // cursor cannot see this assignment at all and it has to be handed over
    // separately.
    s = new Solver(&conf, &must_inter);
    s->conf.simplify_at_startup = true;
    s->conf.full_simplify_at_startup = true;
    s->connect_external_propagator(&p);
    add_random_3sat(s, 60, 150, 3);
    s->add_clause_outside(str_to_cl("1"));
    p.start(s, 60);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);

    s->add_observed_var(0);
    for(uint32_t v = 1; v < 60; v += 3) s->add_observed_var(v);
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, 0U);
}

TEST_F(UserPropNotifyTest, no_notifications_from_inprocessing)
{
    // Everything observed, heavy simplification: any assignment leaking out of
    // probing or distillation would break the mirror.
    s = new Solver(&conf, &must_inter);
    s->conf.simplify_at_startup = true;
    s->conf.full_simplify_at_startup = true;
    s->connect_external_propagator(&p);
    add_random_3sat(s, 150, 620, 31);
    for(uint32_t v = 0; v < 150; v++) s->add_observed_var(v);
    p.start(s, 150);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_NE(s->solve_with_assumptions(), l_Undef);
    EXPECT_GT(p.num_comparisons, 0U);
}

}

////////////////////////////
// WP3: external clause addition during the search
////////////////////////////

namespace CMSat {

// Deterministic random 3-SAT as a plain list of clauses in OUTER numbering.
static vector<vector<Lit>> gen_3sat(uint32_t nvars, uint32_t ncls, uint32_t seed)
{
    uint64_t st = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    auto next = [&st]() {
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(st >> 33);
    };
    vector<vector<Lit>> out;
    for(uint32_t i = 0; i < ncls; i++) {
        vector<Lit> cl;
        while(cl.size() < 3) {
            const uint32_t v = next() % nvars;
            bool dup = false;
            for(const Lit l: cl) if (l.var() == v) dup = true;
            if (!dup) cl.push_back(Lit(v, next() & 1));
        }
        out.push_back(cl);
    }
    return out;
}

static bool model_satisfies(const vector<lbool>& model, const vector<vector<Lit>>& cls)
{
    for(const auto& cl: cls) {
        bool sat = false;
        for(const Lit l: cl) {
            if (l.var() >= model.size()) return false;
            if (model[l.var()] == (l.sign() ? l_False : l_True)) { sat = true; break; }
        }
        if (!sat) return false;
    }
    return true;
}

struct UserPropClauseTest : public ::testing::Test {
    UserPropClauseTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropClauseTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) {
            vector<Lit> tmp = cl;
            ref->add_clause_outside(tmp);
        }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    // 'split' clauses go in up front, the rest arrive through the propagator.
    lbool solve_split(const vector<vector<Lit>>& cls, uint32_t nvars, size_t split) {
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        for(size_t i = split; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
        p.start(s, nvars);

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    OraclePropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropClauseTest, same_answer_as_adding_up_front_sat)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_True);

    ASSERT_EQ(solve_split(cls, nvars, 140), l_True);
    EXPECT_EQ(p.num_handed_over, cls.size() - 140);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropClauseTest, same_answer_as_adding_up_front_unsat)
{
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);
    ASSERT_EQ(solve_split(cls, nvars, 90), l_False);
}

TEST_F(UserPropClauseTest, forgettable_clauses_give_the_same_answer)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    p.forgettable = true;
    ASSERT_EQ(solve_split(cls, nvars, 140), l_True);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropClauseTest, everything_through_the_propagator)
{
    const uint32_t nvars = 40;
    auto cls = gen_3sat(nvars, 120, 3);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_split(cls, nvars, 0), expected);
    if (expected == l_True) { EXPECT_TRUE(model_satisfies(s->get_model(), cls)); }
}

TEST_F(UserPropClauseTest, many_seeds)
{
    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);
        ASSERT_EQ(solve_split(cls, nvars, cls.size()/2), expected) << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
        delete s; s = nullptr;
        delete ref; ref = nullptr;
        p = OraclePropagator();
    }
}

TEST_F(UserPropClauseTest, unit_and_empty_clauses_from_the_propagator)
{
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(8);
    s->add_clause_outside(str_to_cl("1, 2"));
    s->add_clause_outside(str_to_cl("-1, 3"));
    for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);

    // 1, then -1: the second makes the problem unsatisfiable
    p.to_hand_over.push_back(str_to_cl("1"));
    p.to_hand_over.push_back(str_to_cl("-1"));
    p.start(s, 8);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_FALSE(s->okay());
}

TEST_F(UserPropClauseTest, frat_proof_is_written_without_tripping_anything)
{
    // Full checking of the emitted proof needs the frat-xor / cake_xlrup
    // toolchain (see README_VERIFIER.md); what is checked here is that the
    // FRAT path runs, produces output, and still gives the right answer.
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);

    const char* fname = "user_prop_test.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 90; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    for(size_t i = 90; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    delete s; s = nullptr;
    fclose(f);

    FILE* check = fopen(fname, "rb");
    ASSERT_NE(check, nullptr);
    fseek(check, 0, SEEK_END);
    EXPECT_GT(ftell(check), 0);
    fclose(check);
    std::remove(fname);
}

TEST_F(UserPropClauseTest, forgettable_is_ignored_under_frat)
{
    // A redundant input clause cannot be represented in the proof, so a
    // forgettable clause is simply kept. Answer must not change.
    const uint32_t nvars = 30;
    auto cls = gen_3sat(nvars, 125, 4);
    const lbool expected = solve_plain(cls, nvars);

    const char* fname = "user_prop_test_forget.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 60; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    p.forgettable = true;
    for(size_t i = 60; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), expected);
    delete s; s = nullptr;
    fclose(f);
    std::remove(fname);
}

TEST_F(UserPropClauseTest, propagator_forces_a_specific_model)
{
    // Pin every variable with a unit clause handed over during the search.
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(12);
    s->add_clause_outside(str_to_cl("1, 2, 3"));
    for(uint32_t v = 0; v < 12; v++) {
        s->add_observed_var(v);
        p.to_hand_over.push_back(vector<Lit>{Lit(v, v % 2 == 0)});
    }
    p.start(s, 12);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    for(uint32_t v = 0; v < 12; v++) {
        EXPECT_EQ(s->get_model()[v], v % 2 == 0 ? l_False : l_True) << "var " << v+1;
    }
}

}

////////////////////////////
// WP4: external propagation with eager reason clauses
////////////////////////////

namespace CMSat {

struct UserPropPropagateTest : public ::testing::Test {
    UserPropPropagateTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropPropagateTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) {
            vector<Lit> tmp = cl;
            ref->add_clause_outside(tmp);
        }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    // The first 'split' clauses go to the solver; the rest exist only inside
    // the propagator, which propagates over them and explains itself.
    lbool solve_with_theory(const vector<vector<Lit>>& cls, uint32_t nvars, size_t split,
                            bool lazy_reasons = false) {
        delete s;
        conf.ext_lazy_reasons = lazy_reasons;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        p.theory.clear();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_theory(s, nvars);

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    UnitPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropPropagateTest, theory_propagation_matches_plain_solving_sat)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    ASSERT_EQ(solve_plain(cls, nvars), l_True);
    ASSERT_EQ(solve_with_theory(cls, nvars, 140), l_True);
    EXPECT_GT(p.num_propagations, 0U);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropPropagateTest, theory_propagation_matches_plain_solving_unsat)
{
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    ASSERT_EQ(solve_plain(cls, nvars), l_False);
    ASSERT_EQ(solve_with_theory(cls, nvars, 90), l_False);
    EXPECT_GT(p.num_propagations, 0U);
}

TEST_F(UserPropPropagateTest, whole_problem_in_the_propagator)
{
    // The solver gets no clauses at all: every implication and every conflict
    // comes out of the propagator, through reason clauses only.
    const uint32_t nvars = 25;
    auto cls = gen_3sat(nvars, 100, 9);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_with_theory(cls, nvars, 0), expected);
    if (expected == l_True) { EXPECT_TRUE(model_satisfies(s->get_model(), cls)); }
}

TEST_F(UserPropPropagateTest, many_seeds)
{
    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);
        ASSERT_EQ(solve_with_theory(cls, nvars, cls.size()/2), expected)
            << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
        p = UnitPropagator();
    }
}

TEST_F(UserPropPropagateTest, forgettable_reason_clauses)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    p.are_reasons_forgettable = true;
    ASSERT_EQ(solve_with_theory(cls, nvars, 140), l_True);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropPropagateTest, lazy_propagator_is_never_asked)
{
    const uint32_t nvars = 40;
    auto cls = gen_3sat(nvars, 120, 3);
    p.is_lazy = true;
    solve_with_theory(cls, nvars, cls.size());   // nothing left for the theory
    EXPECT_EQ(p.num_propagations, 0U);
}

}

////////////////////////////
// WP5: decisions, forced backtracking and solution analysis
////////////////////////////

namespace CMSat {

// Brute-force model count over 'nvars' variables.
static uint32_t count_models(const vector<vector<Lit>>& cls, uint32_t nvars)
{
    uint32_t count = 0;
    for(uint32_t mask = 0; mask < (1U << nvars); mask++) {
        bool all_sat = true;
        for(const auto& cl: cls) {
            bool sat = false;
            for(const Lit l: cl) {
                const bool v = (mask >> l.var()) & 1;
                if (v != l.sign()) { sat = true; break; }
            }
            if (!sat) { all_sat = false; break; }
        }
        if (all_sat) count++;
    }
    return count;
}

struct UserPropDecideTest : public ::testing::Test {
    UserPropDecideTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropDecideTest() { delete s; }

    SolverConf conf;
    Solver* s = nullptr;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropDecideTest, cb_decide_drives_the_search)
{
    for(int sign = 0; sign < 2; sign++) {
        DecidingPropagator p;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(8);
        for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);
        p.nvars = 8;
        p.sign = (sign == 1);
        p.check_is_decision = true;
        p.start(s, 8);

        must_inter.store(false, std::memory_order_relaxed);
        ASSERT_EQ(s->solve_with_assumptions(), l_True);
        EXPECT_EQ(p.num_decisions, 8U);
        for(uint32_t v = 0; v < 8; v++) {
            EXPECT_EQ(s->get_model()[v], sign == 1 ? l_False : l_True) << "var " << v+1;
        }
        delete s; s = nullptr;
    }
}

TEST_F(UserPropDecideTest, cb_decide_is_ignored_for_assigned_literals)
{
    // The propagator keeps asking for variable 1, which unit propagation has
    // already fixed; the solver must fall back on its own heuristic.
    class Stubborn : public DecidingPropagator {
    public:
        Lit cb_decide() override { num_decisions++; return Lit(0, false); }
    } p;

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(6);
    s->add_clause_outside(str_to_cl("1"));
    for(uint32_t v = 0; v < 6; v++) s->add_observed_var(v);
    p.nvars = 6;
    p.start(s, 6);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_decisions, 0U);
    EXPECT_EQ(s->get_model()[0], l_True);
}

TEST_F(UserPropDecideTest, model_enumeration_through_cb_check_found_model)
{
    const uint32_t nvars = 8;
    auto cls = gen_3sat(nvars, 10, 21);
    const uint32_t expected = count_models(cls, nvars);
    ASSERT_GT(expected, 0U);

    EnumeratingPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(const auto& cl: cls) { vector<Lit> tmp = cl; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    // Every model is rejected and blocked, so the search ends unsatisfiable.
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_EQ(p.models.size(), expected);

    // and no model was enumerated twice
    vector<vector<Lit>> seen = p.models;
    std::sort(seen.begin(), seen.end());
    EXPECT_EQ(std::unique(seen.begin(), seen.end()), seen.end());
}

TEST_F(UserPropDecideTest, rejecting_without_a_clause_is_taken_as_acceptance)
{
    class AlwaysNo : public MirrorPropagator {
    public:
        uint32_t num_rejections = 0;
        bool cb_check_found_model(const vector<Lit>&) override {
            num_rejections++;
            return false;
        }
    } p;

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(5);
    s->add_clause_outside(str_to_cl("1, 2"));
    for(uint32_t v = 0; v < 5; v++) s->add_observed_var(v);
    p.start(s, 5);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_EQ(p.num_rejections, 1U);
}

TEST_F(UserPropDecideTest, force_backtrack_from_cb_decide)
{
    BacktrackingPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(40);
    auto cls = gen_3sat(40, 120, 13);
    for(const auto& cl: cls) { vector<Lit> tmp = cl; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < 40; v++) s->add_observed_var(v);
    p.raw = s;
    p.budget = 25;
    p.start(s, 40);

    must_inter.store(false, std::memory_order_relaxed);
    const lbool ret = s->solve_with_assumptions();
    EXPECT_NE(ret, l_Undef);
    EXPECT_GT(p.num_forced, 0U);
    EXPECT_GT(p.num_backtracks, 0U);
}

TEST_F(UserPropDecideTest, force_backtrack_is_ignored_outside_the_callbacks)
{
    NoopPropagator p;
    SATSolver api;
    api.new_vars(5);
    api.add_clause(str_to_cl("1, 2"));
    api.connect_external_propagator(&p);
    api.add_observed_var(0);
    // Not inside cb_decide()/cb_check_found_model(): must be a no-op, not a crash
    api.force_backtrack(0);
    EXPECT_EQ(api.solve(), l_True);
}

}

////////////////////////////
// WP6: lazy reason clauses
////////////////////////////

namespace CMSat {

struct UserPropLazyTest : public UserPropPropagateTest {};

TEST_F(UserPropLazyTest, lazy_and_eager_agree_over_many_seeds)
{
    size_t eager_explanations = 0;
    size_t eager_propagations = 0;
    size_t lazy_explanations = 0;
    size_t lazy_propagations = 0;

    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);

        for(int lazy = 0; lazy < 2; lazy++) {
            p = UnitPropagator();
            ASSERT_EQ(solve_with_theory(cls, nvars, cls.size()/2, lazy == 1), expected)
                << "seed " << seed << " lazy " << lazy;
            if (expected == l_True) {
                EXPECT_TRUE(model_satisfies(s->get_model(), cls))
                    << "seed " << seed << " lazy " << lazy;
            }
            // an explanation is only ever asked for once per propagation
            EXPECT_LE(p.num_explanations, p.num_propagations);
            if (lazy) {
                lazy_explanations += p.num_explanations;
                lazy_propagations += p.num_propagations;
            } else {
                // eagerly, every propagation is explained straight away
                EXPECT_EQ(p.num_explanations, p.num_propagations);
                eager_explanations += p.num_explanations;
                eager_propagations += p.num_propagations;
            }
        }
    }

    EXPECT_GT(eager_explanations, 0U);
    EXPECT_GT(lazy_propagations, 0U);
    EXPECT_EQ(eager_explanations, eager_propagations);
    // The whole point: most propagations never have to be explained at all.
    EXPECT_LT(lazy_explanations, lazy_propagations);
    EXPECT_LT((double)lazy_explanations/(double)lazy_propagations, 0.9);
}

TEST_F(UserPropLazyTest, lazy_reasons_are_actually_used_in_conflict_analysis)
{
    const uint32_t nvars = 25;
    auto cls = gen_3sat(nvars, 100, 9);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_with_theory(cls, nvars, 0, true), expected);
    // Everything comes from the propagator, so conflict analysis cannot avoid
    // asking for reasons.
    EXPECT_GT(p.num_explanations, 0U);
    EXPECT_LT(p.num_explanations, p.num_propagations);
}

TEST_F(UserPropLazyTest, lazy_is_ignored_under_frat)
{
    // Reason clauses have to be in the proof, so they are asked for eagerly.
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);

    const char* fname = "user_prop_test_lazy.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    conf.ext_lazy_reasons = true;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 90; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    for(size_t i = 90; i < cls.size(); i++) p.theory.push_back(cls[i]);
    p.start_theory(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_EQ(p.num_explanations, p.num_propagations);
    delete s; s = nullptr;
    fclose(f);
    std::remove(fname);
}

TEST_F(UserPropLazyTest, lazy_with_the_whole_problem_in_the_propagator)
{
    for(uint32_t seed = 1; seed <= 8; seed++) {
        const uint32_t nvars = 22;
        auto cls = gen_3sat(nvars, 92, seed);
        const lbool expected = solve_plain(cls, nvars);
        p = UnitPropagator();
        ASSERT_EQ(solve_with_theory(cls, nvars, 0, true), expected) << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
    }
}

}

////////////////////////////
// WP7: everything at once
////////////////////////////

namespace CMSat {

struct UserPropAdversaryTest : public ::testing::Test {
    UserPropAdversaryTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropAdversaryTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) { vector<Lit> tmp = cl; ref->add_clause_outside(tmp); }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    lbool solve_adversarially(const vector<vector<Lit>>& cls, uint32_t nvars,
                              size_t split, uint32_t seed, bool lazy)
    {
        delete s;
        conf.ext_lazy_reasons = lazy;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        // Only some variables are observed to begin with; the propagator asks
        // for the rest while checking a model.
        for(uint32_t v = 0; v < nvars; v++) if ((v + seed) % 3 != 0) s->add_observed_var(v);

        p.theory.clear();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 40;

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    AdversarialPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropAdversaryTest, everything_at_once)
{
    size_t total_forced = 0, total_late = 0, total_rejected = 0, total_given = 0;
    for(uint32_t seed = 1; seed <= 25; seed++) {
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 108, seed);
        const lbool expected = solve_plain(cls, nvars);

        for(int lazy = 0; lazy < 2; lazy++) {
            p = AdversarialPropagator();
            const lbool got = solve_adversarially(cls, nvars, cls.size()*2/3, seed, lazy == 1);
            ASSERT_EQ(got, expected) << "seed " << seed << " lazy " << lazy;
            if (expected == l_True) {
                EXPECT_TRUE(model_satisfies(s->get_model(), cls))
                    << "seed " << seed << " lazy " << lazy;
            }
            total_forced += p.num_forced_backtracks;
            total_late += p.num_late_observes;
            total_rejected += p.num_rejected_models;
            total_given += p.num_clauses_given;
        }
    }
    // make sure the interesting paths were actually taken
    EXPECT_GT(total_forced, 0U);
    EXPECT_GT(total_late, 0U);
    EXPECT_GT(total_given, 0U);
    EXPECT_GT(total_rejected, 0U);
}

TEST_F(UserPropAdversaryTest, everything_at_once_bigger)
{
    for(uint32_t seed = 100; seed <= 106; seed++) {
        const uint32_t nvars = 60;
        auto cls = gen_3sat(nvars, 245, seed);
        const lbool expected = solve_plain(cls, nvars);
        p = AdversarialPropagator();
        ASSERT_EQ(solve_adversarially(cls, nvars, cls.size()/2, seed, seed % 2 == 0), expected)
            << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
    }
}

TEST_F(UserPropAdversaryTest, everything_at_once_under_frat)
{
    for(uint32_t seed = 200; seed <= 204; seed++) {
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 108, seed);
        const lbool expected = solve_plain(cls, nvars);

        const char* fname = "user_prop_adversary.frat";
        FILE* f = fopen(fname, "wb");
        ASSERT_NE(f, nullptr);

        delete s;
        s = new Solver(&conf, &must_inter);
        s->add_frat(f);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        const size_t split = cls.size()*2/3;
        for(size_t i = 0; i < split; i++) { vector<Lit> tmp = cls[i]; s->add_clause_outside(tmp); }
        for(uint32_t v = 0; v < nvars; v++) if ((v + seed) % 3 != 0) s->add_observed_var(v);
        p = AdversarialPropagator();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 40;

        must_inter.store(false, std::memory_order_relaxed);
        EXPECT_EQ(s->solve_with_assumptions(), expected) << "seed " << seed;
        delete s; s = nullptr;
        fclose(f);
        std::remove(fname);
    }
}

TEST_F(UserPropAdversaryTest, everything_at_once_with_assumptions)
{
    for(uint32_t seed = 300; seed <= 308; seed++) {
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 100, seed);

        // A handful of assumptions, the same for both solves.
        vector<Lit> assumps;
        for(uint32_t i = 0; i < 3; i++) assumps.push_back(Lit((seed*7+i) % nvars, (i%2) == 0));

        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) { vector<Lit> tmp = cl; ref->add_clause_outside(tmp); }
        must_inter.store(false, std::memory_order_relaxed);
        const lbool expected = ref->solve_with_assumptions(&assumps);

        delete s;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        const size_t split = cls.size()/2;
        for(size_t i = 0; i < split; i++) { vector<Lit> tmp = cls[i]; s->add_clause_outside(tmp); }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        p = AdversarialPropagator();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 20;

        must_inter.store(false, std::memory_order_relaxed);
        ASSERT_EQ(s->solve_with_assumptions(&assumps), expected) << "seed " << seed;
    }
}

}

int main(int argc, char **argv)
{
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
