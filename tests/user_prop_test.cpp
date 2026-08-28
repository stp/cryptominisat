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

        if (observe) EXPECT_FALSE(s.removed_var(2));
        else EXPECT_TRUE(s.removed_var(2));
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

namespace CMSat {

struct UserPropFreezeTest : public ::testing::Test {
    UserPropFreezeTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropFreezeTest() { delete s; }

    SolverConf conf;
    Solver* s = nullptr;
    std::atomic<bool> must_inter;
};

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

TEST_F(UserPropFreezeTest, no_chrono_backtracking_with_propagator)
{
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    add_random_3sat(s, 120, 520, 42);
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

int main(int argc, char **argv)
{
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
