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

#pragma once

#include <vector>
#include <cstddef>

#include "solvertypesmini.h"

namespace CMSat {

/**
IPASIR-UP: an interface to inspect and influence the CDCL search from outside
the solver. See "Satisfiability Modulo User Propagators", Fazekas, Niemetz,
Preiner, Kirchweger, Szeider & Biere, JAIR 81 (2024) 989-1017.

All literals crossing this interface are in the same numbering as the rest of
the public API (i.e. the numbering used by add_clause() and get_model()), and
all of them must be over *observed* variables, declared through
SATSolver::add_observed_var().

At most one propagator can be connected to a solver. Connecting a propagator
restricts the solver to a single thread and disables Gauss-Jordan elimination,
chronological backtracking and symmetry breaking.

A note on SATSolver::is_decision(): a literal counts as a decision when it is
assigned above the root with no reason, which includes the assumptions of the
current solve call. It is only meaningful while solving -- once solve() has
returned, the solver is back at decision level 0 and nothing is a decision.
*/
class ExternalPropagator
{
public:
    /// A lazy propagator only inspects complete assignments. It is not told
    /// about the trail at all -- none of the notify_* functions below are
    /// called -- and neither are cb_propagate() and cb_decide().
    /// cb_check_found_model() still is, and so is cb_has_external_clause()
    /// whenever a model is rejected: handing over a clause is the only way a
    /// lazy propagator gets to say anything.
    /// Read on every callback, so do not change it while connected.
    bool is_lazy = false;

    /// If true, the solver is allowed to delete the reason clauses handed over
    /// through cb_add_reason_clause_lit() during clause database reduction.
    bool are_reasons_forgettable = false;

    virtual ~ExternalPropagator() = default;

    //////////////////////////////
    // Inspecting the trail
    //
    // The trail is presented as a stack: literals are pushed by
    // notify_assignment() and popped by notify_backtrack(). Notifications are
    // not eager, but the view is always up to date whenever any of the cb_*
    // functions below is called.
    //////////////////////////////

    /// Observed literals that just became true. All literals of one call are
    /// on the same (current) decision level.
    virtual void notify_assignment(const std::vector<Lit>& lits) = 0;

    /// A new decision level has been opened. The decision itself, if it is
    /// over an observed variable, arrives through notify_assignment().
    virtual void notify_new_decision_level() = 0;

    /// The solver backtracked: every assignment made above 'new_level' must
    /// be considered undone. Only ever called with new_level strictly below
    /// the number of decision levels the propagator has been notified about.
    virtual void notify_backtrack(size_t new_level) = 0;

    //////////////////////////////
    // Influencing the search
    //////////////////////////////

    /// A complete assignment was found. 'model' holds one literal per observed
    /// variable, in the same order in which the variables were observed.
    /// Return false to reject it -- the propagator is then expected to hand
    /// over at least one clause through cb_has_external_clause(), or to have
    /// called force_backtrack(). Rejecting without doing either is treated as
    /// acceptance.
    virtual bool cb_check_found_model(const std::vector<Lit>& model) = 0;

    /// The next decision literal, or lit_Undef to let the solver decide.
    /// A literal that is already assigned is ignored.
    ///
    /// This is also the place to call SATSolver::force_backtrack(). The solver
    /// backtracks first and then makes the decision returned here, provided
    /// the literal is unassigned on the backtracked trail and every assumption
    /// is still on it; otherwise the decision is dropped, and cb_decide() is
    /// asked again from the new state.
    virtual Lit cb_decide() { return lit_Undef; }

    /// A literal implied by external knowledge under the current trail, or
    /// lit_Undef if there is nothing to propagate.
    virtual Lit cb_propagate() { return lit_Undef; }

    /// The reason for an earlier cb_propagate() of 'propagated_lit', given one
    /// literal at a time and closed with lit_Undef. The clause must contain
    /// 'propagated_lit' and must be implied by the constraints the propagator
    /// represents. The set of observed variables cannot be changed from inside
    /// this callback: the question is about the trail as it is.
    ///
    /// Every other literal must have been falsified *at the time of the
    /// propagation*, not merely by the time the question is asked. By default
    /// the question comes much later, during conflict analysis (see
    /// SATSolver::set_lazy_external_reasons()), so record the reason when the
    /// propagation is made rather than working it out from the trail on demand
    /// -- by then the solver may have assigned literals that have no business
    /// being in it, and conflict analysis has no way to resolve through them.
    virtual Lit cb_add_reason_clause_lit(Lit propagated_lit) {
        (void)propagated_lit;
        return lit_Undef;
    }

    /// Whether there is a clause to hand over. Set 'is_forgettable' to true to
    /// allow the solver to delete it again during clause database reduction.
    virtual bool cb_has_external_clause(bool& is_forgettable) = 0;

    /// The literals of that clause, one at a time, closed with lit_Undef.
    virtual Lit cb_add_external_clause_lit() = 0;
};

}
