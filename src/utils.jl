"Check if formula contains a predicate name."
has_pred(formula::Const, pred_names) = formula.name in pred_names
has_pred(formula::Var, pred_names) = false
has_pred(formula::Compound, pred_names) = formula.name in pred_names ||
    any(has_pred(f, pred_names) for f in formula.args)
has_pred(formula::Term, domain::Domain) =
    has_pred(formula, keys(domain.predicates))

"Check if formula contains a numeric fluent."
has_fluent(formula::Term, state::State) =
    has_pred(formula, keys(state.fluents))
has_fluent(formula::Term, domain::Domain) =
    has_pred(formula, keys(domain.functions))

"Check if formula contains an axiom reference."
has_axiom(formula::Term, domain::Domain) = length(domain.axioms) > 0 &&
    has_pred(formula, (ax.head.name for ax in domain.axioms))

"Check if formula contains a universal or existential quantifier."
has_quantifier(formula::Term) =
    has_pred(formula, Set(Symbol[:forall, :exists]))

"Get subscript from State"
get_value(state::State, key::String) = state[key]

"Check if term is in State"
has_term_in_state(domain::Domain, state::State, term::Term) =
    return state[domain, term]

flatten_goal(problem::Problem) = 
    return flatten_conjs(problem.goal)

"Filter out negative preconditions"
function filter_negative_preconds(action_def::Term) 
    conds = get_preconditions(action_def; converter=to_dnf)
    conds = [c.args for c in conds.args]
    for c in conds filter!(t -> t.name != :not, c) end
    return conds
end

"Compute axioms without negative literals"
function compute_hsp_axioms(domain::Domain)
    axioms = regularize_clauses(domain.axioms) # Regularize domain axioms
    axioms = [Clause(ax.head, [t for t in ax.body if t.name != :not])
              for ax in axioms] # Remove negative literals
    domain.axioms = Clause[]
    return domain, axioms
end

"Create state class"
function create_state(types::Set{Term}, facts::Set{Term})
    return State(types, facts)
end

"Compute costs of one-step derivation of domain axioms"
function compute_costs_one_step_derivation(facts::Set{Term}, fact_costs::Dict{Term,Float64}, ax::Clause, heur::String)
    _, subst = resolve(ax.body, [Clause(f, []) for f in facts])
    for s in subst
        body = [substitute(t, s) for t in ax.body]
        if heur == "delete_relaxation/h_add"
            cost = sum([0; [get(fact_costs, f, 0) for f in body]])
        else
            cost = maximum([0; [get(fact_costs, f, 0) for f in body]])
        end
        derived = substitute(ax.head, s)
        if cost < get(fact_costs, derived, Inf)
            fact_costs[derived] = cost end
    end
    return fact_costs
end

"Compute costs of all effects of available actions"
function compute_cost_action_effect(fact_costs::Dict{Term,Float64}, act::Term, domain::Domain, preconds::Dict{Symbol, Vector{Vector{Term}}}, additions::Dict{Symbol, Vector{Term}}, heur::String)
    act_args = domain.actions[act.name].args
    subst = Subst(var => val for (var, val) in zip(act_args, act.args)) 
    # Look-up preconds and substitute vars
    conds = preconds[act.name]
    conds = [[substitute(t, subst) for t in c] for c in conds]
    # Compute cost of reaching each action
    if heur == "delete_relaxation/h_add"
        cost = minimum([[sum([0; [get(fact_costs, f, 0) for f in conj]]) for conj in conds]; Inf])
    else
        cost = minimum([[maximum([0; [get(fact_costs, f, 0) for f in conj]]) for conj in conds]; Inf])
    end
    # Compute cost of reaching each added fact
    added = [substitute(a, subst) for a in additions[act.name]]
    cost = cost + 1 # TODO: Handle arbitrary action costs
    for fact in added
        if cost < get(fact_costs, fact, Inf)
            fact_costs[fact] = cost end
    end
    return fact_costs
end
    
