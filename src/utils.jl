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
