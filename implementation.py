import sympy
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Or, And, Not

def pl_resolution(CNF):
    clauses = set(frozenset(c.args) if isinstance(c, Or) else frozenset([c]) for c in CNF)
    new = set()
    while True:
        for ci in clauses:
            for cj in clauses:
                if ci != cj:
                    resolvents = resolve(Or(*ci), Or(*cj))
                    if frozenset() in resolvents:  # Empty clause found
                        return True
                    new.update(resolvents)
        if new <= clauses:
            return False
        clauses.update(new)


def resolve(ci, cj):
    # Convert sympy logical expressions to sets of literals
    ci_set = set(ci.args) if isinstance(ci, Or) else {ci}
    cj_set = set(cj.args) if isinstance(cj, Or) else {cj}
    
    resolvents = set()
    for di in ci_set:
        for dj in cj_set:
            if di == ~dj or ~di == dj:
                # Create new clause without the resolved literals
                new_clause = (ci_set - {di}) | (cj_set - {dj})
                resolvents.add(frozenset(new_clause))
    return resolvents

def handle_contradiction(belief_base_cnf):
    # Sort beliefs by priority (higher priority first)
    belief_base_cnf.sort(key=lambda x: x[1], reverse=True)
    for i in range(len(belief_base_cnf)):
        formula, priority = belief_base_cnf[i]
        # Check for contradiction with the current belief
        if pl_resolution({formula} | {b for b, p in belief_base_cnf if p != priority}):
            # Remove the belief causing the contradiction
            return belief_base_cnf[:i] + belief_base_cnf[i+1:]
    return belief_base_cnf

def expand_belief_base(belief_base_cnf, new_belief, priority):
    new_belief_cnf = to_cnf(new_belief)
    belief_base_cnf.append((new_belief_cnf, priority))
    # Handle potential contradictions after adding the new belief
    return handle_contradiction(belief_base_cnf)


if __name__ == '__main__':
    
    # Define the logical variables
    A, B, C = sympy.symbols('A B C')
    p, q, r, s = sympy.symbols('p q r s')
    # Initial belief base with priorities
    initial_belief_base = [(to_cnf(~p >> q), 1),(to_cnf(q >> p), 2),(to_cnf(p >> r & s), 3)]
    # initial_belief_base = [(to_cnf(A & B), 1), (to_cnf(~B | C), 2), (to_cnf(A >> C), 3)]

    # New belief to add
    #new_belief = A & ~C
    new_belief = p & r & s
    new_priority = 4

    # Expand the belief base with the new belief
    expanded_belief_base = expand_belief_base(initial_belief_base, new_belief, new_priority)
    print("Expanded KB: ",expanded_belief_base)

