import sympy
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Or, And, Not
import itertools

def cnf(belief, newbelief):
    anded_formula = belief[0]
    not_new_belief = sympy.Not(newbelief)

    for formula in belief[1:]: 
        anded_formula = sympy.And(anded_formula,formula)

    full_belief = sympy.And(anded_formula,not_new_belief)

    cnfed_formula = sympy.to_cnf(full_belief)
    return cnfed_formula

def resolution(cnf_expression):
    clauses = set(cnf_expression.args if isinstance(cnf_expression, And) else [cnf_expression])
    original_clauses = clauses.copy()
    new_clauses = True

    while new_clauses:
        new_clauses = set()
        for clause1 in list(clauses):
            for clause2 in list(clauses):
                if clause1 is not clause2:
                    resolvent = resolve(clause1, clause2)
                    if resolvent is False:
                        print(f"Resolving {clause1} and {clause2} yields a contradiction.")
                        return False  # Indicate contradiction found
                    elif resolvent and resolvent not in clauses:
                        new_clauses.add(resolvent)
                        print(f"Resolving {clause1} and {clause2} yields {resolvent}.")

        if new_clauses:
            clauses.update(new_clauses)
        else:
            print("No new resolvents can be derived; resolution complete.")

    if sympy.false in clauses:
        print("The empty clause is derived; contradiction found.")
        return False
    else:
        print("No contradiction found; resolved clauses:")
        for clause in clauses - original_clauses:
            print(clause)
        return clauses  # Return all clauses if no contradiction is found


def resolve(clause1, clause2):
    literals1 = set(clause1.args if isinstance(clause1, Or) else [clause1])
    literals2 = set(clause2.args if isinstance(clause2, Or) else [clause2])

    for lit1 in literals1:
        for lit2 in literals2:
            if lit1 == ~lit2 or ~lit1 == lit2:  # Check for complementary literals
                new_literals = (literals1.union(literals2) - {lit1, lit2})
                if new_literals:
                    return Or(*new_literals)  # Return new clause formed by resolving the pair
                else:
                    return False  # Return False indicating an empty clause (contradiction)
    return None  # Return None if no resolution is possible

def check_implication(beliefs, formula):
    test_formula = sympy.And(*beliefs, sympy.Not(formula))
    contradiction_found = resolution(to_cnf(test_formula)) == False
    return contradiction_found  # True if 'beliefs' imply 'formula'


def find_remainder_sets(belief_base, phi):
    remainders = []
    # Generate all possible non-empty subsets of the belief base
    for r in range(1, len(belief_base) + 1):
        for subset in itertools.combinations(belief_base, r):
            if phi not in subset:  # Optionally check if phi is directly in the subset
                implies_phi = check_implication(subset, phi)
                print(f"Testing subset: {subset}")
                if not implies_phi:
                    print(f"Subset {subset} does NOT imply {phi}, adding to remainders.")
                    remainders.append(subset)
                else:
                    print(f"Subset {subset} implies {phi}, hence not a remainder.")
    print(f"Found {len(remainders)} valid remainder(s).")
    return remainders

def select_remainder_based_on_entrenchment(remainders, entrenchment):
    # Ensuring at least one remainder is selected if available
    max_entrenchment_value = -1
    selected_remainder = None
    for remainder in remainders:
        entrenchment_value = sum(entrenchment.get(belief, 0) for belief in remainder)
        if entrenchment_value > max_entrenchment_value:
            max_entrenchment_value = entrenchment_value
            selected_remainder = remainder
    return selected_remainder or []  # Return an empty list if no remainders are selected

# Update the contraction function to handle cases where no remainder is selected
def contract(belief_base, phi, entrenchment):
    remainders = find_remainder_sets(belief_base, phi)
    selected_remainder = select_remainder_based_on_entrenchment(remainders, entrenchment)
    return selected_remainder if selected_remainder is not None else belief_base

def expand_belief_base(belief_base, new_belief, entrenchment):
    """
    Expands the belief base by optionally contracting with the negation of the new belief
    and then adding the new belief to ensure consistency.
    """
    # Contract the belief base with the negation of the new belief to resolve potential inconsistencies
    negated_new_belief = sympy.Not(new_belief)
    contracted_base = contract(belief_base, negated_new_belief, entrenchment)
    
    contracted_base = list(contracted_base) 
    # Now add the new belief to the contracted belief base
    expanded_base = contracted_base + [new_belief]
    return expanded_base


if __name__ == '__main__':

    p, q, r, s = sympy.symbols('p q r s')
    #initial_belief = [(~p >> q),(q >> p),(p >> (r & s))]
    #new_belief = p & r & s

    #initial_belief = [~r >> q, ~q]
    #new_belief = r
    # Example belief base and entrenchment levels

    # initial_belief = [(~p | ~q | r), (q | r), (p | r)]
    # entrenchment = {
    #     (~p | ~q | r): 1,
    #     (q | r): 2,
    #     (p | r): 3 
    # }

    # initial_belief = [p,q,r]
    # entrenchment = {
    #     p&q: 1,
    #     ~p|~q: 2
    # }
    # new_belief = r
    # full_cnf = cnf(initial_belief, new_belief)

    # #phi_to_contract = ~p
    # phi_to_add = p
    # new_belief_base = expand_belief_base(initial_belief, phi_to_add, entrenchment)
    # print("Expanded Belief Base:", new_belief_base)
    
    initial_belief = [p, p&q, r]  # Example belief base
    entrenchment = {
        p: 3,
        p&q: 2,
        r: 1
    }

    # Logical equivalents
    phi = p
    psi = Not(Not(p))  # Equivalent to p

    contracted_with_phi = contract(initial_belief, phi, entrenchment)
    contracted_with_psi = contract(initial_belief, psi, entrenchment)

    print("Contracted with phi (p):", contracted_with_phi)
    print("Contracted with psi (~~p):", contracted_with_psi)
    print("Are the contracted bases equivalent?", contracted_with_phi == contracted_with_psi)

    #contracted_belief_base = contract(initial_belief, phi_to_contract, entrenchment)
    #print("Contracted Belief Base:", contracted_belief_base)
    
    # print("FULL CNF; ", full_cnf)
    # print(resolution(full_cnf))
    # resolution_result = resolution(full_cnf)
    # if resolution_result is False:
    #     print("Consistent!")
    # else:
    #     print("Not Consistent!")

