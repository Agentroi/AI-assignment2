import sympy
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Or, And, Not

def cnf(belief, newbelief):
    anded_formula = belief[0]
    not_new_belief = sympy.Not(newbelief)

    for formula in belief[1:]: 
        anded_formula = sympy.And(anded_formula,formula)

    full_belief = sympy.And(anded_formula,not_new_belief)

    cnfed_formula = sympy.to_cnf(full_belief)
    return cnfed_formula

def resolution(cnf_expression):
    # Extract clauses from CNF, each clause is a disjunction
    clauses = set(cnf_expression.args if isinstance(cnf_expression, And) else [cnf_expression])
    original_clauses = clauses.copy()
    new_clauses = True

    while new_clauses:
        new_clauses = set()
        # Try all pairs of clauses
        for clause1 in list(clauses):
            for clause2 in list(clauses):
                if clause1 is not clause2:
                    resolvent = resolve(clause1, clause2)
                    if resolvent is False:
                        print(f"Resolving {clause1} and {clause2} yields a contradiction.")
                        return False  # Contradiction found
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
        return clauses

def resolve(clause1, clause2):
    literals1 = set(clause1.args if isinstance(clause1, Or) else [clause1])
    literals2 = set(clause2.args if isinstance(clause2, Or) else [clause2])

    for lit1 in literals1:
        for lit2 in literals2:
            if lit1 == ~lit2 or ~lit1 == lit2:
                new_literals = (literals1.union(literals2) - {lit1, lit2})
                if new_literals:
                    return Or(*new_literals)
                else:
                    return False  # Empty clause (contradiction)
    return None  # No resolution possible

def check_implication(beliefs, formula):
    # Simplified checking using resolution or other means
    return resolution(to_cnf(And(*beliefs, Not(formula)))) is False

def find_remainder_sets(belief_base, phi):
    remainders = []
    for i in range(len(belief_base)):
        test_base = belief_base[:i] + belief_base[i+1:]
        if not check_implication(test_base, phi):
            remainders.append(test_base)
    return remainders

def select_remainder_based_on_entrenchment(remainders, entrenchment):
    # Selecting remainders that have the highest sum of entrenchment values
    max_entrenchment_value = -1
    selected_remainders = []
    for remainder in remainders:
        entrenchment_value = sum(entrenchment.get(belief, 0) for belief in remainder)
        if entrenchment_value > max_entrenchment_value:
            max_entrenchment_value = entrenchment_value
            selected_remainders = remainder
    return selected_remainders

def contract(belief_base, phi):
    remainders = find_remainder_sets(belief_base, phi)
    selected_remainder = select_remainder_based_on_entrenchment(remainders, entrenchment)
    return selected_remainder


if __name__ == '__main__':

    p, q, r, s = sympy.symbols('p q r s')
    #initial_belief = [(~p >> q),(q >> p),(p >> (r & s))]
    #new_belief = p & r & s

    #initial_belief = [~r >> q, ~q]
    #new_belief = r
    # Example belief base and entrenchment levels

    initial_belief = [(~p | ~q | r), (q | r), (p | r)]
    entrenchment = {
        (~p | ~q | r): 1,
        (q | r): 2,
        (p | r): 3 
    }
    new_belief = r
    full_cnf = cnf(initial_belief, new_belief)

    phi_to_contract = q
    contracted_belief_base = contract(initial_belief, phi_to_contract)
    print("Contracted Belief Base:", contracted_belief_base)
    
    # print("FULL CNF; ", full_cnf)
    # print(resolution(full_cnf))
    # resolution_result = resolution(full_cnf)
    # if resolution_result is False:
    #     print("Consistent!")
    # else:
    #     print("Not Consistent!")

