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

def resolve(clause1, clause2):
    resolvents = []

    print("clause1:", clause1)
    print("clause2:", clause2)


    literals1 = list(clause1.args if isinstance(clause1, sympy.Or) else [clause1])
    literals2 = list(clause2.args if isinstance(clause2, sympy.Or) else [clause2])

    print("literals1:", literals1)
    print("literals2:", literals2)

    for literal1 in literals1:
        for literal2 in literals2:
            if literal1 == ~literal2 or ~literal1 == literal2:
                resolvent = [l for l in literals1 if l != literal1] + [l for l in literals2 if l != literal2]
                resolvents.append(resolvent)
    return resolvents

def resolution(cnf):
    clauses = list(cnf.args if isinstance(cnf, sympy.And) else [cnf])
    print("clauses:", clauses)

    while True:
        new_clauses = []
        n = len(clauses)
        pairs = [(clauses[i], clauses[j]) for i in range(n) for j in range(i + 1, n)]
        for ci, cj in pairs:
            if isinstance(ci, list):
                ci = ci[0]
            if isinstance(cj, list):
                cj = cj[0]
            resolvents = resolve(ci, cj)
            if [] in resolvents:  # Empty clause found, contradiction
                return True
            new_clauses.extend(resolvents)
        print("new clauses:", new_clauses)
        if len(new_clauses) <= len(clauses):  # No new clauses added, can't proceed further
            return False
        clauses += new_clauses

if __name__ == '__main__':

    #TODO: Implement belief base with user input, 1) give symbols 2) give beliefbase 3) give new belief
    #Remember to add correct paranthesis as the parser is a bit wack
    p, q, r, s, m = sympy.symbols('p q r s m')
    #initial_belief = [(~p >> q),(q >> p),(p >> (r & s))]
    #new_belief = q & ~p
    initial_belief = [(~r>>q), ~q]
    new_belief = r

    full_cnf = cnf(initial_belief, new_belief)
    
    print("full cnf:", full_cnf)
    print(resolution(full_cnf))


