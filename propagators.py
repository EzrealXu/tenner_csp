# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within 
   bt_search.
   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]
      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.
      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW
       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.
      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.
      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice
      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []
        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.
        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp
      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.
         for forward checking we forward check all constraints with V
         that have one unassigned variable left
         for gac we initialize the GAC queue with all constraints containing V.
   '''


def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if newVar:
        for constrain in csp.get_cons_with_var(newVar):
            if constrain.get_n_unasgn() == 0:
                variables = constrain.get_scope()
                values = []
                for variable in variables:
                    values.append(variable.get_assigned_value())
                if not constrain.check(values):
                    return False, []
    return True, []


def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    values_purne = []
    if (newVar == None):
        constraints = csp.get_all_cons()
        for constraint in constraints:
            if constraint.get_n_unasgn() == 1:
                variable = constraint.get_unasgn_vars()[0]
                for domain in variable.cur_domain():
                    if not constraint.has_support(variable, domain):
                        pair = (variable, domain)
                        if (pair not in values_purne):
                            values_purne.append(pair)
                            variable.prune_value(domain)
                if variable.cur_domain_size() == 0:
                    return False, values_purne
    else:
        constraints = csp.get_cons_with_var(newVar)
        for constraint in constraints:
            if constraint.get_n_unasgn() == 1:
                variable = constraint.get_unasgn_vars()[0]
                for domain in variable.cur_domain():
                    if not constraint.has_support(variable, domain):
                        pair = (variable, domain)
                        if (pair not in values_purne):
                            values_purne.append(pair)
                            variable.prune_value(domain)
                if variable.cur_domain_size() == 0:
                    return False, values_purne
    return True, values_purne


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    pruned_vals = []
    GAC = []

    if (newVar == None):
        constraints = csp.get_all_cons()
        for constraint in constraints:
            GAC.append(constraint)
    else:
        constraints = csp.get_cons_with_var(newVar)
        for constraint in constraints:
            GAC.append(constraint)
    while len(GAC) != 0:
        constraint = GAC.pop(0)
        for variable in constraint.get_scope():
            for domain in variable.cur_domain():
                if not constraint.has_support(variable, domain):
                    if (variable, domain) not in pruned_vals:
                        pruned_vals.append((variable, domain))
                        variable.prune_value(domain)
                    if variable.cur_domain_size() == 0:
                        GAC.clear()
                        return False, pruned_vals
                    else:
                        for cons in csp.get_cons_with_var(variable):
                            if (cons not in GAC):
                                GAC.append(cons)
    return True, pruned_vals

def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    v = csp.get_all_unasgn_vars()
    mrv = v[0]
    for variable in v:
        if mrv.cur_domain_size() > variable.cur_domain_size():
            mrv = variable
    return mrv
