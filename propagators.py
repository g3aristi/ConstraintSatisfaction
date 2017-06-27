#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

from queue import *
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
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

# helper function
def check_var_in_cons (pruned, c):
    '''  given c, check scope, if only one variable not assigned,
    check if that variable obey the cons
    '''
    if c.get_n_unasgn() is 1:
        unasgn = -1 
        scope = c.get_scope()
        vals = []       
        
        for i in range(0, len(scope)):
            if scope[i].is_assigned():
                vals.append(scope[i].get_assigned_value())
            elif not scope[i].is_assigned():
                unasgn = i
                vals.append(-1)
        domain = scope[unasgn].cur_domain()
        #variable for one cons
        for vl in domain:
            vals[unasgn] = vl
            if not c.check(vals):   #prune
                if (scope[unasgn], vl) not in pruned:
                    scope[unasgn].prune_value(vl)
                    pruned.append((scope[unasgn], vl))
        if scope[unasgn].cur_domain() == []:
            return False, pruned  
    return True, pruned

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    
    #no newVar: forward_check constraints whose scope contains only one variable
    if newVar is None:
        cons = csp.get_all_cons()
        pruned = []
        status = True
        for c in cons:
            #do forward check
            if c.get_n_unasgn() is 1:
                status, pruned = check_var_in_cons(pruned, c)
                if status is False:
                    return False, pruned                
    
    #newVar: run FC on all constraints that contain newVar.            
    else:
        pruned = []
        for c in csp.get_cons_with_var(newVar):
            # do forward check
            status, pruned = check_var_in_cons(pruned, c)
            if status == False:
                return False, pruned
                        
    return True, pruned    

# helper function
def enforce_gac(csp, queue, pruned):
    checked = []
    while not queue.empty():
        c = queue.get()
        checked.append(c)
        for v in c.get_scope(): 
            for d in v.cur_domain():
                
                #find an assignment for each value d
                if not c.has_support(v, d):
                    pruned.append((v, d))
                    v.prune_value(d)
                    if len(v.cur_domain()) is 0:
                        queue.empty()
                        return False, pruned
                    else:
                        new = csp.get_cons_with_var(v)
                        for n in new:
                            if n in checked:
                                checked.remove(n)
                                queue.put(n)
                            else:
                                pass
                else:
                    pass
    return True, pruned

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    
    pruned = []
    all_cons = csp.get_all_cons()
    q = Queue(len(all_cons)) 

    if newVar is None:
        for c in all_cons:
            q.put(c)
        return enforce_gac(csp, q, pruned)
    
    # GAC enforce with constraints containing newVar on GAC Queue 
    else:
        cons = csp.get_cons_with_var(newVar)
        for c in cons:
            q.put(c)
        return enforce_gac(csp, q, pruned)

