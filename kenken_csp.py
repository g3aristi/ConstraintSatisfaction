#Look for #IMPLEMENT tags in this file.

'''
Construct and return Kenken CSP model.
'''

from cspbase import *
import itertools
from copy import deepcopy

def operation_check(t, r, o):
    '''
    Returns booling:
    True if the 'o'peration applied to the 't'uple yields the 'r'esult
    False otherwise.
    '''
    if o is 0: # addition
        s = 0
        for n in t:
            s += n
        if s == r:
            return True, t
        return False, t
    
    elif o is 1: # substraction
        for perms in itertools.permutations(t):
            cr = perms[0]
            for i in range(1,len(perms)):
                cr -= perms[i]
            if cr == r:
                return True, t # there most be a way to return the permutation
        return False, t
    
    elif o is 2: # division
        for perms in itertools.permutations(t):
            cr = perms[0]
            for i in range(1,len(perms)):
                cr /= perms[i]
            if cr == r:
                return True, t # there most be a way to return the permutation
        return False, t
    
    elif o is 3: # multiplication
        p = 1
        for n in t:
            p *= n
        if p == r:
            return True, t
        return False, t

def row_cons(vars, cur_var, row_index, col_index):
    '''
    Returns a list of row constraints
    '''
    cur_var_row_cons = []
    check_row = vars[row_index]
    for i in range(0, len(check_row)):
        if i <= col_index:
            continue
        else:
            check_doms = []
            check_doms.append(cur_var.domain())
            check_doms.append(check_row[i].domain())
            sat_tuples = []

            for t in itertools.product(*check_doms):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            con = Constraint("C:V{}{}V{}{}".
                format(row_index+1, col_index+1, row_index+1, i+1), [cur_var, check_row[i]])
            con.add_satisfying_tuples(sat_tuples)
            cur_var_row_cons.append(con)

    return cur_var_row_cons

def col_cons(vars, cur_var, row_index, col_index):
    '''
    Returns a list of column constraints
    '''
    cur_var_col_cons = []
    check_col_vars = []
    for row in vars:
        check_col_vars.append(row[col_index])

    for i in range(len(check_col_vars)):
        if i <= row_index:
            continue
        else:
            check_doms = []
            check_doms.append(cur_var.domain())
            check_doms.append(check_col_vars[i].domain())
            sat_tuples = []

            for t in itertools.product(*check_doms):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            con = Constraint("C:V{}{}V{}{}".
                format(row_index+1, col_index+1, i+1, col_index+1), [cur_var, check_col_vars[i]])
            con.add_satisfying_tuples(sat_tuples)
            cur_var_col_cons.append(con)

    return cur_var_col_cons

def kenken_csp_model(kenken_grid):
    '''Returns a CSP object representing a Kenken CSP problem along 
       with an array of variables for the problem. That is return
       kenken_csp, variable_array
       where kenken_csp is a csp representing the kenken model
       and variable_array is a list of lists
       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]
       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the board (indexed from (0,0) to (N-1,N-1))
       
       The input grid is specified as a list of lists. The first list
	   has a single element which is the size N; it represents the
	   dimension of the square board.
	   
	   Every other list represents a constraint a cage imposes by 
	   having the indexes of the cells in the cage (each cell being an 
	   integer out of 11,...,NN), followed by the target number and the
	   operator (the operator is also encoded as an integer with 0 being
	   '+', 1 being '-', 2 being '/' and 3 being '*'). If a list has two
	   elements, the first element represents a cell, and the second 
	   element is the value imposed to that cell. With this representation,
	   the input will look something like this:
	   
	   [[N],[cell_ij,...,cell_i'j',target_num,operator],...]
	   
       This routine returns a model which consists of a variable for
       each cell of the board, with domain equal to {1-N}.
       
       This model will also contain BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.) and an n-ary constraint for each cage in the grid.
    '''
    
    # generate dom
    size = kenken_grid[0][0]
    dom = []
    i=0
    for i in range(1, size+1):
        dom.append(i)

    # generate vars
    vars = []
    for i in range(1, size+1):
        each_row = []
        for j in range(1, size+1):
            each_row.append(Variable('V{}{}'.format(i,j), dom))
        vars.append(each_row)

    # generate constraints
    cons = []
    for i in range(1, len(kenken_grid)):
        cage = kenken_grid[i]

        scope = []
        varDoms = []
        for j in range (0, len(cage)-2):
            each_dom = []
            for k in range(1, size+1):
                each_dom.append(k)
            varDoms.append(each_dom)
            index1 = int(str(cage[j])[0])
            index2 = int(str(cage[j])[1])
            scope.append(vars[index1-1][index2-1])

        sat_tuples = []
        
        for cp in itertools.product(*varDoms):
            result = operation_check(cp, cage[len(cage)-2], cage[len(cage)-1])
            if result[0]:
                sat_tuples.append(result[1])

        # make constraints
        con = Constraint("C:cage{})".format(i), scope)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)


    # make all binary constraints
    for v in range(0, len(vars)):
        row = vars[v]
        for r in range(len(row)):
            cur_var = row[r]
            row_con = row_cons(vars, cur_var, v, r)
            col_con = col_cons(vars, cur_var, v, r)
            cons.extend(row_con)
            cons.extend(col_con)

    kenken_csp = CSP("Kenken")

    # add vars
    for row in vars:
        for v in row:
            kenken_csp.add_var(v)

    # add constraints
    for c in cons:
        kenken_csp.add_constraint(c)

    return kenken_csp, vars
