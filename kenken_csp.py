#Look for #IMPLEMENT tags in this file.

'''
Construct and return Kenken CSP model.
'''

from cspbase import *
import itertools

'''
Helper functions to create the Kenken CSP
'''
def check_operator(t, result, operator):
    '''
    Returns booling: 
    True when the 'operator' applied to 't' yields the expected 'result'
    False other wise
    '''
    if operator is 0: #plus
        sum = 0
        for num in t:
            sum += num
        if sum is result:
            return True
        return False
    
    elif operator is 1: #minus
        for perms in itertools.permutations(t):
            curr_result = perms[0]
            for i in range(1,len(perms)):
                curr_result = curr_result - perms[i]
            if curr_result is result:
                return True
        return False
    
    elif operator is 2: #divide
        for perms in itertools.permutations(t):
            curr_result = perms[0]
            for i in range(1,len(perms)):
                curr_result = curr_result / perms[i]
            if curr_result == result:
                return True
        return False
    
    elif operator is 3: #multiply
        product = 1
        for num in t:
            product = product * num
        if product is result:
            return True
        return False

def check_result(t, result):
    ''' Returns booling:
    True if 't' contains the result
    False other wise.
    '''
    if t[0] != result:
        return False
    return True

def make_row_cons(vars, curr_var, row_index, col_index):
    '''
    Makes the row constrains for the kenken game
    '''
    row_cons_for_curvar = []
    row_to_check = vars[row_index]
    for i in range(0, len(row_to_check)):
        if i <= col_index:
            continue
        else:
            domains_to_check = []
            domains_to_check.append(curr_var.domain())
            domains_to_check.append(row_to_check[i].domain())
            sat_tuples = []

            for t in itertools.product(*domains_to_check):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            con = Constraint("C:V{}{}V{}{}".
                format(row_index+1, col_index+1, row_index+1, i+1), [curr_var, row_to_check[i]])
            con.add_satisfying_tuples(sat_tuples)
            row_cons_for_curvar.append(con)

    return row_cons_for_curvar

def make_col_cons(vars, curr_var, row_index, col_index):
    '''
    Makes the column constraints for the kenken game
    '''
    col_cons_for_curvar = []
    col_vars_to_check = []
    #get all vars to check
    for row in vars:
        col_vars_to_check.append(row[col_index])

    for i in range(len(col_vars_to_check)):
        if i <= row_index:
            continue
        else:
            domains_to_check = []
            domains_to_check.append(curr_var.domain())
            domains_to_check.append(col_vars_to_check[i].domain())
            sat_tuples = []

            for t in itertools.product(*domains_to_check):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            con = Constraint("C:V{}{}V{}{}".
                format(row_index + 1, col_index + 1, i + 1, col_index + 1), [curr_var, col_vars_to_check[i]])
            con.add_satisfying_tuples(sat_tuples)
            col_cons_for_curvar.append(con)

    return col_cons_for_curvar

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
    
    #generate dom
    size = kenken_grid[0][0]
    dom = []
    i = 0
    for i in range(1, size + 1):
        dom.append(i)

    # generate vars
    vars = []
    for i in range(1, size + 1):
        each_row = []
        for j in range(1, size + 1):
            each_row.append(Variable('V{}{}'.format(i,j), dom))
        vars.append(each_row)

    # generate constraints
    cons = []
    for i in range(1, len(kenken_grid)):
        each_cage = kenken_grid[i]
    
        #generate list of lists for looping
        scope = []
        varDoms = []
        for j in range(0, len(each_cage) - 2):
            each_dom = []
            for k in range(1, size+1):
                each_dom.append(k)
            varDoms.append(each_dom)
            index1 = int(str(each_cage[j])[0])
            index2 = int(str(each_cage[j])[1])
            scope.append(vars[index1-1][index2-1])
    
        sat_tuples = []
        #iterate the cartesian product
        for t in itertools.product(*varDoms):
            if len(each_cage) > 2:
                if check_operator(t, each_cage[len(each_cage)-2], each_cage[len(each_cage)-1]):
                    sat_tuples.append(t)
            else:
                if check_result(t, each_cage[len(each_cage)- 1]):
                    sat_tuples.append(t)
    
            #make con
            con = Constraint("C:cage{})".format(i), scope)
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)
            
    #make all binary constraints
    for i in range(0, len(vars)):
        row = vars[i]
        for j in range(len(row)):
            curr_var = row[j]
            row_cons = make_row_cons(vars, curr_var, i, j)
            col_cons = make_col_cons(vars, curr_var, i, j)
            cons.extend(row_cons)
            cons.extend(col_cons)
            
    kenken_csp = CSP("kenkencsp:size{}".format(size))
    
    #add all vars
    for row in vars:
        for v in row:
            kenken_csp.add_var(v)
            
    #add all constraints
    for each_con in cons:
        kenken_csp.add_constraint(each_con) 
        
    return kenken_csp, vars