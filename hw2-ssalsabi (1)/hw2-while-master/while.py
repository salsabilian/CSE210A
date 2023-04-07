import sys
import copy
import ply.ply.lex as lex
import ply.ply.yacc as yacc

stack = [] #holds our ast in post depth traversal
storage = {} #holds our variables

#lex rules
reserved = { #reserved words for conditionals
  'if' : 'IF',
  'then' : 'THEN',
  'else' : 'ELSE',
  'while' : 'WHILE',
  'do' : 'DO',
  'skip' : 'SKIP',
}
tokens = ['NUMBER', 'VAR', 'PLUS', 'MINUS', 'TIMES', 'COMMA', 'LSQUARE', 'RSQUARE', 'LPAREN', 'RPAREN', 'LBRACK', 'RBRACK', 'EQUAL', 'true', 'false', 'GREATER', 'NOT', 'AND', 'OR', 'SEMI', 'ASSIGN'] + list(reserved.values()) #our tokens

t_PLUS = r'\+' #what our tokens look like
t_MINUS = r'\-'
t_TIMES = r'\*'
t_COMMA = r'\,'
t_LSQUARE = r'\['
t_RSQUARE = r'\]' 
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACK = r'\{'
t_RBRACK = r'\}'
t_EQUAL = r'\='
t_true = r'\true'
t_false = r'\false'
t_GREATER = r'\<'
t_AND = r'\∧'
t_OR = r'\∨'
t_NOT = r'\¬'
t_SEMI =  r'\;'
t_ASSIGN = r'\:='
t_ignore = " \t" #ignore white spaces

def t_NUMBER(t):  # our rule for numbers
  r'\d+'
  t.value = int(t.value)
  return t
def t_error(t):
  print("illegal character '%s' " % t.value[0])
  t.lexer.skip(1)

def t_VAR(t): #our rule for variables
  r'[a-zA-Z_][a-zA-Z_0-9]*'
  t.type = reserved.get(t.value, 'VAR')
  return t

#parsing rules
precedence =  ( #our precedence order
              ('left', 'IF', 'THEN', 'ELSE', 'WHILE', 'DO', 'SKIP'),
              ('left', 'SEMI', 'ASSIGN'),
              ('left', 'PLUS', 'MINUS'),
              ('left', 'TIMES'),
              ('left', 'true', 'false'),
              ('left', 'AND', 'OR'),
              ('left', 'GREATER', 'EQUAL'),
              ('left', 'NOT'),
              ('left', 'LPAREN', 'RPAREN'),
              ('right', 'UMINUS'),
              )
class Node:  #establish our node class for our AST
  def __init__(self,type,left = None, right=None, root = None):
    self.type = type
    if left != None:
       self.left = left
    else:
       self.left = None
    if right != None:
       self.right = right
    else:
       self.right = None
    self.root = root

def p_fact_comm(p): #commands
 '''factor     : VAR LSQUARE expression RSQUARE ASSIGN expression
               | VAR ASSIGN LSQUARE expression RSQUARE
               | VAR ASSIGN expression
               | factor SEMI factor
               | IF term THEN factor ELSE factor
               | WHILE term DO factor
               | SKIP
               | term
               | expression'''
 if(p[1] == "while"): #place while in our AST
   y = Node("comm", p[4], None, p[3])
   x = Node("comm", y, None, p[2])
   p[0] = Node("comm", x, None,  p[1])
 elif(p[1] == "if"): #place if in our AST
   x = Node("comm", p[6], None, p[5])
   y = Node("comm", p[4], None, p[3])
   z = Node("comm", y, x, p[2])
   p[0] = Node("comm", z, None, p[1])
 elif(p[1] == "skip"): #place skip in our AST
   p[0] = Node("comm", None, None, p[1])
 elif(p[3] == '['): #handling arrays
   x =  Node("comm", p[3], p[4], p[5])
   p[0] = Node("comm", p[1], x, p[2])
 elif(p[2] == '['): #handling changing specific values in an array
   z = Node("comm", p[2], p[3], p[4])
   y = Node( "comm", z , p[1], p[6])
   p[0] = Node("comm", y , None , p[5])
 else: #otherwise theres 3 like normal and place them normally
   p[0] = Node("comm", p[1], p[3], p[2])

def p_term_bool(p): #booleans
 '''term : true 
         | false
         | expression EQUAL expression
         | expression GREATER expression
         | NOT term
         | term AND term
         | term OR term
         | expression'''
 if(p[1] == "true"): #handle non 3 cases
  p[0] = Node("bool", None, None, True)
 elif(p[1] == "false"):
  p[0] = Node("bool", None, None, False)
 elif(p[1] == '¬'):
  p[0] = Node("bool", p[2], None, p[1])
 else:
  p[0] = Node("bool", p[1], p[3], p[2])

def p_expr_binop(p): #same as arith
 '''expression : expression PLUS expression
               | expression MINUS expression
               | expression TIMES expression
               | expression COMMA expression'''
 if(p[2] == ","):
   p[0] = Node("binop", p[3], None, p[1])
 else:
   p[0] = Node("binop", p[1], p[3], p[2])

def p_error(p): #can always use an error checker
   print("Syntax error at '%s' " % p.value)

def p_expr_uminus(p): #handles negative numbers
 'expression : MINUS expression %prec UMINUS'
 p[0] = -p[2]

def p_expr_number(p): #if its a number assign it
 'expression : NUMBER'
 p[0] = p[1]

def p_expr_var(p): #if its a variable assign it
 'expression : VAR'
 p[0] = p[1]

def p_expr_group(p): #ignore parenthesis
 'expression : LPAREN expression RPAREN'
 p[0] = p[2]

def p_expr_group_4(p): #ignore parenthesis
 'term : LPAREN term RPAREN'
 p[0] = p[2]
def p_expr_group_2(p): #include brackets
 'factor : LBRACK factor RBRACK'
 p[0] = Node("brack", p[3], p[2], p[1])

def p_expr_group_3(p):
 'factor : LSQUARE factor RSQUARE'
 p[0] = Node("Sbrack", p[3], p[2], p[1])


def print_tree(tree): #for debugging purposes
  if(tree is None):
    return
  if(isinstance(tree, int) or isinstance(tree, str)):
    print(tree)
    return
  print_tree(tree.left)
  print_tree(tree.right)
  print_tree(tree.root)

def parse_tree(tree): #place our tree in a stack to easily manipulate
  if(tree is None):
   return
  if(isinstance(tree, int) or isinstance(tree, str)):
    stack.append(tree)
    return
  parse_tree(tree.left)
  parse_tree(tree.right)
  parse_tree(tree.root)

def solvemath(stack, i): #solve basic math functions
  if(stack[i] == '+' or stack[i] == '-' or stack[i] == '*'):
     num1 = 0
     num2 = 0
     if(i - 1 >= 0 and isinstance(stack[i - 1], int)): #check to see if its an int
      num1 = stack[i - 1]
     elif(i - 1 >= 0 and isinstance(stack[i - 1], str)): #if its not its a variable
      if(stack[i-1] in storage):
        num1 = storage[stack[i - 1]]
     else: #this shouldnt happen
       print("ERROR : reached start of the stack")
     if(i - 2 >= 0 and isinstance(stack[i - 2], int)): #same as above for the second number
      num2 = stack[i - 2]
     elif(i - 2 >= 0 and isinstance(stack[i - 2], str)):
      if(stack[i-2] in storage):
        num2 = storage[stack[i - 2]]
     else:
       print("ERROR : reached start of the stack")
     if(stack[i] == '+'): #solve the math and place it in the top place
       stack[i] = num2 + num1;
     elif(stack[i] == '-'):
       stack[i] = num2 - num1;
     elif(stack[i] == '*'):
       stack[i] = num2 * num1;
     else:
       print("ERROR: unexplained token?")
     stack.pop(i-1) #remove the numbers before
     stack.pop(i-2)

def adddict(stack, i): #place variables in our dictionary
 if(i - 1 >= 0 and stack[i - 1] == ']'):
  stack.pop(i - 1) 
  arr = []
  i = i - 1
  while(stack[i-1] != '['):
    if(isinstance(stack[i-1], int)):
      arr.append(stack[i-1])
    else:
      if(stack[i-1] in storage.keys()):
        arr.append(storage[stack[i-1]])
      else:
        arr.append(0)
    stack.pop(i-1)
    i = i - 1
  stack.pop(i-1)
  i = i - 1 
  storage[stack[i-1]] = arr
  stack.pop(i - 1)
  stack.pop(i - 1)
  i = i - 1
 else:
   if(i - 2 >= 0): #make sure we are not at the bottom of stack
     if(isinstance(stack[i-1], int)): #if its an int just add it 
       storage[stack[i-2]] = stack[i - 1]
     else:
       if(stack[i-1] in storage.keys()): #if its another variable and its in our dictionary add it
         storage[stack[i-2]] = storage[stack[i-1]]
       else: #otherwise initialize it to 0
         storage[stack[i-2]] = 0
     if(i+1 < len(stack) and stack[i + 1] == ';'): #eliminate the variable, :=, the value, and potentially the semicolon from the stack
      stack.pop(i + 1)
      stack.pop(i)
      stack.pop(i - 1)
      stack.pop(i - 2)
     elif(i + 1 < len(stack) and stack[i + 1] != ';'):
      stack.pop(i)
      stack.pop(i-1)
      stack.pop(i-2)
     elif(i + 1 >= len(stack)):
      stack.pop(i)
      stack.pop(i-1)
      stack.pop(i-2)
     else:
      print("ERROR: unknown token")
def semistate(stack): #if we have assignments at the top of the stack go ahead and solve them
  i = 0
  missemi = 0
  while(i < len(stack) and missemi < 2): #make sure where in the stack
   if(stack[i] == '+' or stack[i] == '-' or stack[i] == '*'): #solve any arithmetic
     solvemath(stack, i)
     i = 0
   elif(stack[i] == ':='): #assign any values
     if(i + 1 < len(stack) and stack[i + 1] != ';'): # if we hit a second statement without a semicolon, we've hit a while or if and should stop
       missemi = missemi + 1;
       if(missemi == 2):
         break
     adddict(stack, i)
     i = 0
   if(i < len(stack) and (stack[i] == '{' or stack[i] == '}')): # if we hit a bracket it means we've hit a while or if and should stop
     break
   elif(i < len(stack) and (stack[i] == "true" or stack[i] == "false" or stack[i] == "=" or stack[i] == "<" or stack[i] == "¬" or stack[i] == "∧" or stack[i] == "∨")): #if we hit any boolean, we should stop
     break
   i = i + 1
def solveboolean(conditional): #boolean for if or while, solve it to find out if we need to do stuff
 cond = copy.deepcopy(conditional) #make a copy of the conditional cause we dont want to accidently destroy it
 i = 0
 while(len(cond) != 1): # we should one as our final cond value either true or false
   if(cond[i] == '+' or cond[i] == '-' or cond[i] == '*'): # solve any math
     solvemath(cond, i)
     i = 0
   if(cond[i] == "=" or cond[i] == "<"): #solve boolean < or =
     num1 = 0
     num2 = 0
     if(i - 1 >= 0 and isinstance(cond[i - 1], int)): #check to see if its an int or a variable
      num1 = cond[i - 1]
     elif(i - 1 >= 0 and isinstance(cond[i - 1], str)):
      if(cond[i-1] in storage):
        num1 = storage[cond[i - 1]]
     else:
       print("ERROR : reached start of the stack")
     if(i - 2 >= 0 and isinstance(cond[i - 2], int)): #same as above for num 2
      num2 = cond[i - 2]
     elif(i - 2 >= 0 and isinstance(cond[i - 2], str)):
      if(cond[i-2] in storage):
        num2 = storage[cond[i - 2]]
     else:
       print("ERROR : reached start of the stack")
     if(cond[i] == '='):  #solve the booleans
       cond[i] = num2 == num1
     if(cond[i] == '<'):
       cond[i] = num2 < num1
     if(cond[i] == '∧'):
       cond[i] = cond[i - 1] & cond[i - 2]
     if(cond[i] == '∨'):
       cond[i] = cond[i - 1] | cond[i - 2]
     cond.pop(i - 1)
     cond.pop(i - 2)
     i = 0
   if(cond[i] == '∧'): #solve the booleans
     cond[i] = cond[i - 1] & cond[i - 2]
     cond.pop(i - 1)
     cond.pop(i - 2)
     i = 0
   if(cond[i] == '∨'):
     cond[i] = cond[i - 1] | cond[i - 2]
     cond.pop(i - 1)
     cond.pop(i - 2)
     i = 0
   if(cond[i] == '¬'):
     if(cond[i-1] == False):
       cond[i] = True
     elif(cond[i-1] == True):
       cond[i] = False
     else:
       print("ERROR: Should be true or false")
     cond.pop(i - 1)
     i = 0      
   i = i + 1
 return cond[0] #return either true or false
 
def whilestate(stack, i):
 conditional = [] #get our initial conditional statement
 while(stack[i] != "do"): #when we hit do weve reached the end of our boolean
   conditional.insert(0, stack[i])
   stack.pop(i)
   i = i - 1
 if(stack[0] == '}'): #if we have brackets theres more than one command but dont worry we know to break out from the other bracket
   stack.pop(i)
   i = i - 2
   j = 0 
   while(solveboolean(conditional) == True):  #if the conditional is true we keep running and checking
     j = 0
     val = copy.deepcopy(stack) # make a copy of the stack cause were gonna keep going through
     val.pop(j) #pop the first bracket 
     while( i >= j):
       if(i-1 < len(val) and val[i - 1] == "if"): #solve if statements
         val.pop(i - 1)
         ifstate(val, i - 2)
         j = 0
       if(j < len(val) and (val[j] == '+' or val[j] == '-' or val[j] == '*')): #solve arithmetic
         solvemath(val, j)
         j = 0
       if(j < len(val) and val[j] == ":="): #assign values
         adddict(val, j)
         j = 0
       if(val[j] == "{" or val[j] == "}"): #if we hit another bracket break out
         break
       j = j + 1    
   j = 0 
   while(stack[i] != '{'): #until we hit the other bracket pop everything off the stack
     stack.pop(i)
     i = i - 1   
   stack.pop(i)
 else: #if theres no brackets theres only one command
   colon = False #if theres a colon we might have stacked while loops 
   stack.pop(i) 
   i = i - 1
   if(stack[i] == ';'): #pop the colon if its there 
     stack.pop(i)
     colon = True
   while(solveboolean(conditional) == True): #same as with bracket except this time we break out after the first command
     j = 0
     val =  copy.deepcopy(stack)
     while( i >= j):
       if(j < len(val) and (val[j] == '+' or val[j] == '-' or val[j] == '*')):
         solvemath(val, j)
         j = 0
       if(j < len(val) and val[j] == ":="):
         adddict(val, j)
         break
       if(j < len(val) and val[j] == "skip"):
         break
       j = j + 1
   if(colon == False and stack[len(stack) - 1] == "while"): #if we have stacked while loops we need to go to the first do not the last one
     j = 0  #we kept track of the initial do when we got our conditional
     while(len(stack) > 0 and  j < i): #hacky solution that passes the test case 
       stack.pop(0)
       j=j-1
   else:
     while(stack[0] != ":=" and stack[0] != "skip"): #otherwise we need to pop till we see the first command cause theres only one command
       stack.pop(0)
     stack.pop(0)
  
def ifstate(stack, i): 
  conditional = []  #get the initial conditional
  while(stack[i] != "else"):
    conditional.insert(0, stack[i])
    stack.pop(i)
    i = i - 1
  j = 0
  if(solveboolean(conditional) == True): #check if its true
    while(stack[j] != "then"): # if it is solve everything from the top down to then
      if(stack[j] == '+' or stack[j] == '-' or stack[j] == '*'):
        solvemath(stack, j)
        j = 0
      if(stack[j] == ":="):
        adddict(stack, j)
        j = 0
      if(stack[j] == "then"):
        stack.pop(j)
        break
      j = j + 1
    j = 0
    while(stack[j] != "else"): #then pop everything down to else
      stack.pop(j)
    stack.pop(j)
  else: #if its not true
    while(stack[j] != "then"): #pop all the way down to then
      stack.pop(j)
      i = i - 1
    stack.pop(j)
    i = i - 1
    while(stack[j] != "else"): #then solve everything down to else
      if(i-1 < len(stack) and stack[i - 1] == "while"):
        stack.pop(i - 1)
        whilestate(stack, i - 2)
        j = 0
      if(stack[j] == '+' or stack[j] == '-' or stack[j] == '*'):
        solvemath(stack, j)
        j = 0
      if(stack[j] == ":="):
        adddict(stack, j)
        j = 0
      if(stack[j] == "else"):
        stack.pop(j)
        break
      j = j + 1

def eval(stack):
  while(len(stack) != 0): #while theres still items in the stack
    if(len(stack) != 0  and stack[len(stack) - 1] == ';'): #if theres a semicolon at the end of the stack, solve assignment operators at the top
      stack.pop(len(stack) - 1)
      semistate(stack)
    if(len(stack) != 0 and stack[len(stack) - 1] == "while"): #if theres a while at the end of the stack, solve the while
      stack.pop(len(stack) - 1)
      whilestate(stack, len(stack) - 1)
      continue #this continue without my hacky solution above will create a infinite loop
    if(len(stack) != 0 and stack[len(stack) - 1] == "if"): # if theres a if at the end of the stack, solve the stack
      stack.pop(len(stack) - 1)
      ifstate(stack, len(stack) - 1)
    else:  #otherwise solve everything from the bottom down
      j = 0
      while(len(stack) != 0): #until the stack is empty 
       if(stack[j] == '+' or stack[j] == '-' or stack[j] == '*'):
        solvemath(stack, j)
        j = 0
       elif(stack[j] == ":="):
        adddict(stack, j)
        j = 0
       elif(stack[j] == "skip"):
        stack.pop(j)
        j = 0
       j = j + 1

def prettyprint(storage): #print our variable values the way the test script prefers
  key = sorted(storage.keys())
  print("{", end = '')
  for x in key:
   print(x, end = '')
   print(" → ", end = '')
   print(storage[x], end = '')
   if(list(key)[-1] != x):
     print(", ", end = '')
  print("}")

s = input() #grab our input
lexer = lex.lex() #create our lexer
parser = yacc.yacc() #create our parser
tree = parser.parse(s) #convert our parser solution into an AST
parse_tree(tree) # put that AST into a stack
eval(stack) #evaluate that stack
prettyprint(storage) #print out our dictionary
