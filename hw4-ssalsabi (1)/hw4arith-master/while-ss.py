import sys
import copy
import ply.ply.lex as lex
import ply.ply.yacc as yacc

stack = [] #holds our ast in post depth traversal
storage = {} #holds our variables
ordered = []
removed = 0
linecount = 0
loop = []

#lex rules
reserved = { #reserved words for conditionals
  'if' : 'IF',
  'then' : 'THEN',
  'else' : 'ELSE',
  'while' : 'WHILE',
  'do' : 'DO',
  'skip' : 'SKIP',
}
tokens = ['NUMBER', 'VAR', 'PLUS', 'MINUS', 'TIMES', 'LPAREN', 'RPAREN', 'EQUAL', 'true', 'false', 'GREATER', 'NOT', 'AND', 'OR', 'SEMI', 'ASSIGN'] + list(reserved.values())

t_PLUS = r'\+' #what our tokens look like
t_MINUS = r'\-'
t_TIMES = r'\*'
t_LPAREN = r'\('
t_RPAREN = r'\)'
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
t_ignore_LBRACK = r'\{'
t_ignore_RBRACK = r'\}'

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
 '''factor     : VAR ASSIGN expression
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
               | expression TIMES expression'''
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

def print_tree(tree): #for debugging purposes
  if(tree is None):
    return
  if(isinstance(tree, int) or isinstance(tree, str)):
    print(tree)
    return
  print_tree(tree.left)
  print_tree(tree.right)
  print_tree(tree.root)

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

def reverse_conditional_ast(ordered, start, end):
  #need a deep copy in higher up call
  i = start
  while(i <= end):
    if(ordered[i] == '∧' or ordered[i] == '∨' or ordered[i] == '<' or ordered[i] == '=' or ordered[i] == '*' or ordered[i] == '+' or ordered[i] == '-'):
      previ = i-1
      while(previ > start):
         if(isinstance(ordered[previ], int)) or (isinstance(ordered[previ], str)
         and ((ordered[previ] != '∧') and (ordered[previ] != '∨') and (ordered[previ] != '<') and (ordered[previ] != '=') and 
         (ordered[previ] != '*') and (ordered[previ] != '+') and ordered[previ] != '-')):
           if(isinstance(ordered[previ-1], int)) or (isinstance(ordered[previ-1], str)
           and ((ordered[previ-1] != '∧') and (ordered[previ-1] != '∨') and (ordered[previ-1] != '<') and (ordered[previ-1] != '=') and (ordered[previ-1] != '*')
           and (ordered[previ-1] != '+') and (ordered[previ-1] != '-'))):
               ordered.insert(previ, ordered[i])
               ordered.pop(i+1)
               break
         previ = previ - 1
    elif(ordered[i] == '¬'):
      ordered.insert(start, '¬')
      ordered.pop(i+1)
    i = i + 1
  return end

def add_paran(ordered, start, end):
 i = start
 while( i <= end):
   if(ordered[i] == '*' or ordered[i] == '+' or ordered[i] == '-'):
     if(ordered[i+1] != '('):
      ordered.insert(i+2, ')')
      end = end + 1
     else:
      balance = 1
      previ = i + 2
      while(previ <= end):
        if(ordered[previ] == '('):
          balance = balance + 1
        if(ordered[previ] == ')'):
          balance = balance - 1
        if(balance == 0):
          ordered.insert(previ, ')')
          end = end + 1
        previ = previ + 1
     if(ordered[i-1] != ')'):
      ordered.insert(i-1, '(')
      end = end + 1
      i = i + 1
     else:
      balance = 1
      previ = i - 2
      while(previ >= start):
       if(ordered[previ] == ')'):
         balance = balance + 1
       if(ordered[previ] == '('):
         balance = balance - 1
       if(balance == 0):
         ordered.insert(previ, '(')
         end = end + 1
         i = i + 1
         break;
       previ = previ - 1
   i = i + 1
 return end

def reverse_assign_ast(ordered, start, end):
  #need a deep copy in higher up call
  i = start
  while(i <= end):
    if(ordered[i] == '*' or ordered[i] == '+' or ordered[i] == '-' or ordered[i] == ':='):
      previ = i-1
      while(previ > start):
         if(isinstance(ordered[previ], int)) or (isinstance(ordered[previ], str) 
         and ((ordered[previ] != '+') and (ordered[previ] != '*') and (ordered[previ] != '-') and (ordered[previ] != ':=') and (ordered[previ] != ';'))):
           if(isinstance(ordered[previ-1], int)) or (isinstance(ordered[previ-1], str) 
           and ((ordered[previ-1] != '+') and (ordered[previ-1] != '*') and (ordered[previ-1] != '-') and (ordered[previ-1] != ':=') and (ordered[previ-1] != ';'))):
               ordered.insert(previ, ordered[i])
               ordered.pop(i+1)
               break
         previ = previ - 1
    i = i + 1
  end = add_paran(ordered, start, end)
  return end

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


def ifstate(stack, i, whilecopy = []): 
  conditional = []  #get the initial conditional
  while(stack[i] != "else"):
    conditional.insert(0, stack[i])
    stack.pop(i)
    i = i - 1
  j = 0
  ifcopy = copy.deepcopy(stack)
  while(stack[j] != "then"):
    j = j + 1
  if(solveboolean(conditional) == True):
    if(len(whilecopy) == 0):
      reverse_ast(ifcopy, 0, j-1, 0, True, False, whilecopy)
    else:
      reverse_ast(ifcopy, 0, j-1, 0, True, False, whilecopy)
      reverse_ast(whilecopy, 0, j-1, 0, False, False, whilecopy)
  else:
    if(len(whilecopy) == 0):
      x = j
      while(stack[j] != "else"):
        j = j + 1
      ifcopy.pop(j) #hacky solution
      reverse_ast(ifcopy, x+1, j-1, 0, True)
    else:
      x = j
      while(stack[j] != "else"):
        j = j + 1
      ifcopy.pop(j) #hacky solution
      reverse_ast(ifcopy, x+1, j-1, 0, True, False, whilecopy)
      reverse_ast(whilecopy, 0, len(whilecopy)-1, 0, False, False, whilecopy)
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

def whilestate(stack, i):
 conditional = []
 whilecopy = copy.deepcopy(stack)
 whilecopy.insert(i+1, "while")
 origi = i+1
 commprint = 0
 while(stack[i] != "do"):
   conditional.insert(0, stack[i])
   stack.pop(i)
   i = i - 1
 j = 0 
 while(solveboolean(conditional) == True):
   commprint = 0
   global loop
   loop.clear()
   reverse_ast(whilecopy, 0, origi, 0, True, True)
   val = copy.deepcopy(stack)
   while( i > j):
     if(val[j] == '+' or val[j] == '-' or val[j] == '*'):
       solvemath(val, j)
       j = 0
     if(val[j] == ":="):
       commprint = commprint + 1
       adddict(val, j)
       while(len(loop) != 0 and loop[0] != ';'):
         loop.pop(0)
       if(len(loop) != 0  and loop[0] == ';'):
         loop.pop(0)
       reverse_ast(whilecopy, 0, origi, 0, False, False)
       j = 0
     if(i-1 < len(val) and val[i - 1] == "if"):
       val.pop(i - 1)
       ifstate(val, i - 2, whilecopy)
       loop.clear()
       reverse_ast(whilecopy, 0, origi, 0, False, False)
       j = 0
     if(val[j] == "do"):
       break
     j = j + 1   
 j = 0
 while(i >= j):
  stack.pop(i)
  i = i - 1   
  

def reverse_if_ast(ordered, start, end):
 conditional = []
 i = end
 while(ordered[i] != 'else'):
   conditional.insert(0, ordered[i])
   ordered.pop(i)
   i = i - 1
   end = end - 1
 conditional.pop()
 if(len(conditional) != 1):
   reverse_conditional_ast(conditional, 0, len(conditional) - 1)
   add_paran(conditional, 0, len(conditional) - 1)
   if(conditional[0] == '¬'):
     if(len(conditional) != 2):
       conditional.insert(1, '(')
       conditional.insert(len(conditional), ')')
   else:
     conditional.insert(0, '(')
     conditional.insert(len(conditional), ')')
 ordered.insert(start, "if")
 start = start + 1
 end = end + 1
 while(len(conditional) != 0):
   ordered.insert(start, conditional.pop(0))
   start = start + 1
   end = end + 1
 ordered.insert(start, 'then')
 start = start + 1
 ordered.insert(start, '{')
 start = start + 1
 end = end + 1
 i = start
 while(ordered[i] != 'then'):
   i = i + 1
 ordered.pop(i)
 i = i - 1
 diff = start
 start = reverse_assign_ast(ordered, start, i)
 end = end + (start - i)
 semi = 0
 i = start
 ordered.insert(start + 1, '}')
 end = end + 1
 start = start + 1
 while(ordered[i] != 'else' and semi != 2):
  if(ordered[i] == ':=' and ordered[i + 1] != ';'):
    semi = semi + 1
  i = i + 1
 if(ordered[i] == 'else'):
  ordered.pop(i)
  start = start + 1
 ordered.insert(start, 'else')
 start = start + 1
 ordered.insert(start, '{')
 start = start + 1
 i = i + 1
 end = end + 1
 start = reverse_assign_ast(ordered, start, i)
 end = end + (start - i)
 ordered.insert(end+1, '}')
 end = end + 1
 start = start + 1
 return start, end

def reverse_while_ast(ordered, start, end, wcond):
 conditional = []
 i = end
 global loop
 while(ordered[i] != 'do'):
   conditional.insert(0, ordered[i])
   ordered.pop(i)
   i = i - 1
   end = end - 1
 conditional.pop()
 if(len(conditional) != 1):
   reverse_conditional_ast(conditional, 0, len(conditional) - 1)
   add_paran(conditional, 0, len(conditional) - 1)
   if(conditional[0] == '¬'):
     if(len(conditional) != 2):
       conditional.insert(1, '(')
       conditional.insert(len(conditional), ')')
   else:
     conditional.insert(0, '(')
     conditional.insert(len(conditional), ')')
 ordered.insert(start, "while")
 start = start + 1
 end = end + 1
 while(len(conditional) != 0):
   ordered.insert(start, conditional.pop(0))
   start = start + 1
   end = end + 1
 ordered.insert(start, 'do')
 start = start + 1
 ordered.insert(start, '{')
 start = start + 1
 end = end + 1
 i = start
 while(ordered[i] != 'do'):
   i = i + 1
 ordered.pop(i)
 i = i - 1
 if(ordered[i] == 'if'):
   diff = start
   start, end = reverse_if_ast(ordered, start, i) 
   if(wcond == True):
     while(diff <= end):
       loop.append(ordered[diff])
       diff = diff + 1
   i = start
   ordered.insert(start + 1, '}')
   end = end + 1
   start = start + 1
 else:
   if(ordered[i] == ';'):
     ordered.pop(i)
     i = i - 1
     semicol = start
     while(ordered[semicol] != ':='):
       semicol = semicol + 1
     ordered.insert(semicol + 1, ';')
     i = i + 1
   diff = start
   start = reverse_assign_ast(ordered, start, i)
   end = end + (start - i)
   if(wcond == True):
     while(diff <= end):
       loop.append(ordered[diff])
       diff = diff + 1 
   i = start
   ordered.insert(start + 1, '}')
   end = end + 1
   start = start + 1
 return end, start

def reverse_ast(stack, start, end, missemi = 0, cond = False, wcond = False, whilecopy = []):
  semi = missemi
  global loop
  global ordered
  global linecount
  ordered = copy.deepcopy(stack)
  i = start
  initstart = start
  while(start <= end):
    if(ordered[len(ordered) - 1] == ';'):
      if(ordered[i] == ':='):
        if(ordered[i + 1] != ';'):
          semi = semi + 1
          if(semi == 2):
            ordered.pop(len(ordered) - 1)
            continue
        i = reverse_assign_ast(ordered, start, i)
        if(ordered[i + 1] != ';'):
          ordered.insert(i+1, ';')
          i = i + 1
        else:
          i = i + 1
        start = i + 1
    elif(ordered[len(ordered) - 1] == 'if'):
      # will probably need a better method then end later
      i, end = reverse_if_ast(ordered, start, len(ordered) - 1)
      start = i + 1
    elif(ordered[len(ordered) - 1] == 'while'):
      i, end = reverse_while_ast(ordered, start, len(ordered) - 1, wcond)
      start = i + 1
    else:
      if(ordered[i] == ':='):
        i = reverse_assign_ast(ordered, start, i)
        start = i + 1
    i = i + 1
  if(ordered[len(ordered) - 1] == ';'):
    ordered.pop()
    end = end - 1
  x = initstart
  if(len(whilecopy) != 0 and cond == True):
    linecount = linecount + 1
    if(linecount == 10001):
      exit()
    print("⇒", end = "")
    y = initstart
    while(y <= end):
      if(ordered[y] != ';'):
       print(" ", end = "")
      print(ordered[y], end = "")
      y = y + 1
      if(y <= end and ordered[y] == '('):
        balance = 1
        print(" ", end = "")
        print(ordered[y], end = "")
        y = y + 1
        while(balance != 0):
          print(ordered[y], end = "")
          if(ordered[y] == ')'):
            balance = balance - 1
          elif(ordered[y] == '('):
            balance = balance + 1
          y = y + 1
    print(';', end = "")
  elif(len(whilecopy) != 0 and cond == False):
    while(x <= end): #no line count here
     if(ordered[x] != ';'):
       print(" ", end = "")
     if(isinstance(ordered[x], bool) and ordered[x] == True):
       print("true", end = "")
     elif(isinstance(ordered[x], bool) and ordered[x] == False):
       print("false", end= "")
     else:
       print(ordered[x], end = "")
     x = x + 1
     if(x <= end and ordered[x] == '('):
      balance = 1
      if(x-1 >= 0 and ordered[x-1] != '¬'):
        print(" ", end = "")
      if(isinstance(ordered[x], bool) and ordered[x] == True):
        print("true", end = "")
      elif(isinstance(ordered[x], bool) and ordered[x] == False):
        print("false", end= "")
      else:
        print(ordered[x], end = "")
      x = x + 1
      while(balance != 0):
        if(isinstance(ordered[x], bool) and ordered[x] == True):
          print("true", end = "")
        elif(isinstance(ordered[x], bool) and ordered[x] == False):
          print("false", end= "")
        else:
          print(ordered[x], end = "")
        if(ordered[x] == ')'):
          balance = balance - 1
        elif(ordered[x] == '('):
          balance = balance + 1
        x = x + 1
    print(", ", end = "")
    prettyprint(storage)
  elif(cond == False):
    linecount = linecount + 1
    if(linecount == 10001):
      exit()
    print("⇒ skip;", end = "")
    if(len(loop) != 0):
      y = 0
      while(y < len(loop)):
        if(loop[y] != ';'):
         print(" ", end = "")
        print(loop[y], end = "")
        y = y + 1
        if(y < len(loop) and loop[y] == '('):
          balance = 1
          print(" ", end = "")
          print(loop[y], end = "")
          y = y + 1
          while(balance != 0):
            print(loop[y], end = "")
            if(loop[y] == ')'):
              balance = balance - 1
            elif(loop[y] == '('):
              balance = balance + 1
            y = y + 1
      if(loop[len(loop)-1] != ';'):
        print(';', end = "")  
    while(x <= end):
      if(ordered[x] != ';'):
        print(" ", end = "")
      if(isinstance(ordered[x], bool) and ordered[x] == True):
        print("true", end = "")
      elif(isinstance(ordered[x], bool) and ordered[x] == False):
        print("false", end= "")
      else:
        print(ordered[x], end = "")
      x = x + 1
      if(x <= end and ordered[x] == '('):
       balance = 1
       if(x-1 >= 0 and ordered[x-1] != '¬'):
         print(" ", end = "")
       if(isinstance(ordered[x], bool) and ordered[x] == True):
         print("true", end = "")
       elif(isinstance(ordered[x], bool) and ordered[x] == False):
         print("false", end= "")
       else:
         print(ordered[x], end = "")
       x = x + 1
       while(balance != 0):
         if(isinstance(ordered[x], bool) and ordered[x] == True):
           print("true", end = "")
         elif(isinstance(ordered[x], bool) and ordered[x] == False):
           print("false", end= "")
         else:
           print(ordered[x], end = "")
         if(ordered[x] == ')'):
           balance = balance - 1
         elif(ordered[x] == '('):
           balance = balance + 1
         x = x + 1
    print(", ", end = "")
    prettyprint(storage)
    linecount =  linecount + 1
    if(linecount == 10001):
      exit()
    print("⇒", end ="") 
    if(len(loop) != 0):
      y = 0
      while(y < len(loop)):
        if(loop[y] != ';'):
         print(" ", end = "")
        print(loop[y], end = "")
        y = y + 1
        if(y < len(loop) and loop[y] == '('):
          balance = 1
          print(" ", end = "")
          print(loop[y], end = "")
          y = y + 1
          while(balance != 0):
            print(loop[y], end = "")
            if(loop[y] == ')'):
              balance = balance - 1
            elif(loop[y] == '('):
              balance = balance + 1
            y = y + 1
      if(loop[len(loop)-1] != ';'):
        print(';', end = "")
    x = initstart
    while(x <= end):
      if(ordered[x] != ';'):
        print(" ", end = "")
      if(isinstance(ordered[x], bool) and ordered[x] == True):
        print("true", end = "")
      elif(isinstance(ordered[x], bool) and ordered[x] == False):
        print("false", end= "")
      else:
        print(ordered[x], end = "")
      x = x + 1
      if(x <= end and ordered[x] == '('):
         balance = 1
         if(x-1 >= 0 and ordered[x-1] != '¬'):
           print(" ", end = "")
         if(isinstance(ordered[x], bool) and ordered[x] == True):
           print("true", end = "")
         elif(isinstance(ordered[x], bool) and ordered[x] == False):
           print("false", end= "")
         else:
           print(ordered[x], end = "")
         x = x + 1
         while(balance != 0):
           if(isinstance(ordered[x], bool) and ordered[x] == True):
             print("true", end = "")
           elif(isinstance(ordered[x], bool) and ordered[x] == False):
             print("false", end= "")
           else:
             print(ordered[x], end = "")
           if(ordered[x] == ')'):
             balance = balance - 1
           elif(ordered[x] == '('):
             balance = balance + 1
           x = x + 1
    print(", ", end = "")
    prettyprint(storage)
  elif(cond == True and wcond == True):
   x = 0
   linecount = linecount + 1
   if(linecount == 10001):
     exit()
   print("⇒", end ="")
   while(x <= (len(loop) - 1)):
     if(loop[x] != ';'):
        print(" ", end = "")
     print(loop[x], end = "")
     x = x + 1
     if(x <= (len(loop) - 1) and loop[x] == '('):
        balance = 1
        if(x-1 >= 0 and loop[x-1] != '¬'):
          print(" ", end = "")
        print(loop[x], end = "")
        x = x + 1
        while(balance != 0):
          print(loop[x], end = "")
          if(loop[x] == ')'):
            balance = balance - 1
          elif(loop[x] == '('):
            balance = balance + 1
          x = x + 1
   print(";", end = "")
   x = 0
   while(x <= end):
    if(ordered[x] != ';'):
      print(" ", end = "")
    if(isinstance(ordered[x], bool) and ordered[x] == True):
      print("true", end = "")
    elif(isinstance(ordered[x], bool) and ordered[x] == False):
      print("false", end= "")
    else:
      print(ordered[x], end = "")
    x = x + 1
    if(x <= end and ordered[x] == '('):
      balance = 1
      if(x-1 >= 0 and ordered[x-1] != '¬'):
        print(" ", end = "")
      if(isinstance(ordered[x], bool) and ordered[x] == True):
         print("true", end = "")
      elif(isinstance(ordered[x], bool) and ordered[x] == False):
         print("false", end= "")
      else:
         print(ordered[x], end = "")
      x = x + 1
      while(balance != 0):
         if(isinstance(ordered[x], bool) and ordered[x] == True):
           print("true", end = "")
         elif(isinstance(ordered[x], bool) and ordered[x] == False):
           print("false", end= "")
         else:
           print(ordered[x], end = "")
         if(ordered[x] == ')'):
           balance = balance - 1
         elif(ordered[x] == '('):
           balance = balance + 1
         x = x + 1
   print(", ", end = "")
   prettyprint(storage)
  else:
    linecount = linecount + 1
    if(linecount == 10001):
      exit()
    print("⇒", end = "")
    while(x <= end):
     if(ordered[x] != ';'):
       print(" ", end = "")
     if(isinstance(ordered[x], bool) and ordered[x] == True):
       print("true", end = "")
     elif(isinstance(ordered[x], bool) and ordered[x] == False):
       print("false", end= "")
     else:
       print(ordered[x], end = "")
     x = x + 1
     if(x <= end and ordered[x] == '('):
       balance = 1
       if(x-1 >= 0 and ordered[x-1] != '¬'):
         print(" ", end = "")
       if(isinstance(ordered[x], bool) and ordered[x] == True):
         print("true", end = "")
       elif(isinstance(ordered[x], bool) and ordered[x] == False):
         print("false", end= "")
       else:
         print(ordered[x], end = "")
       x = x + 1
       while(balance != 0):
         if(isinstance(ordered[x], bool) and ordered[x] == True):
           print("true", end = "")
         elif(isinstance(ordered[x], bool) and ordered[x] == False):
           print("false", end= "")
         else:
           print(ordered[x], end = "")
         if(ordered[x] == ')'):
           balance = balance - 1
         elif(ordered[x] == '('):
           balance = balance + 1
         x = x + 1
    print(", ", end = "")
    prettyprint(storage)

def solvemath(stack, i): #solve basic math functions
  global removed
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
     removed = removed + 2

def adddict(stack, i): #place variables in our dictionary
   global removed
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
      removed = removed + 4
     elif(i + 1 < len(stack) and stack[i + 1] != ';'):
      stack.pop(i)
      stack.pop(i-1)
      stack.pop(i-2)
      removed = removed + 3
     elif(i + 1 >= len(stack)):
      stack.pop(i)
      stack.pop(i-1)
      stack.pop(i-2)
      removed = removed + 3
     else:
      print("ERROR: unknown token")

def semistate(stack): #if we have assignments at the top of the stack go ahead and solve them
  i = 0
  missemi = 0
  while(i < len(stack) and missemi < 2): #make sure where in the stack
   if(stack[i] == '+' or stack[i] == '-' or stack[i] == '*'): #solve any arithmetic
     j = i
     while(stack[j] != ':='):
       j = j + 1
     if(missemi == 1 and stack[j + 1] != ';'):
        missemi = missemi + 1
        continue
     solvemath(stack, i)
     i = 0
   elif(stack[i] == ':='): #assign any values
     if(i + 1 < len(stack) and stack[i + 1] != ';'): # if we hit a second statement without a semicolon, we've hit a while or if and should stop
       missemi = missemi + 1;
       if(missemi == 2):
         break
     adddict(stack, i)
     if(len(stack) != 0):
       reverse_ast(stack, 0, len(stack) - 1, missemi)
     else:
       print("⇒ skip, ", end ="")
       prettyprint(storage) 
     i = 0
   if(i < len(stack) and (stack[i] == "true" or stack[i] == "false" or stack[i] == "=" or stack[i] == "<" or stack[i] == "¬" or stack[i] == "∧" or stack[i] == "∨")): #if we hit any boolean, we should stop
     break
   i = i + 1

def eval(stack):
  global removed
  global linecount
  while(len(stack) != 0): #while theres still items in the stack
    if(len(stack) != 0  and stack[len(stack) - 1] == ';'): #if theres a semicolon at the end of the stack, solve assignment operators at the top
      semistate(stack)
      if(len(stack) - 1 > 0 and stack[len(stack) - 1] == ';'):
        stack.pop(len(stack) - 1)
    if(len(stack) != 0 and stack[len(stack) - 1] == "while"): #if theres a while at the end of the stack, solve the while
      stack.pop(len(stack) - 1) 
      whilestate(stack, len(stack) - 1)
      if(len(stack) == 0):
        linecount = linecount + 1
        if(linecount == 10001):
          exit()
        print("⇒ skip, ", end = "")
        prettyprint(storage)
    if(len(stack) != 0 and stack[len(stack) - 1] == 'if'):
      stack.pop(len(stack) - 1)
      ifstate(stack, len(stack) - 1)
      if(len(stack) == 0):
        linecount = linecount + 1
        if(linecount == 10001):
          exit()
        print("⇒ skip, ", end = "")
        prettyprint(storage)
    else:  #otherwise solve everything from the bottom down
      j = 0
      while(len(stack) != 0): #until the stack is empty 
       if(stack[j] == '+' or stack[j] == '-' or stack[j] == '*'):
        solvemath(stack, j)
        j = 0
       elif(stack[j] == ":="):
        adddict(stack, j)
        if(len(stack) != 0):
          reverse_ast(stack, 0, len(stack) - 1)
        else:
          linecount = linecount + 1
          if(linecount >= 10001):
            exit()
          print("⇒ skip, ", end = "")
          prettyprint(storage)
        j = 0
       elif(stack[j] == "skip"):
        stack.pop(j)
        if(len(stack) != 0):
          reverse_ast(stack, 0, len(stack) - 1)
        removed = removed + 1
        j = 0
       j = j + 1

s = input() #grab our input
lexer = lex.lex() #create our lexer
parser = yacc.yacc() #create our parser
tree = parser.parse(s) #convert our parser solution into an AST
parse_tree(tree) # put that AST into a stack
eval(stack)
