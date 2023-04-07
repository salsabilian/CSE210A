import sys
import ply.ply.lex as lex
import ply.ply.yacc as yacc
tokens = ( # our tokens
 'number',
 'plus',
 'times',
 'modulo',
 'minus',
)
stack = [] # we place our ast in here in postorder order
#rules for our tokens
t_ignore = ' \t' # ignore white spaces
t_plus = r'\+'
t_minus = r'\-' #needed for negative numbers
t_times = r'\*'
t_modulo = r'\%'
def t_number(t):
  r'\d+'
  t.value = int(t.value)
  return t
def t_error(t): # handle token errors
  print("Illegal character '%s'" % t.value[0])
  t.lexar.skip(1) 
lexer = lex.lex() # produce our lexer
precedence = ( #the first part determines which way we are grouping
   ('left', 'plus'), #ordered from lowest to highest precedence
   ('left', 'times'),
   ('left', 'modulo'),
   ('right', 'uminus'),
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
# parser rules
def p_expr_uminus(p):
   'expression : minus expression %prec uminus' # if we find a negative expression give it uminus precedence
   p[0] = -p[2] #set our number to the negative version of itself
def p_expr_number(p): 
   'expression : number'
   p[0] = p[1]
def p_expression_binop(p): #AST structure
   '''expression : expression plus expression
                 | expression times expression
                 | expression modulo expression '''
   p[0] = Node("binop", p[1], p[3], p[2]) # putting expressions in our tree
def p_error(p):
   print("Syntax error at '%s' " % p.value)
def eval(tree):
   parse_tree(tree) # place ast in a stack in postorder
   i = 0
   while(len(stack) > 1):
     if(stack[i] == '*'):
        currind = i - 1
        prevnum1 = -1
        prevnum2 = -1
        while(currind >= 0 and (prevnum1 == -1 or prevnum2 == -1)):
          if(isinstance(currind,int) and prevnum1 == -1):
             prevnum1 = currind
          elif(isinstance(currind, int) and prevnum2 == -1):
             prevnum2 = currind
          currind =  currind - 1
        if(prevnum1 == -1 or prevnum2 == -1):
            print("error")
        else:
           stack[i] = stack[prevnum1] * stack[prevnum2]
           stack.pop(prevnum1)
           stack.pop(prevnum2)
        i = 0
     elif(stack[i] == '+'):
        currind = i - 1
        prevnum1 = -1
        prevnum2 = -1
        while(currind >= 0 and (prevnum1 == -1 or prevnum2 == -1)):
          if(isinstance(currind,int) and prevnum1 == -1):
             prevnum1 = currind
          elif(isinstance(currind, int) and prevnum2 == -1):
             prevnum2 = currind
          currind=currind-1
        if(prevnum1 == -1 or prevnum2 == -1):
            print("error")
        else:
           stack[i] = stack[prevnum1] + stack[prevnum2]
           stack.pop(prevnum1)
           stack.pop(prevnum2)
        i = 0
     elif(stack[i] == '%'):
        currind = i - 1
        prevnum1 = -1
        prevnum2 = -1
        while(currind >= 0 and (prevnum1 == -1 or prevnum2 == -1)):
          if(isinstance(currind,int) and prevnum1 == -1):
             prevnum1 = currind
          elif(isinstance(currind, int) and prevnum2 == -1):
             prevnum2 = currind
          currind=currind-1
        if(prevnum1 == -1 or prevnum2 == -1):
            print("error")
        else:
           stack[i] = stack[prevnum2] % stack[prevnum1]
           stack.pop(prevnum1)
           stack.pop(prevnum2)
        i = 0
     i=i+1
        
def parse_tree(tree): # order the ast and place in an array
   if(tree is None):
      return
   if(isinstance(tree, int)):
      stack.append(tree)
      return
   parse_tree(tree.left)
   parse_tree(tree.right)
   stack.append(tree.root) 
def print_tree(tree): # for debugging purpose
   if(tree is None):
      return
   if(isinstance(tree, int)):
      print(tree)
      return
   print_tree(tree.left)
   print_tree(tree.right)
   print(tree.root)
parser = yacc.yacc()
math = input()
tree = parser.parse(math) #ladies and gentlemen we have an AST
eval(tree)
print(stack[0]) #final answer
