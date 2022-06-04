#Lexer by Andres Carlos Barrera Basilio A00815749
#Lexer using PLY
#Parser by Andres Carlos Barrera Basilio A00815749
#Parser using the above LExer and PLY

################## THE MIR LEXER AND PARSER #############################


#Librerias para importar en el Lexer-Parser
from re import split
import os
import sys
import ply.yacc as yacc
from Semanticcube import Semanticcube
from time import sleep

#Entrada de archivo de programacion para compilar con el input
arch = input("Nombre del archivo para compilar : ")


###################----------------GLOBAL VARIABLES AND METHODS------------------###################
###### PYTHON SETS, MUTABLE, ORDER OF ELEMENTS NOT IMPORTANT############

TABLEof_functions = {}
GLOBALvar_set = {}
LOCALvar_set = {}
CONSTANTSvar_set = {}


#The Operation number that will be stored inside the quads product indicating which type of operation the quads is
HASHofoperatorsinquads = {
    '+' : 1,
    '-' : 2,
    '*' : 3,
    '/' : 4,
    '>' : 5,
    '>=' : 6,
    '<' : 7,
    '<=' : 8,
    '==' : 9,
    '<>' : 10,
    '=' : 11,
    'READ' : 12,
    'WRITE' : 13,
    'and' : 14,
    'OR' : 15,
    'GOTO' : 16,
    'GOTOF' : 17,
    'GOTOV' : 18,
    'ERA' : 19,
    'VER' : 20,
    'ENDPROC' : 21,
    'PARAM' : 22,
    'GOSUB' : 23,
    'MEDIA' : 24,
    'MEDIANA' : 25,
    'MODA' : 26,
    'STDEV' : 27,
    'VARIANZA' : 28,
    'PLOTXY' : 29,
    'RETURN' : 30,
    '' : -1
}

##### PYTHON LISTS, MUTABLE, ORDER OF ELEMENTS INHERENT IN THEIR APPLICATION, CAN FUNCTION AS STACKS #############
#~~~~~~~IN PROGRESSS~~~~~~~~~~~
QUADSlist=[]

######### MY STACKS, USING THE PYTHON LISTS AND POP() TO SIMULATE THE STACK BEHAVIOR
PilaO = []
POper = []
Pilatypes = []
Pjumps = []
PDim = []

###### SENSORS, CHECKING THE SCOPE (CONTEXT) OF THE VARIABLES, & COUNTERS ############
INITIAlvarinFOR = 0
FINALvarinFOR = 0
TEMPORALScounter = 0
SPECIALMETHODScounter = -1
CURRENTcontext = 'g'
CURRENTtype = ''
CURRENTfunctionname = '' 

################ MEMORY MAP FOR VARIABLE, CONSTANT, FUNCTION, TEMPORAL, PARAMETERS AND POINTERS STORAGE ###########
#When a memory block is used, it adds 1 to the counter.
GLOBALINTcounter = 1000 - 1  # BLOCK of 2000 spaces 
GLOBALFLOATcounter = 3000 - 1
GLOBALCHARcounter = 5000 - 1
LOCALINTcounter = 7000 - 1
LOCALFLOATcounter = 9000 - 1
LOCALCHARcounter = 11000 - 1
TEMPINTcounter = 13000 - 1
TEMPFLOATcounter = 15000 - 1
TEMPCHARcounter = 17000 - 1
TEMPBOOLcounter = 19000 - 1
CONSTINTcounter = 21000 - 1
CONSTFLOATcounter = 23000 - 1
CONSTCHARcounter = 25000 - 1
FUNCTIONVIRADDRcounter = 27000 - 1 # BLOCK of 3000 spaces 
PARAMSINTcounter = 30000 - 1
PARAMSFLOATcounter = 33000 - 1
PARAMSCHARcounter = 36000 - 1 # BLOCK of 4000 spaces 
POINTERScounter = 40000 - 1 # LAST BLOCK


############### QUADRUPLE CLASS FOR STORING THE COMPILER OPERATIONS ############

class Quadruple :
    def __init__(self, operator,LeftOperand,RightOperand,result):
        global QUADSlist
        self.QUADcounter = len(QUADSlist) + 1 # The number of the quadruple, so that we can have GOTO and derived functions
        self.operator = operator
        self.LeftOperand = LeftOperand
        self.RightOperand = RightOperand
        self.result = result

#### SEMANTIC CUBE CLASS OBJECT, A SENSOR THAR CHECKS OPERATIONS BETWEEN THE SIMPLE DATATYPES #############
semantics = Semanticcube()

########################################################################################################################################

#---------------------------------------------------NEURALGIC FUNCTIONS AUX ------------------------------------------------------------
#---------------------------------------------------NEURALGIC FUNCTIONS AUX ------------------------------------------------------------
#---------------------------------------------------NEURALGIC FUNCTIONS AUX ------------------------------------------------------------
#---------------------------------------------------NEURALGIC FUNCTIONS AUX ------------------------------------------------------------
#---------------------------------------------------NEURALGIC FUNCTIONS AUX ------------------------------------------------------------




########### GLOBAL AUXILIAR METHODS FOR NEURALGIC POINTS MANIPULATIONS ############

#~~~~~~~IN PROGRESSS~~~~~~~~~~~
















#~~~~~~~IN PROGRESSS~~~~~~~~~~~


########################################################################################################################################

#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 
#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 
#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 
#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 
#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 
#---------------------------------------------------THE LEXER -------------------------------------------------------------------------- 

reserved = {
    'Program' : 'PROGRAM', # program reserved word
    'main' : 'MAIN', # main reserved word
    'function' : 'FUNCTION', # function reserved word 
    'VARS' : 'VARS', # VARS reserved word
    'int' : 'INT', # int reserved word
    'float' : 'FLOAT', # flot reserved word
    'char' : 'CHAR', # char reserved word
    'str' : 'STR', # STR reserved word
    'return' : 'RETURN', # return reserved word
    'read' : 'READ', # read reserved word
    'write' : 'WRITE', # write reserved word
    'and' : 'AND', # and reserved word
    'or' : 'OR', # or reserved word
    'if' : 'IF', # if reserved word
    'then' : 'THEN', # then reserved word
    'else' : 'ELSE',  # else reserved word
    'while' : 'WHILE', # while reserved word
    'do' : 'DO', # do reserved word
    'for' : 'FOR', # for reserved word
    'to' : 'TO', # to reserved word
    'void' : 'VOID', # void reserved word
    'true' : 'TRUE', # TRUE reserved word
    'false' : 'FALSE', # FALSE reserved word
    'media' : 'MEDIA', # special function average
    'mediana': 'MEDIANA', # special function median
    'moda' : 'MODA', # special function mode
    'varianza' : 'VARIANZA', # special function variance
    'stdev' : 'STDEV', # special function simple regression
    'plotxy' : 'PLOTXY', # special function plot two data columns
    } #dont put the previous reserved words as ID types, this handles that


##### THE LIST OF TOKENS IN MIR LANGUAGE
tokens = [
    'STRING', # String token
    'ID', # ID token
    'PLUS', # + symbol
    'REST', # - symbol
    'TIMES', # * symbol
    'DIVIDE', # / symbol
    'GREATER', # > symbol
    'GREATERAND', # >= symbol
    'LESSER', # < symbol
    'LESSERAND', # <= symbol
    'SAME', # == symbol
    'NOTSAME', # <> symbol
    'NOT', # ! symbol
    'EQUAL', # = symbol
    'LEFTBR', # { symbol
    'RIGHTBR', # } symbol
    'LEFTPAR', # ( symbol
    'RIGHTPAR', # ) symbol
    'LEFTSQR', # [ symbol
    'RIGHTSQR', # ] symbol
    'COLON', # : symbol
    'SEMICOLON', # ; symbol
    'COMMA', # , symbol
    'CTEINT', # constant int
    'CTEFLOAT', # constant float
    'CTECHAR', # constant char
] + list(reserved.values())

##### THE DEFINITION OF THE TOKENS
#---SYMBOLS

t_ignore = ' \t'
t_SEMICOLON = r'\;'
t_COLON = r'\:'
t_COMMA = r'\,'
t_EQUAL = r'\='
t_SAME = r'\=\='
t_LEFTPAR = r'\('
t_RIGHTPAR = r'\)'
t_LEFTBR = r'\{'
t_RIGHTBR = r'\}'
t_LEFTSQR = r'\['
t_RIGHTSQR = r'\]'
t_STRING = r'\".*\"'
t_PLUS  = r'\+'
t_REST = r'\-'
t_TIMES = r'\*'
t_DIVIDE = r'\/'
t_GREATER = r'\>'
t_GREATERAND = r'\>\='
t_LESSER = r'\<'
t_LESSERAND = r'\<\='
t_NOTSAME = r'\<\>'
t_NOT = r'\!'
t_CTECHAR =r"\'.\'"

#----COMPLEX DEFINITIONS

def t_CTEFLOAT(t):
    r'-?\d+\.\d+' # able to accept sign symbols, and .97 (numbers without the integer part)
    try:
        t.value = float(t.value)
    except ValueError:
        print("Float value too large %d", t.value)
        t.value = 0
    return t

def t_CTEINT(t):
    r'-?\d+' # taking account if sign symbol is present
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
    return t

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z0-9]*'
    t.type = reserved.get(t.value, 'ID') 
    return t


# every symbol that doesn't match with almost one of the previous tokens is considered an error
# modification so that all errors can be processed and debugged with the error catcher below

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")

def t_error(t):
    print("ERROR with illegal character (lexer) at: '%s'" % t.value[0])
    t.lexer.skip(1)

###################### BUILDING THE LEXER #########################
import ply.lex as lex
lexer = lex.lex()





########################################################################################################################################

#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------
#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------
#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------
#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------
#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------
#---------------------------------------------------THE GRAMMAR ------------------------------------------------------------------------ 




#--------------OUTER INITIAL SHELL--------------#
#functions = modules

def p_PROGRAM(p): #PROGRAM SHELL LOGIC
    '''
    program : PROGRAM neuraladdfuncdir varsgl modules MAIN LEFTPAR RIGHTPAR LEFTBR neuralmainjump statutes RIGHTBR
    '''
    print ('Llego al final de la gramatica, aceptado \n')
    global GLOBALINTcounter,GLOBALFLOATcounter,GLOBALCHARcounter
    global TEMPINTcounter,TEMPFLOATcounter,TEMPCHARcounter,TEMPBOOLcounter
    global CONSTINTcounter,CONSTFLOATcounter,CONSTCHARcounter,POINTERScounter

    actualmodulename = p[2] # GET THE NAME OF THE PROGRAM, WHICH WILL BE STORED IN THE DIRFUNC

    TABLEof_functions[actualmodulename]['Intnumbers'] = (GLOBALINTcounter-(1000-1)) + (TEMPINTcounter - (13000-1))
    TABLEof_functions[actualmodulename]['Floatnumbers'] = (GLOBALFLOATcounter - (3000 - 1)) + (TEMPFLOATcounter - (15000-1))
    TABLEof_functions[actualmodulename]['Charnumbers'] = (GLOBALCHARcounter-(5000-1)) + (TEMPCHARcounter - (17000-1))
    TABLEof_functions[actualmodulename]['Boolnumbers'] = (TEMPBOOLcounter-(19000-1))
    TABLEof_functions[actualmodulename]['Pointernumbers'] = (POINTERScounter-(40000-1))
    #STORING THE VARIABLE NUMBERS BY SUBSTRACTING THE INITIAL MEMORY ALLOCATIONS TO THE FINAL VARIABLES COUNTERS

def p_NEURALADDFUNCDIR(p): #NEURALGIC POINT THAT SAVES THE MAIN PROGRAM, STORING ITS QUADRUPLE PLACEMENT
    '''
    neuraladdfuncdir : ID SEMICOLON
    '''
    global CURRENTcontext,GLOBALvar_set,QUADSlist,HASHofoperatorsinquads,Pjumps,CONSTANTSvar_set
    p[0] = p[1] # SKIP THE TOKEN
    #### AUXILIAR insert in the table function###
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,-999))
    Pjumps.append(len(QUADSlist))
    #### AUXILIAR set the virtual address of constants 0 and 1, we will need it##