#Lexer by Andres Carlos Barrera Basilio A00815749
#Lexer using PLY
#Parser by Andres Carlos Barrera Basilio A00815749
#Parser using the above LExer and PLY

################## THE MIR LEXER AND PARSER #############################


#Librerias para importar en el Lexer-Parser
from re import split
import os
import sys
import PIL
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
THEPARAMETERSset = {}


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

GLOBALnames = []
LOCALnames = []


CONTPARAMETERSlist = []
PARAMETERSTABLElist = []
PARAMETERSQUEUElist = []

SPECIALMETHODSlist = []
SPECIALMETHODSaux = []

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

def getandsetVirtualAddrFunc(): # SET THE VIRTUAL ADDRESS FOR THE FUNCTION 
    global FUNCTIONVIRADDRcounter
    FUNCTIONVIRADDRcounter += 1
    return FUNCTIONVIRADDRcounter

def ENDANDRESETFunc(): #RESET EVERY LOCAL AND TEMPORAL VARIABLES, INCLUDING POINTERS AND PARAMETERS
    global LOCALCHARcounter,LOCALFLOATcounter,LOCALINTcounter
    global TEMPINTcounter, TEMPFLOATcounter, TEMPCHARcounter, TEMPBOOLcounter, POINTERScounter
    global PARAMSINTcounter, PARAMSFLOATcounter, PARAMSCHARcounter, temporalsCounter
    global CURRENTcontext, LOCALvar_set, LOCALnames, THEPARAMETERSset,PARAMETERSTABLElist
    LOCALINTcounter = 7000 - 1
    LOCALFLOATcounter = 9000 - 1
    LOCALCHARcounter = 11000 - 1
    TEMPINTcounter = 13000 - 1
    TEMPFLOATcounter = 15000 - 1
    TEMPCHARcounter = 17000 - 1
    TEMPBOOLcounter = 19000 - 1
    PARAMSINTcounter = 30000 - 1
    PARAMSFLOATcounter = 33000 - 1
    PARAMSCHARcounter = 36000 - 1 
    POINTERScounter = 40000 - 1 
    CURRENTcontext = 'g' # RETURN TO THE GLOBAL SCOPE TILL NEXT LOCAL CHANGE
    LOCALvar_set = {} # EMPTY THE LOCAL VARIABLES
    LOCALnames = [] # EMPTY THE ORDERED USED NAMES
    temporalsCounter = 0 # RESET OUR COUNTER FOR TEMPORALS USED

def getandsetVirtualAddrCTE(value): # VIRTUAL ADDRESS SETER FOR CTES
    global CONSTINTcounter,CONSTFLOATcounter,CONSTCHARcounter
    constanttype = type(value)
    if constanttype == int:
        CONSTINTcounter += 1
        return CONSTINTcounter
    elif constanttype == float:
        CONSTFLOATcounter += 1
        return CONSTFLOATcounter
    elif constanttype == str:
        CONSTCHARcounter += 1
        return CONSTCHARcounter
    else: 
        ERRORHANDLER("type error", str(value)) # SEND THE VALUE THAT WE TRIED TO CONSTANT

def getandsetVirtualAddrVars(type, context): # VIRTUAL ADDRESS SETER FOR VARIABLES
    global GLOBALINTcounter, GLOBALFLOATcounter, GLOBALCHARcounter
    global LOCALINTcounter, LOCALFLOATcounter, LOCALCHARcounter
    if context == 'g':
        if type == 'int':
            GLOBALINTcounter += 1
            return GLOBALINTcounter + 1
        elif type == 'float':
            GLOBALFLOATcounter += 1
            return GLOBALFLOATcounter + 1
        elif type == 'char':
            GLOBALCHARcounter += 1
            return GLOBALCHARcounter + 1
    else:
        if type == 'int':
            LOCALINTcounter += 1
            return LOCALINTcounter
        elif type == 'float':
            LOCALFLOATcounter += 1
            return LOCALFLOATcounter
        elif type == 'char':
            LOCALCHARcounter += 1
            return LOCALCHARcounter


def getandsetVirtualAddrTemp(type): # GET THE VIRTUAL ADDRESS OF OUR TEMPORALS AND POINTERS
    global TEMPINTcounter, TEMPFLOATcounter, TEMPCHARcounter, TEMPBOOLcounter
    global TEMPORALScounter, POINTERScounter
    TEMPORALScounter += 1
    if type == 'int':
        TEMPINTcounter += 1
        return TEMPINTcounter
    elif type == 'float':
        TEMPFLOATcounter += 1
        return TEMPFLOATcounter
    elif type == 'char':
        TEMPCHARcounter += 1
        return TEMPCHARcounter
    elif type == 'bool':
        TEMPBOOLcounter += 1
        return TEMPBOOLcounter
    elif type == 'pointer':
        POINTERScounter += 1
        return POINTERScounter


def ERRORHANDLER(errortype,location = ""): # GET THE VARIOUS ERROR MESSAGES HANDLED
    errormessage = ""
    #I could match case here, but I dont want to change python versions midproject
    if errortype == "funcrepetida":
        errormessage = "FUNCION EXISTENTE REPETIDA"
    elif errortype == "nombreusado":
        errormessage = "ID DE VARIABLE Y/O PROGRAMA REPETIDA"
    elif errortype == "invalidoperator":
        errormessage = "OPERACION INVALIDA, MISMATCH DE TIPOS"
    elif errortype == "varrepetida":
        errormessage = "VARIABLE DECLARADA MULTIPLES VECES"
    elif errortype == "tiposdif":
        errormessage = "MISMATCH DE TIPOS"
    elif errortype == "tiposhuh":
        errormessage = "TIPO DE DATO NO ACEPTADO"
    elif errortype == "notype":
        errormessage = "VARIABLE SIN TIPO"
    elif errortype == "noval":
        errormessage = "VARIABLE SIN VALOR"
    elif errortype == "notthere":
        errormessage = "NO EXISTE LA VARIABLE QUE SE BUSCA "
    elif errortype == "type error":
        errormessage = "ERROR EN TIPO DE DATO CONSTANTE"
    elif errortype == "INVALIDOP":
        errormessage = "OPERACION INVALIDA"
    elif errortype == "funcwithparamhuh":
        errormessage = "FUNCION ESPERABA NO PARAMETROS"
    elif errortype == "invalidnumparams":
        errormessage = "FUNCION CON NUMERO DE PARAMETROS ERRONEO"
    elif errortype == "dimshuh":
        errormessage = "VARIABLE VECTOR SIN DIMENSIONES"
    print("ERROR " + errormessage + "\n at ===> " + str(location))
    sys.exit()

def insertinFunctable(id,type,context, variables): #INSERT THE FUNCTION INTO A UNORDERED SET
    global TABLEof_functions, GLOBALnames, LOCALnames
    if id in TABLEof_functions:
        ERRORHANDLER("funcrepetida") # FUNCTION ALREADY USED 
    elif id in GLOBALnames:
        ERRORHANDLER("nombreusado") # NAME ALREADY USED
    else:
        TABLEof_functions[id] = {'type' : type, 'context' : context, 'variables' : variables}
        GLOBALnames.append(id)

def insertinVartable(id,virtualaddr,type): #INSERT OUR FORMATTED VAR INSIDE A TABLE SET
    if virtualaddr < 7000:
        if id in GLOBALnames:
            ERRORHANDLER("nombreusado", str(id + " " + type))
        if id in GLOBALvar_set:
            ERRORHANDLER("varrepetida",id)
        GLOBALvar_set[id] = {'virtualaddress': virtualaddr, 'type' : type}
        GLOBALnames.append(id)
    else:
        if id in LOCALnames:
            ERRORHANDLER("nombreusado", str(id + " " + type))
        if id in LOCALvar_set:
            ERRORHANDLER("varrepetida",id)
        LOCALvar_set[id] = {'virtualaddress': virtualaddr, 'type' : type}
        LOCALnames.append(id)


def typechecker(type1,type2): # CHEKCIK IF OUR TYPES ARE ACTUALLY THE SAME, USED IN ASSIGNING, CYCLES AND LOOPS
    if type1 != type2:
        ERRORHANDLER("tiposdif",str(type1 + " ====== " + type2))

def getValtype(val): # RETURN THE VALUE OF THE VARIABLE, FUNCTION... THINGY WE ARE ACCESSING
    if val in LOCALvar_set:
        return LOCALvar_set[val]['type']
    if val in GLOBALvar_set:
        return GLOBALvar_set[val]['type']
    if val in TABLEof_functions:
        return TABLEof_functions[val]['type']
    if type(val) == int:
        return 'int'
    if type(val) == float:
        return 'float'
    if type(val) == str:
        return 'char'


def virtualaddrfetcher(val): #VIRTUAL ADDRESS FETCHER, CHECKING THE APPROPIATE SETS
    global GLOBALvar_set,LOCALvar_set, CONSTANTSvar_set,TABLEof_functions
    if val in LOCALvar_set: #IS IT IN THE LOCAL VARS?
        return LOCALvar_set[val]['virtualaddress']
    elif val in GLOBALvar_set: # IS IT IN THE GLOBAL VARS?
        return GLOBALvar_set[val]['virtualaddress']
    else: # ASSUMING CONSTANTS
        if type(val) == int:
            return CONSTANTSvar_set[int(val)]
        if type(val) == float:
            return CONSTANTSvar_set[float(val)]
        if type(val) == str:
            return CONSTANTSvar_set[str(val)]

def getType(val): #GETTING THE TYPE IN THE FOR NEURALGIC POINTS
    if val in LOCALvar_set: 
        try:
            return LOCALvar_set[val]['type']
        except:
            ERRORHANDLER("notype",val)
    elif val in GLOBALvar_set:
        try:
            return GLOBALvar_set[val]['type']
        except:
            ERRORHANDLER("notype",val)
    else:
        ERRORHANDLER("notthere",val) # IF ITS NOT THERE, THEN IT DOES NOT EXIST

def existencesensor(id): # METHOD TO CHECK IF THE DATA OF THE CONSTANT IS SAVED
    global LOCALvar_set,GLOBALvar_set,CONSTANTSvar_set,TABLEof_functions
    if id not in CONSTANTSvar_set and id not in GLOBALvar_set and id not in LOCALvar_set and id not in TABLEof_functions:
        ERRORHANDLER("notthere",id)

def setvirtualaddrdimensions(context,type,size): # METHOD USED IN DIMENSION MANAGEMENT OF VECTORS
    global GLOBALINTcounter, GLOBALFLOATcounter, GLOBALCHARcounter
    global LOCALINTcounter, LOCALCHARcounter, LOCALFLOATcounter
    if context == 'g':
        if type == 'int':
            GLOBALINTcounter += size
        elif type == 'float':
            GLOBALFLOATcounter += size
        elif type == 'char':
            GLOBALCHARcounter += size
    elif context == 'l':
        if type == 'int':
            LOCALINTcounter += size
        elif type == 'float':
            LOCALFLOATcounter += size
        elif type == 'char':
            LOCALCHARcounter += size

def dimensionssensor(id): # METHOD THAT CHECKS IF THE VARIABLES IS ACTUALLY AN ARRAY (OR VECTOR IN THIS LANGUAGE)
    global GLOBALvar_set, LOCALvar_set
    try:
        LOCALvar_set[id]['arraysensor']
    except:
        try: 
            GLOBALvar_set[id]['arraysensor']
        except:
            ERRORHANDLER("dimshuh")


def isarraymethod(id): #SIMILAR METHOD TO THE ABOVE, BUT RETURNS A BOOLEAN AND HAS NO ERRORHANDLER
    global GLOBALvar_set, LOCALvar_set
    try:
        LOCALvar_set[id]['arraysensor']
        return True
    except:
        try: 
            GLOBALvar_set[id]['arraysensor']
            return True
        except:
            return False

def setsizedims(id,context,size): # METHOD ADDING THE SIZE VALUE TO THE VARIABLE, IDENTIFYING IT AS A VECTOR
    global GLOBALvar_set,LOCALvar_set
    if context == 'g':
        GLOBALvar_set[id]['size'] = size
    elif context == 'l':
        LOCALvar_set[id]['size'] = size


def getdimlimits(id): # GET THE DIMENSION LIMITS OF A VECTOR
    global GLOBALvar_set, LOCALvar_set
    try:
        return LOCALvar_set[id]['size']
    except:
        return GLOBALvar_set[id]['size']

def fetinitialvirtualaddrvector(id): # GET THE INITIAL VIRTUAL ADDRESS OF A VECTOR
    global GLOBALvar_set, LOCALvar_set
    try:
        return LOCALvar_set[id]['virtualaddress']
    except:
        return GLOBALvar_set[id]['virtualaddress']


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




#-----------------------------------OUTER INITIAL SHELL---------------------------------------------#
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
    insertinFunctable(p[1],'VOID',CURRENTcontext,GLOBALvar_set)
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,-999))
    Pjumps.append(len(QUADSlist))
    CONSTANTSvar_set[0] = getandsetVirtualAddrCTE(0)
    CONSTANTSvar_set[1] = getandsetVirtualAddrCTE(1)
    #### AUXILIAR set the virtual address of constants 0 and 1, we will need it##

def p_NEURALMAINJUMP(p):
    '''
    neuralmainjump :
    '''
    global QUADSlist, Pjumps
    if Pjumps : #CHECK IF PENDING JUMPS EXIST, SHOULD BE THE MAIN JUMP
        endo = Pjumps.pop()
        newQuad = QUADSlist[endo-1]
        newQuad.result = len(QUADSlist) + 1 # GO TO THE PART WHERE THE MAIN ACTUALLY STARTS




#####------------------ VARIABLE DECLARATION LOGIC-----------------#####

def p_VARSGL(p): #THE GLOBAL VARS PART
    '''
    varsgl : VARS vars 
            | empty
    '''

def p_VARS(p):
    '''
    vars : typing COLON neuralinsertvar varsarr varsmul vars
            | empty
    '''

def p_NEURALINSERTVAR(p): #INSERT THE VAR DATA WITH ADDRESS AND TYPE
    '''
    neuralinsertvar : ID
    '''
    global CURRENTcontext,CURRENTtype #THE CURRENT TYPE DEALT WITH THE 'TYPING' GRAMMAR BELOW
    p[0]= p[1] #TOKEN SKIPPING
    newaddr = getandsetVirtualAddrVars(CURRENTtype,CURRENTcontext) ### AUXILIAR NEURAL FUNCTION to GET AND SET THE VIRTUAL ADDRESS
    insertinVartable(p[1],newaddr,CURRENTtype)# AUXILIAR FUNCTION TO INSERT IN VARTABLE


def p_VARSMUL(p): #MULTIPLE VARIABLE LOGIC TO GET VARIABLES SEPARATED BY COMMAS
    '''
    varsmul : SEMICOLON
            | COMMA neuralinsertvar varsarr varsmul
    '''


#-------------------- VECTOR VARIABLE DECLARATION LOGIC---------------#

def p_VARSARR(p): # LOGIC FOR GETTING VECTOR VARIABLES
    '''
    varsarr : neuralinitdim CTEINT neuralenddim
            | empty
    '''
    ### LOGIC IN PROGRESS.....

def p_NEURALENDDIM(p):
    '''
    neuralenddim : RIGHTSQR
    '''
    global CURRENTcontext, CURRENTtype, CONSTANTSvar_set
    sizedim = int(p[-1]) # THE PREVIOUS TOKEN VALUE IS TAKEN AS INT
    id = p[-3] # GET THE IDENTIFIER

    if not p[-1] in CONSTANTSvar_set: # IF THE VALUE USED HERE ISNT ALREADY STORED AS A CONSTANT, STORE IT
        CONSTANTSvar_set[sizedim] = getandsetVirtualAddrCTE(sizedim)

    setsizedims(id,CURRENTcontext,sizedim) # SET THE DIMS IN THE APPROPIATE CONTEXT VARIABLE SET
    setvirtualaddrdimensions(CURRENTcontext,CURRENTtype,sizedim) # SET THE LIMITS OF MEMORY USED


def p_NEURALINITDIM(p): # MAKE THE STORED VARIABLE VECTOR HAVE AN ARRAYSENSOR SET TO TRUE
    '''
    neuralinitdim : LEFTSQR
    '''
    global LOCALvar_set, GLOBALvar_set, CURRENTcontext
    id = p[-1] # GET THE NAME WE ARE LOOKING FOR
    if CURRENTcontext == 'g':
        GLOBALvar_set[id]['arraysensor'] = True 
    elif CURRENTcontext == 'l':
        LOCALvar_set[id]['arraysensor'] = True



#DIMENSIONAL ACCESS HANDLER
def p_IDARRAY(p):
    '''
    idarray : neuralinitarray exp verify RIGHTSQR
            | empty
    '''
    global PilaO,QUADSlist,HASHofoperatorsinquads,GLOBALvar_set,Pilatypes,POper, CONSTANTSvar_set
    if len(p) > 2 :
        if PilaO and POper: # IF THE STACKS ARE NOT EMPTY AND WE HAVE A WORKING ARRAY
            aux = PilaO.pop()
            initaddr = fetinitialvirtualaddrvector(p[-1])
            if not initaddr in CONSTANTSvar_set: # IF NEW CONSTANT,SAVE IT
                CONSTANTSvar_set[initaddr] = getandsetVirtualAddrCTE(initaddr)
            actualaddr = CONSTANTSvar_set[initaddr] # IF ALREADY USED, GIVE US THE VIRTUALADDRESS
            pointer = getandsetVirtualAddrTemp('pointer')
            QUADSlist.append(Quadruple(HASHofoperatorsinquads['+'],aux,actualaddr,pointer)) # AS SEEN IN CLASS TO DEAL WITH ARRAYS
            PilaO.append(pointer)
            POper.pop() #DEAL WITH THE OPERATOR

def p_NEURALINITARRAT(p):
    '''
    neuralinitarray : LEFTSQR
    '''
    global POper,PilaO,PDim,Pilatypes
    if PilaO:
        id = PilaO.pop()
        typeclearer = Pilatypes.pop()
        name = p[-1] # GET THE TOKEN IDENTIFIER FOR THIS VECTOR
        dimensionssensor(name)
        DIM = 1 # IN THIS LANGUAAAGE, ONLY VECTORS PASS MY LIEGE
        PDim.append((id,DIM))
        POper.append("~~~") # OUR FAKE BOTTOM, AS SEEN IN CLASS



def p_VERIFY(p):
    '''
    verify : 
    '''
    global PilaO, QUADSlist, HASHofoperatorsinquads, CONSTANTSvar_set
    value = PilaO[-1] # OUR LAST ELEMENT, TOP() INHERENT IN PYTHON 
    id = p[-3] # GET THAT IDENTIFIER
    limit = getdimlimits(id)
    upperlimit = virtualaddrfetcher(limit) # GET OUR LIMITS GO GO GO
    lowerlimit = virtualaddrfetcher(0)
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['VER'],value,lowerlimit,upperlimit)) # OUR NICE VER QUADRUPLE




# TYPING OF VARIABLES SECTION 

def p_TYPING(p):
    '''
    typing : INT
            | FLOAT
            | CHAR
    '''
    global CURRENTtype
    CURRENTtype = p[1] # THE NEXT TOKEN GETS TAKEN AS THE CURRENT TYPE
    p[0] = p[1] #SKIPPING

#--------------------------------FUNCTIONS SHELL-----------------------------------------#
# IN THE GRAMMAR STYLE OF function void/type FunctionName (int: id, float: id[val])

def p_MODULES(p): #LOGIC TO GET THE MODULES/FUNCTIONS SAVED
    '''
    modules : FUNCTION functype neuralinsertfuncs funcparam
            | empty
    '''

def p_NEURALINSERTFUNCS(p): # INSERT WITH AUXILIAR FUNCTIONS
    '''
    neuralinsertfuncs : ID
    '''
    global CURRENTcontext, CURRENTtype, LOCALvar_set,GLOBALvar_set,CURRENTfunctionname
    CURRENTfunctionname = p[1] # GET THAT FUNCTION NAME (THE ID)
    p[0]= p[1] #SKIPPING
    CURRENTcontext = 'l'
    newaddr = getandsetVirtualAddrFunc() # GET THE NEW FUNCTION ADDRESS
    GLOBALvar_set[CURRENTfunctionname]={'virtualaddress': newaddr, 'type' : CURRENTtype} # SAVE THE FUNCTION NAME AS A GLOBAL VARIABLE AS SEEN IN CLASS
    insertinFunctable(CURRENTfunctionname,CURRENTtype,CURRENTcontext,LOCALvar_set) # SAVE THE DATA TO INSERT INTO THE FUNCTION TABLES


def p_FUNCPARAM(p): #GRAMMAR LOGIC TO GET ALL PARAMETERS AND NEURALGIC POINTS RELATING TO FUNCTIONS MAINTENANCE
    '''
    funcparam : LEFTPAR parameters RIGHTPAR SEMICOLON varsgl LEFTBR neuralinitfuncs statutes RIGHTBR neuralfuncsize neuralendfuncs modules
    '''
    global CURRENTcontext 
    CURRENTcontext = 'l' #CHANGE THE CONTEXT


def p_NEURALENDFUNCS(p): # NEURALGIC POINT FOR ENDPROC QUADS AND RESETTING LOCAL MEMORY
    '''
    neuralendfuncs :
    '''
    global TABLEof_functions,QUADSlist,HASHofoperatorsinquads,CURRENTfunctionname, TEMPORALScounter
    id = CURRENTfunctionname
    TABLEof_functions[id]['Tempsnumber'] = TEMPORALScounter # SAVE THE TEMPORALS NUMBER
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['ENDPROC'],-1,-1,-1)) #SAVE THE QUAD
    ENDANDRESETFunc()#### AUXILIAR TO RESET THE LOCAL AND TEMPORAL VARIABLES

def p_NEURALFUNCSIZE(p): # THE NEURALGIC POINT THE HANDLES THE VARIABLE SIZES OF THE FUNCTION INVOLVED
    '''
    neuralfuncsize :
    '''
    global TABLEof_functions, LOCALvar_set, QUADSlist, CURRENTfunctionname
    global LOCALINTcounter,LOCALFLOATcounter, LOCALCHARcounter, TEMPINTcounter, TEMPFLOATcounter, TEMPCHARcounter, TEMPBOOLcounter, POINTERScounter
    actualfuncname = CURRENTfunctionname
    TABLEof_functions[actualfuncname]['Paramnumbers'] = len(LOCALvar_set)
    TABLEof_functions[actualfuncname]['Intnumbers'] = (LOCALINTcounter-(7000-1)) + (TEMPINTcounter - (13000-1))
    TABLEof_functions[actualfuncname]['Floatnumbers'] = (LOCALFLOATcounter - (9000 - 1)) + (TEMPFLOATcounter - (15000-1))
    TABLEof_functions[actualfuncname]['Charnumbers'] = (LOCALCHARcounter-(11000-1)) + (TEMPCHARcounter - (17000-1))
    TABLEof_functions[actualfuncname]['Boolnumbers'] = (TEMPBOOLcounter-(19000-1))
    TABLEof_functions[actualfuncname]['Pointernumbers'] = (POINTERScounter-(40000-1))
    # ALL THE SAVING OF ACTUAL VARIABLE NUMBERS, SAME AS THE OUTER PROGRAM VERSION

def p_NEURALINITFUNCS(p): #NEURALGIC POINT THAT GENERATES THE QUAD AND SAVES THE FUNCTION ADDR IN THE TABLEof_functions
    '''
    neuralinitfuncs :
    '''
    global CURRENTfunctionname,QUADSlist
    actualmodulename = CURRENTfunctionname
    TABLEof_functions[actualmodulename]['Initialfuncpoint']= len(QUADSlist) + 1

def p_FUNCTYPE(p): # DEALING WITH THE VOID OR TYPING
    '''
    functype : VOID
            | typing
    '''
    global CURRENTtype
    CURRENTtype = p[1] # SAVE THE TYPE WITH THE NEXT TOKEN



####PARAMATERS AND RELATED SECTION #######

def p_PARAMETERS(p): # THE LOGIC TO GET ALL THE PARAMETRS IN A FUNCTION CALL
    '''
    parameters : typing COLON neuralinsertparam idarray mulparams
                | empty
    '''
    

def p_NEURALINSERTPARAM(p): # GET AND SAVE ALL THE PARAMETER DATA
    '''
    neuralinsertparam : ID
    '''
    global CURRENTcontext,CURRENTtype, PARAMETERSTABLElist, PARAMETERSQUEUElist
    CURRENTcontext = 'l'
    virtualaddr = getandsetVirtualAddrVars(CURRENTtype,CURRENTcontext) # GET TEH ADDRESS
    PARAMETERSQUEUElist.append(virtualaddr) # ADD TO THE LIST THE ADDRESS
    insertinVartable(p[1],virtualaddr, CURRENTtype) # GET THE VALUE WE ARE LOOKING FOR AND ADD IT TO THE VARTABLE
    PARAMETERSTABLElist.append(CURRENTtype)



def p_MULPARAMS(p): # HANDLE TEH MULTIPLE PARAMETERS
    '''
    mulparams : COMMA parameters
                | empty
    '''


#--------------------------------THE STATUTES SHELL DEFINITION-----------------------------------------#

def p_STATUTES(p): # THE CENTRAL LOGIC OF A PROGRAM WHERE WE HAVE ALL THE POSSIBLE STATUTES
    '''
    statutes : assign statuteaux
            | reading statuteaux
            | writing statuteaux
            | returning statuteaux
            | ifing statuteaux
            | whiling statuteaux
            | foring statuteaux
            | exp statuteaux
            | media statuteaux
            | plotxy statuteaux
            | mediana statuteaux
            | moda statuteaux
            | variance statuteaux
            | stdev statuteaux
    '''

def p_STATUTEAUX(p): # THE MULTIPLE STATUTES HANDLER
    '''
    statuteaux : statutes
                | empty
    '''

#------------------------ SPECIAL FUNCTIONS OF MYRLIKELANGUAGE --------------------------------#######
def p_MEDIA(p):
    '''
    media : MEDIA LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_MEDIANA(p):
    '''
    mediana : MEDIANA LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_MODA(p):
    '''
    moda : MODA LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_STDEV(p):
    '''
    stdev : STDEV LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_VARIANCE(p):
    '''
    variance : VARIANZA LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_PLOTXY(p):
    '''
    plotxy : PLOTXY LEFTPAR specfuncnumbers RIGHTPAR specialfunclist SEMICOLON
    '''

def p_SPECIALFUNCLIST(p):
    '''
    specialfunclist : 
    '''

def p_SPECFUNCNUMBERS(p): # METHOD TO HANDLE THE CONSTANT NUMBERS
    '''
    specfuncnumbers : CTEINT neuralnum mulnumeros
                    | CTEFLOAT neuralnum mulnumeros
    '''

def p_NEURALNUM(p): #NEURALGIC POINT TO DEAL WITH THE PARAMETERS OF A SPECIAL METHOD
    '''
    neuralnum :
    '''

def p_MULNUMEROS(p): # MULTIPLE CONSTANTS IN THE SPECIAL METHOD
    '''
    mulnumeros : COMMA specfuncnumbers
                | empty
    '''


######--------------------- ASSIGN LOGIC SECTION ------------------------------######
# ID = 123 ; OR ID =12.3 OR ID = VAR OR ID = VAR[1] OR ID = FUNCTION(1,1) OR ID = 'C' 
def p_ASSIGN(p):
    '''
    assign : neuralassign idarray neuralassign2 assignexp SEMICOLON
    '''
    global PilaO, Pilatypes, HASHofoperatorsinquads
    if PilaO and Pilatypes : #NOT EMPTY, CHECK THE LAST 2 Operands
        result = PilaO.pop()
        righttype = Pilatypes.pop()
        leftop = PilaO.pop()
        lefttype = Pilatypes.pop()
        typechecker(lefttype,righttype)#Auxiliar typechecker cubo semantico
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],result,-1,leftop))

def p_NEURALASSIGN(p):
    '''
    neuralassign : ID
    '''
    global PilaO,Pilatypes
    p[0]=p[1] #SKIPPING
    virtualaddr = virtualaddrfetcher(p[1]) # GET THE TOKEN WE ARE LOOKING FOR
    PilaO.append(virtualaddr)
    Pilatypes.append(getValtype(p[1])) # GET THE TYPE OF THE VALUE WE ARE LOOKING

def p_NEURALASSIGN2(p):
    '''
    neuralassign2 : EQUAL
    '''
    global POper
    POper.append(p[1]) # STORING THE EQUAL TOKEN

def p_ASSIGNEXP(p):
    '''
    assignexp : exp
    '''
    p[0]=p[1] # SKIPPING TOKEN





#### RETURN SPECIAL QUAD ####
def p_RETURNING(p): # A STATIC GRAMMAR, ONLY THE EXP IS SPECIAL
    '''
    returning : RETURN LEFTPAR exp RIGHTPAR SEMICOLON
    '''
    global PilaO,QUADSlist,HASHofoperatorsinquads,GLOBALvar_set
    valtoreturn = PilaO.pop()
    Pilatypes.pop()
    funcviraddr = GLOBALvar_set[CURRENTfunctionname]['virtualaddress'] # GET ME THE ADDRESS FOR THE FUNCTION SPECIAL VARIABLE WE HAVE HERE
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['RETURN'],valtoreturn,-1,funcviraddr))




######--------------------- READ LOGIC SECTION ------------------------------######

def p_READING(p): # OUR OUTER SHELL OF THE READ LOGIC
    '''
    reading : READ LEFTPAR neuralreadid idarray mulread RIGHTPAR SEMICOLON
    '''

def p_NUERALREADID(p):
    '''
    neuralreadid : ID
    '''
    global QUADSlist,HASHofoperatorsinquads
    assignedvar = virtualaddrfetcher(p[1]) # THE VAR TO BE READ AND ASSIGNED VALUE, GET THEIR ADDRESS
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['READ'],-1,-1,assignedvar)) #ADD THE QUADRUPLE

def p_MULREAD(p): # MANAGE THE MULTIPLE READING TO ASSIGN VALUE TO VARIABLES
    '''
    mulread : COMMA neuralreadid idarray mulread
            | empty
    '''



######--------------------- READ LOGIC SECTION ------------------------------######
def p_WRITING(p): # WRITE ALL DATA, ARRAY EXPECTED TO BE ALREADY IN A SPECIFIC VAR WHEN ACCESSED BY EXP
    '''
    writing : WRITE LEFTPAR neuralwrite mulwrite RIGHTPAR SEMICOLON
    '''

def p_NEURALWRITE(p):
    '''
    neuralwrite : writetype
                | exp
    '''
    global PilaO,QUADSlist,HASHofoperatorsinquads
    result = PilaO.pop() # GET THE OPERAND THAT IS GOIN TO WRITE
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['WRITE'],-1,-1,result)) # ADD THE WRITE QUADRUPLE

def p_WRITETYPE(p):
    '''
    writetype : STRING
            | CTECHAR
    '''
    global PilaO
    PilaO.append(p[1]) # STORE THAT OPERAND THAT IS WAITING AS A STRING OR CTECHAR

def p_MULWRITE(p): #MANAGE MULTIPLE VARIABLES TO WRITE
    '''
    mulwrite : COMMA neuralwrite mulwrite
            | empty
    '''



######--------------------- CONDITIONALS LOGIC SECTION ------------------------------######

########### IF AND ELSE ##################

def p_IFING(p):
    '''
    ifing : IF LEFTPAR exp neuralif THEN LEFTBR statutes RIGHTBR elsing
    '''
    global Pjumps, QUADSlist
    if Pjumps: #IF THER IS SOMETHING THERE
        endo = Pjumps.pop() # GET THAT VIRTUAL ADDRESS
        newQuad = QUADSlist[endo-1] # GET THE QUAD TO CHANGE PENDING ADDRESS
        newQuad.result = len(QUADSlist)+1 # THE RESULT STORES THE APPROPIATE ADDRESS

def p_ELSING(p): # CHECK IF THERE IS AN ELSE AND PROCESS THE STATUES IF SO
    '''
    elsing : neuralelse LEFTBR statutes RIGHTBR
            | empty
    '''

def p_NEURALELSE(p): # GETTING THE QUADRUPLE ADDED, TO GET THE GOTO FOR THE ELSE
    '''
    neuralelse : ELSE 
    '''
    global QUADSlist, Pjumps, HASHofoperatorsinquads
    if Pjumps:
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,-999))
        elseendo = Pjumps.pop() # GET THE ADDRESS FOR THE JUMP
        Pjumps.append(len(QUADSlist)) # ADD THE NUMVALUE TO BE JUMPED
        newQuad = QUADSlist[elseendo-1] # GET THE ADDRESS QUADRUPLE TO BE MODIFIED
        newQuad.result = len(QUADSlist) + 1 # STORES THE APPROPIATE ADDRESS
    
def p_NEURALIF(p): # THE NEURAL POINT THAT ADDS THE QUADRUPLE OF THE IF
    '''
    neuralif : RIGHTPAR
    '''
    global Pilatypes, PilaO,QUADSlist,Pjumps,HASHofoperatorsinquads
    if Pilatypes and PilaO: # DO WE HAVE VALUES TO WORK WITH?
        vartype = Pilatypes.pop()
        typechecker(vartype,'bool') # ONLY BOOLS ARE ALLOWED HERE IN THE DECISION 
        result = PilaO.pop()
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTOF'],result,-1,-99)) # THE QUADRUPLE, ADDRESS PENDING
        Pjumps.append(len(QUADSlist)) #  GET THE QUAD COUNTER OF THE JUMP APPENDED



########### WHILE ##################

def p_WHILING(p): # 
    '''
    whiling : neuralwhile LEFTPAR exp neuralwhile2 DO LEFTBR statutes RIGHTBR
    '''
    global Pjumps,QUADSlist,HASHofoperatorsinquads
    if Pjumps:
        endo = Pjumps.pop()
        starto = Pjumps.pop()
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,starto+1)) # SET THE GOTO QUAD WITH THE APPROPIATE ADDRESS
        newQuad =  QUADSlist[endo - 1]
        newQuad.result = len(QUADSlist) + 1 # STORE THE APPROPIATE ADDRESS
    
def p_NEURALWHILE(p): # NEURAL POINT TO GET THE STACK OF JUMPS WITH THE QUAD COUNTER
    '''
    neuralwhile : WHILE
    '''
    global Pjumps, QUADSlist
    Pjumps.append(len(QUADSlist)) # GET THAT QUAD COUNTER

def p_NEURALWHILE2(p): # NEURAL POINT CHECKING IF THE TYPE ACTUALLY WORKS, AND GET THE INITIAL GOTOF
    '''
    neuralwhile2 : RIGHTPAR
    '''
    global Pilatypes,PilaO,QUADSlist, Pjumps,HASHofoperatorsinquads
    if Pilatypes and PilaO: # DO WE HAVE VALS to WORK WITH?
        exptype = Pilatypes.pop()
        typechecker(exptype,'bool')
        result = PilaO.pop()
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTOF'],result,-1,-999)) # THE QUAD, PENDING THE ADDRESS FOR THE GOTOF
        Pjumps.append(len(QUADSlist)) #GET THE QUAD COUNTER STORED




########### FOR  ##################

def p_FORING(p): # THE LOGIC FOR THE FOR STATUTE
    '''
    foring : FOR neuralfor idarray EQUAL exp neuralfor2 exp neuralfor3 LEFTBR statutes RIGHTBR
    '''
    global INITIALVARINfor,Pjumps, QUADSlist,HASHofoperatorsinquads,Pilatypes,PilaO
    temporalint = getandsetVirtualAddrTemp('int') # GET OUR TEMPORAL ADDRESS 
    constant1addr = virtualaddrfetcher(1) # THE CONSTANT 1 address
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['+'],INITIALVARINfor,constant1addr,temporalint)) # THE ITERATION
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],temporalint,-1,INITIALVARINfor)) #CONTINUING ITERATION
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],temporalint,-1,PilaO[-1])) #THE QUADRUPLE GETTING THE OPERATOR STACK MODIFIED
    endo = Pjumps.pop() #GET THE COUNTER FOR THE ENDO
    starto = Pjumps.pop() # GET THE COUNTER FOR THE STARTO
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,starto)) # VALIDATE THE CONDOITION
    QUADSlist[endo - 1].result =  len(QUADSlist) + 1 # GET THAT PENDING QUADRUPLE WITH THE QUAD COUNTER
    operandcleaner =  PilaO.pop()
    typecleaner = Pilatypes.pop()

def p_NEURALFOR(p): # GET THE ID ADDRESS HANDLED FOR THE CONTROL VARIABLE
    '''
    neuralfor : ID
    '''
    global PilaO, Pilatypes
    virtualaddr = virtualaddrfetcher(p[1]) # THE VIRTUAL ADDRESS FOR THE VARIABLE WE ARE WORKING
    type =  getType(p[1]) # GET OUR TYPE FOR THE VAR WE ARE WORKING WITH
    PilaO.append(virtualaddr) # ADD TO THE STACK THE VIRTUAL ADDRESS WE ARE WORKING WITH
    Pilatypes.append(type)
    typechecker(type,'int') # ONLY INTS ENTER OUR FORS

def p_NEURALFOR2(p): #NEURALGIC POINT TO CHECK IF THE VALUE THAT IS FORING IS APPROPIATE
    '''
    neuralfor2 : TO
    '''
    global Pilatypes,INITIALVARINfor,PilaO,QUADSlist,HASHofoperatorsinquads
    typeexp = Pilatypes.pop()
    typechecker(typeexp,'int') # ONLY INTS FOR THIS FOR
    if PilaO: #NOT EMPTY
        exp = PilaO.pop()
        INITIALVARINfor = PilaO[-1] # THE INITIAL VARINFOR GOES FROM THE LAST OPERAND
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],exp,-1,INITIALVARINfor)) # THE QUADRUPLE FOR THE INITIAL FOR VAL

def p_NEURALFOR3(p): # NEURALGIC POINT FOR THE GOTOF, ACTUALLY CHECK THE CONDITION VALIDITY
    '''
    neuralfor3 : DO
    '''
    global Pilatypes,PilaO,INITIALVARINfor,FINALVARINfor,Pjumps,QUADSlist,HASHofoperatorsinquads
    if Pilatypes and PilaO: # DO WE HAVE VALUES TO WORK WITH
        typeexp = Pilatypes.pop()
        typechecker(typeexp,'int') #ONLY INTS CONTINUE IN THIS FOR
        exp =  PilaO.pop()
        FINALVARINfor = getandsetVirtualAddrTemp('int') #GET THE VIRTUAL ADDR FOR THE TEMP
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],exp,-1,FINALVARINfor))
        temporalbool = getandsetVirtualAddrTemp('bool') # GET THE THE VIRTUAL ADDR FOR THE BOOL
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['<'],INITIALVARINfor, FINALVARINfor,temporalbool))
        Pjumps.append(len(QUADSlist)) #QUAD COUNTER
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTOF'],temporalbool,-1,99))
        Pjumps.append(len(QUADSlist)) #QUAD COUNTER AGAIN








######--------------------- EXP (EXPRESION) LOGIC SECTION ------------------------------######
#FOLLOWING THE OPERATORS PRIORITY IN PYTHON STYLE

def p_EXP(p): 
    '''
    exp : andexp exp1
    '''
    p[0] = p[1] # SKIPPING

def p_EXP1(p):
    '''
    exp1 : OR exp
        | empty
    '''

def p_ANDEXP(p):
    '''
    andexp : boolexp andexp1
    '''
    p[0]= p[1] #SKIPPING

def p_ANDEXP1(p):
    '''
    andexp1 : neuraland andexp
            | empty
    '''

def p_NEURALAND(p):
    '''
    neuraland : AND
    '''
    global POper
    POper.append(p[1]) # GET THE AND OPERATOR


#### BOOLEAN TOKENS HANDLER AND QUADAND LOADER####
def p_BOOLEXP(p):
    '''
    boolexp : arithexp boolexp1
    '''
    global POper,PilaO,Pilatypes,QUADSlist #GENERATE THE AND QUADS
    if POper:
        if POper[-1] == 'and' :
            rightOperand = PilaO.pop()
            righttype =  Pilatypes.pop()
            leftOperand = PilaO.pop()
            lefttype = Pilatypes.pop()
            operator = POper.pop()
            resulttype = semantics.getType(lefttype,righttype,operator)
            if resulttype == 'ERROR':
                ERRORHANDLER("tiposdif")
            newvirtualaddr = getandsetVirtualAddrTemp(resulttype)
            QUADSlist.append(Quadruple(HASHofoperatorsinquads[operator],leftOperand,rightOperand,newvirtualaddr))
            PilaO.append(newvirtualaddr)
            Pilatypes.append(resulttype)
    
    p[0]=p[1] #SKIPPING

def p_BOOLEXP1(p):
    '''
    boolexp1 : neuralbool arithexp
            | empty
    '''

def p_NEURALBOOL(p):
    '''
    neuralbool : GREATER
                | GREATERAND
                | LESSER
                | LESSERAND
                | SAME
                | NOTSAME
                | NOT
    '''
    global POper
    POper.append(p[1]) # ADD THE TOKEN THAT WE HAVE IDENTIFIED AS A BOOLEAN OPERATOR





#### ARITHMETIC TOKENS HANDLER AND QUADBOOL LOADER####

def p_ARITHEXP(p):
    '''
    arithexp : geoexp arithexp1
    '''
    global POper, PilaO,Pilatypes,QUADSlist,HASHofoperatorsinquads
    boolopers = ['>','>=', '<','<=','==','<>']
    if POper :
        if POper[-1] in boolopers: # MAKING THE QUAD THIS BOOLEAN OPERATORS
            rightOperand = PilaO.pop()
            righttype =  Pilatypes.pop()
            leftOperand = PilaO.pop()
            lefttype = Pilatypes.pop()
            operator = POper.pop()
            resulttype = semantics.getType(lefttype,righttype,operator)
            if resulttype == 'ERROR':
                ERRORHANDLER("tiposdif")
            newvirtualaddr = getandsetVirtualAddrTemp(resulttype)
            
            QUADSlist.append(Quadruple(HASHofoperatorsinquads[operator],leftOperand,rightOperand,newvirtualaddr))
            PilaO.append(newvirtualaddr)
            Pilatypes.append(resulttype)
    p[0] = p[1] #SKIPPING

def p_ARITHEXP1(p):
    '''
    arithexp1 : neuralarith arithexp
                | empty
    '''

def p_NEURALARITH(p): # SUM AND SUBSTRACTING SYMBOLS ADDED
    '''
    neuralarith : PLUS
                | REST
    '''
    global POper
    POper.append(p[1])


#### GEOMETRIC TOKENS HANDLER AND QUADARITH LOADER####

def p_GEOEXP(p):
    '''
    geoexp : finexp geoexp1
    '''
    global POper,PilaO,Pilatypes,QUADSlist,HASHofoperatorsinquads
    if len(POper) > 0:
        if POper[-1] == '+' or POper[-1] == '-': #GENERATE ARITH QUADS
            rightOperand = PilaO.pop()
            righttype =  Pilatypes.pop()
            leftOperand = PilaO.pop()
            lefttype = Pilatypes.pop()
            operator = POper.pop()
            resulttype = semantics.getType(lefttype,righttype,operator)
            if resulttype == 'ERROR':
                ERRORHANDLER("tiposdif")
            newvirtualaddr = getandsetVirtualAddrTemp(resulttype)
            QUADSlist.append(Quadruple(HASHofoperatorsinquads[operator],leftOperand,rightOperand,newvirtualaddr))
            PilaO.append(newvirtualaddr)
            Pilatypes.append(resulttype)
        p[0] = p[1]

def p_GEOEXP1(p):
    '''
    geoexp1 : neuralgeo geoexp
            | empty
    '''

def p_NEURALGEO(p): # THE TOKEN HANDLER FOR GEOMETRICS
    '''
    neuralgeo : TIMES
            | DIVIDE
    '''
    global POper
    POper.append(p[1])


# PARENTHESIS LOGICS WITH FALSE BOTTOMS

def p_ADDBOTTOM(p):
    '''
    addbottom : LEFTPAR
    '''
    global POper
    POper.append('~~~') ## ADD FALSE BOTTOM

def p_POPBOTTOM(p):
    '''
    popbottom : RIGHTPAR
    '''
    global POper
    POper.pop() #GET RID OF FALSE BOTTOM

def p_FINEXP(p):
    '''
    finexp : addbottom exp popbottom
            | cteexp
    '''
    global PilaO,POper,Pilatypes,QUADSlist,HASHofoperatorsinquads,CONSTANTSvar_set
    if len(p) == 2:
        virtualaddr = virtualaddrfetcher(p[1]) #IF NOT FUNCTION CALL, DEAL WITH VECTOR
        if not virtualaddr >= 27000 and virtualaddr < 30000:
            PilaO.append(virtualaddr)
            Pilatypes.append(getValtype(p[1]))
        if isarraymethod(p[1]):
            debug = PilaO.pop()
        p[0] = p[1]
    if len(p) == 3: # DEAL WITH THE FUNCTION CALLS
        newvirtualadrr = virtualaddrfetcher(p[1])
        PilaO.append(newvirtualadrr)
        Pilatypes.append(getValtype(p[1]))
        p[0] = p[1]
    if len(POper) > 0: # GENERATE THE ARITH QUADS
        if POper[-1] =='*' or POper[-1]=='/':
            rightOperand = PilaO.pop()
            righttype =  Pilatypes.pop()
            leftOperand = PilaO.pop()
            lefttype = Pilatypes.pop()
            operator = POper.pop()
            resulttype = semantics.getType(lefttype,righttype,operator)
            if resulttype == 'ERROR':
                ERRORHANDLER("tiposdif")
            newvirtualaddr = getandsetVirtualAddrTemp(resulttype)
            QUADSlist.append(Quadruple(HASHofoperatorsinquads[operator],leftOperand,rightOperand,newvirtualaddr))
            PilaO.append(newvirtualaddr)
            Pilatypes.append(resulttype)
# HANDLING ALL THE ABOVE BETWEEN PARENTHESES, VECTORS



### CONSTANT EXP HANDLING

def p_CTEEXP(p): # HANDLE THE CONSTANTS
    '''
    cteexp : CTEINT
            | CTEFLOAT
            | CTECHAR
            | ID neuralexist paramsexp
    '''
    global CONSTANTSvar_set, PilaO
    if len(p) == 2:
        if not p[1] in CONSTANTSvar_set: # IF THIS CONSTANT ISNT ALREADY SAVED, SAVE IT
            CONSTANTSvar_set[p[1]] = getandsetVirtualAddrCTE(p[1])
    p[0]=p[1] #SKIPPING


def p_NEURALEXIST(p): # CHECK IF THE ID ACTUALLY EXISTS
    '''
    neuralexist : 
    '''
    existencesensor(p[-1])
    POper.append("~~~") # FAKE BOTTOM
    p[0] = p[-1]


### EXPRESION CONSTANT AND FUNCTION CALLS

def p_PARAMSEXP(p):
    '''
    paramsexp : LEFTPAR neuralera paramsexp2 neuralpar
            | idarray
    '''

def p_PARAMSEXP2(p):
    '''
    paramsexp2 : exp neuralpar2 mulparamsexp
                | empty 
    '''

def p_NEURALPAR(p):
    '''
    neuralpar : RIGHTPAR
    '''
    global QUADSlist,HASHofoperatorsinquads,TABLEof_functions
    global GLOBALvar_set,CURRENTfunctionname,PilaO,POper,Pilatypes
    #global CONTPARAMETERSlist, PARAMETERSTABLElist
    POper.pop()
    id = p[-4]
    #auxparam = CONTPARAMETERSlist.pop()
    #if len(PARAMETERSTABLElist) != auxparam:
    #    ERRORHANDLER("invalidnumparams")
    startaddr = TABLEof_functions[id]['Initialfuncpoint']
    funcvirtaddr = GLOBALvar_set[id]['virtualaddress']
    functiontype = GLOBALvar_set[id]['type']
    temporal =getandsetVirtualAddrTemp(functiontype)
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOSUB'],id,-1,startaddr))
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],funcvirtaddr,-1,temporal))
    PilaO.append(temporal)
    Pilatypes.append(functiontype)

def p_NEURALERA(p):
    '''
    neuralera : 
    '''
    global QUADSlist,HASHofoperatorsinquads,TABLEof_functions,POper,CONTPARAMETERSlist
    global PilaO, Pilatypes ,PARAMETERSTABLElist,THEPARAMETERSset
    POper.append("~~~")
    id =(p[-3]) #FUNCTION ID
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['ERA'],-1,-1,id)) 
    CONTPARAMETERSlist.append(0)


def p_NEURALPAR2(p):
    '''
    neuralpar2 :
    '''
    global PARAMSINTcounter,PARAMSFLOATcounter,PARAMSCHARcounter,PARAMETERSTABLElist
    global PilaO,Pilatypes,QUADSlist,HASHofoperatorsinquads, PARAMETERSQUEUElist,CONTPARAMETERSlist
    if PilaO and Pilatypes and PARAMETERSTABLElist:
        argument = PilaO.pop()
        argumentype = Pilatypes.pop()
        paramaux =CONTPARAMETERSlist.pop()
        if argumentype!= PARAMETERSTABLElist[paramaux]:
            ERRORHANDLER("tiposdif")
        if argumentype == 'int':
            PARAMSINTcounter +=1
            QUADSlist.append(Quadruple(HASHofoperatorsinquads['PARAM'],argument,-1,PARAMETERSQUEUElist[paramaux]))
        elif argumentype == 'float':
            PARAMSINTcounter +=1
            QUADSlist.append(Quadruple(HASHofoperatorsinquads['PARAM'],argument,-1,PARAMETERSQUEUElist[paramaux]))
        elif argumentype == 'char':
            PARAMSINTcounter +=1
            QUADSlist.append(Quadruple(HASHofoperatorsinquads['PARAM'],argument,-1,PARAMETERSQUEUElist[paramaux]))
        CONTPARAMETERSlist.append(paramaux+1)
    else:
        if len(PARAMETERSTABLElist)!= CONTPARAMETERSlist:
            ERRORHANDLER("functionwithparamhuh",p[-1])


def p_MULPARAMSEXP(p): #HANDLING MULTIPLE PARAMETER DECLARATION
    '''
    mulparamsexp : COMMA exp neuralpar2 mulparamsexp
                | empty
    '''


####EXCEPTIONS HANDLING#####

def p_empty(p):
    '''
    empty : 
    '''     
    pass  

def p_error(p):
    print ("Syntax Error in '%s'" % p.value)
    print (p)
    sys.exit()


##ALTERNATIVE FILEHANDLER

import ply.yacc as yacc
parser = yacc.yacc()
f = open("./"+arch , "r")
input = f.read()
parser.parse(input, debug=0)
output = open("Quads.mir", "w")
for x in QUADSlist:
    output.write(str(x.QUADcounter)+ "~" + str(x.operator) + "~" + str(x.LeftOperand)+ "~" + str(x.RightOperand) + "~" + str(x.result) + "\n")
output.close()