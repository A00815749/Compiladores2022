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


def typechecker(type1,type2): # CHEKCIK IF OUR TYPES ARE ACTUALLY THE SAME, USED IN ASSIGNING, CYCLES AND LOOPS
    if type1 != type2:
        ERRORHANDLER("tiposdif",str(type1 + " ====== " + type2))


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
    #### AUXILIAR insert in the table function###
    QUADSlist.append(Quadruple(HASHofoperatorsinquads['GOTO'],-1,-1,-999))
    Pjumps.append(len(QUADSlist))
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
    ### AUXILIAR NEURAL FUNCTION to GET AND SET THE VIRTUAL ADDRESS
    # AUXILIAR FUNCTION TO INSERT IN VARTABLE


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
    ### LOGIC IN PROGRESS.....


def p_NEURALINITDIM(p): # MAKE THE STORED VARIABLE VECTOR HAVE AN ARRAYSENSOR SET TO TRUE
    '''
    neuralinitdim : LEFTSQR
    '''
    ### LOGIC IN PROGRESS.....


#DIMENSIONAL ACCESS HANDLER
def p_IDARRAY(p):
    '''
    idarray : neuralinitarray exp verify RIGHTSQR
            | empty
    '''

def p_NEURALINITARRAT(p):
    '''
    neuralinitarray : LEFTSQR
    '''


def p_VERIFY(p):
    '''
    verify : 
    '''




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
    newaddr = 0 #_____AUXILIAR FUNCTIONS OF VIRTUALADDRES
    GLOBALvar_set[CURRENTfunctionname]={'virtualaddress': newaddr, 'type' : CURRENTtype} # SAVE THE FUNCTION NAME AS A GLOBAL VARIABLE AS SEEN IN CLASS
    #_______AUXILIAR FUNCTION TO INSERT IN FUNCTION TABLE


def p_FUNCPARAM(p): #GRAMMAR LOGIC TO GET ALL PARAMETERS AND NEURALGIC POINTS RELATING TO FUNCTIONS MAINTENANCE
    '''
    funcparam : LEFTPAR parameters RIGHTPAR SEMICOLON varsgl LEFTBR neuralinitfuncs statutes RIGHTBR neuralfuncsize neuralendfuncs functions
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
    #### AUXILIAR TO RESET THE LOCAL AND TEMPORAL VARIABLES

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
        leftype = Pilatypes.pop()
        #Auxiliar typechecker cubo semantico
        QUADSlist.append(Quadruple(HASHofoperatorsinquads['='],result,-1,leftop))

def p_NEURALASSIGN(p):
    '''
    neuralassign : ID
    '''
    global PilaO,Pilatypes
    p[0]=p[1] #SKIPPING
    virtualaddr = 0 #FUNCION AUXILIAR PARA EL VIRTUALADDRES p[1]
    PilaO.append(virtualaddr)
    Pilatypes.append('placeholder') # FUNCION AUXILIAR PARA AGREGAR TIPO DE VALOR

def p_NEURALASSIGN2(p):
    '''
    neuralassign2 : =
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