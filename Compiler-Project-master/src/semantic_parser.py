import argparse
import re
import sys
from collections import OrderedDict
import pickle
import ply.lex as lex
import ply.yacc as yacc

gcounter, out_ir, out_st = 0, None, None

struct_count = 0
if_count = 0
elif_count = 0
for_count = 0
switch_count = 0
default_count = 0
lab_count = 0
str_count = 0
cur_symtab, cur_offset, cur_activation = [], [], []
func_offset = []
array_info = {}

# used for 3ac
set_of_activation = {}
string_map = {}
# used for 3ac

case_count = 0
addr_compiler_count = 0
const_compiler_count = 0
r_compiler_count = 0


class activation_record:
    def __init__(self, previous=None):
        self.previous = previous
        self.label = "global"
        self.total = 0
        self.ret_value_addr = None
        self.data = {}


class symtab:
    def __init__(self, previous=None):
        self.previous = previous
        self.label = "global"
        self.data = {}
        self.children = {}
        self.total = 0
        self.typedef_map = {}
        self.label_map = []
        self.struct_name_map = {}
        if previous is not None:
            self.typedef_map = previous.typedef_map.copy()
            self.label_map += previous.label_map
            self.struct_name_map = previous.struct_name_map.copy()


class structtab:
    def __init__(self, previous=None):
        self.label = 'struct'
        self.data = OrderedDict()
        self.total = 0
        self.typedef_map = {}
        self.struct_name_map = {}
        if previous is not None:
            self.typedef_map = previous.typedef_map.copy()
            self.struct_name_map = previous.struct_name_map.copy()


class values:
    def __init__(self, type=None, width=0, offset=None, args=None, place=None, args_width=None):
        self.type = type
        self.offset = offset
        self.width = width
        self.args = args
        self.place = place
        self.args_width = args_width


def lookup_top(table, id):
    if table is None:
        return None
    for key, val in table.data.items():
        if key == id:
            return val
    return lookup_top(table.previous, id)


def lookup(table, id):
    # print type(table)

    if table is None:
        return None

    return next((val for key, val in table.data.items() if key == id), None)


def is_float(type1, table):
    type2 = first_nontypedef(type1, table)
    if len(type2) == 1 and type2[0] >= 13 and type2[0] <= 14:
        return 1
    else:
        return 0

# def find_basic_type(type1, table):
#     if len(type1) == 1:
#         return type1[0]
#     elif type1[0] >= 1 and type1[0] <= 4:
#         return None
#     else:
#         return find_basic_type(table.typedef_map[type1[1]]["type"], table)

# def remove_typedef(type1,table):
#     if len(type1) == 0:
#         return -1
#     if type1[0] ==2 or type1[0] == 3 or type1[0] ==4:
#         return type1[0]
#     elif type1[0] == 1:
#         return -1
#     else:
#         return 1


def first_nontypedef(type1, table):
    if len(type1) == 0:
        return type1
    elif type1[0] != 5:
        return type1
    else:
        return first_nontypedef(table.typedef_map[type1[1]]["type"], table)


def check_type_struct(type1, type2, table):
    if len(type1) != len(type2):
        return 0
    if len(type1) == 1:
        return type1[0] == type2[0]
    elif type1[0] == 5 and type2[0] == 5:
        return type1[1] == type2[1]
    elif type1[0] == 3 and type2[0] == 3:
        return check_eq(type1[1], type2[1], table)
    elif type1[0] == 2 and type2[0] == 2:
        if type1[1] == type2[1]:
            return check_type_struct(type1[2:], type2[2:], table)
    elif type1[0] == type2[0]:
        return check_type_struct(type1[2:], type2[2:], table)
    return False


def check_eq(name1, name2, table):
    sym1 = table.struct_name_map[name1].data
    sym2 = table.struct_name_map[name2].data
    if len(sym1) != len(sym2):
        return False
    l1 = sym1.keys()
    l2 = sym2.keys()
    for i in range(0, len(sym1)):
        if l1[i] != l2[i]:
            return False
        if not (check_type_struct(sym1[l1[i]].type, sym2[l2[i]].type, table)):
            return False
    return True


def check_type(type1, type2, table):
    if len(type1) == 0 and len(type2) == 0:
        return 1
    if len(type1) == 0 or len(type2) == 0:
        return 0
    if type1[0] != 5 and type2[0] != 5:
        if len(type1) == 1 and len(type2) == 1:
            return type1[0] == type2[0]
        if len(type1) == 1 or len(type2) == 1:
            return 0
        if type1[0] == 3 and type2[0] == 3:
            return check_eq(type1[1], type2[1], table)
        elif type1[0] == 2 and type2[0] == 2:
            if type1[1] == type2[1]:
                return check_type(type1[2:], type2[2:], table)
            else:
                return 0
        elif type1[0] == 1 and type2[0] == 1:
            return check_type(type1[2:], type2[2:], table)
        elif type1[0] == 4 and type2[0] == 4:
            return check_type(type1[1:], type2[1:], table)
    elif type1[0] == 5:
        return check_type(table.typedef_map[type1[1]]["type"], type2, table)
    elif type2[0] == 5:
        return check_type(type1, table.typedef_map[type2[1]]["type"], table)


def address_generate_compilername(offset1=None, width=None, label=None, isf=0, isreg=-1):
    global addr_compiler_count
    addr_compiler_count += 1
    name = "var_" + str(addr_compiler_count)
    cur_activation[-1].data[name] = {"width": width, "label": label,
                                     "func_offset": offset1, "isf": isf, "isreg": isreg}
    return name


def generate_name():
    global struct_count
    struct_count += 1
    return "struct_" + str(struct_count)


def generate_ifname():
    global if_count
    if_count += 1
    return "if_" + str(if_count)


def generate_strname():
    global str_count
    str_count += 1
    return "msg_" + str(str_count)


def generate_label():
    global lab_count
    lab_count += 1
    return "lab_" + str(lab_count)


def generate_forname():
    global for_count
    for_count += 1
    return "for_" + str(for_count)


def generate_switchname():
    global switch_count
    switch_count += 1
    return "switch_" + str(switch_count)


def generate_casename():
    global case_count
    case_count += 1
    return "case_" + str(case_count)


def generate_defaultname():
    global default_count
    default_count += 1
    return "default_" + str(default_count)


def find_parentfunc(table):
    if table.label == "func":
        return table  # this case is not possible though
    return find_parentfunc(table.previous)


class Node:
    def __init__(self, type, children=None, leaf=None):
        self.type = type
        if children:
            self.children = children
        else:
            self.children = []
        self.leaf = leaf


def dfs(a, lcounter):
    global gcounter
    if a is not None:
        string = ""
        string = string + "a" + str(lcounter) + " [label=\"" + str(
            a.leaf["label"]) + "\"];\n"
        outfile.write(string)
        string = ""
        for x in a.children:
            if x is not None:
                string = string + "a" + str(lcounter) + " -> " + "a" + str(
                    gcounter + 1) + ";\n"
                outfile.write(string)
                string = ""
                gcounter += 1
                dfs(x, gcounter)


# def math_alwd(type1):
#     type2 = find_basic_type(type1, cur_symtab[-1])
#     if type2 is None:
#         return False
#     return math_alwd_dict[type2]

# def math_alwd_int(type1):
#     type2 = find_basic_type(type1, cur_symtab[-1])
#     if type2 is None:
#         return False
#     return type2>=3 and type2<=12

# def math_alwd_ext(type1):
#     type2 = find_basic_type(type1, cur_symtab[-1])
#     if type2 is None:
#         return False
#     return  (math_alwd_dict[type2] or type2==16)

# #THE FOLLOWING FUNCTIONS CHECK TYPE GIVEN THAT THEY ARE ABSOLUTE INT/FLOAT/STRINGS
# def is_type_int(type1):
#     if len(type1) != 1:
#         return False
#     return type1[0] >= 3 and type1[0] <= 12

# def is_type_float(type1):
#     if len(type1) != 1:
#         return False
#     return type1[0] >= 13 and type1[0] <= 14

# def is_type_string(type1):
#     if len(type1) != 1:
#         return False
#     return type1[0] == 16

# def implicit_cast(type1, type2):
#     assert (len(type1) == 1 and len(type2) == 1)
#     if type1[0] >= 3 and type1[0] <= 12 and type2[0] >= 3 and type2[0] <= 12:
#         return [type_map['int32']], 4
#     return [type_map['float64']], 8

type_map = {
    'bool': 1,
    'byte': 2,
    'int': 3,
    'uint8': 4,
    'uint16': 5,
    'uint32': 6,
    'uint64': 7,
    'int8': 8,
    'int16': 9,
    'int32': 10,
    'int64': 11,
    'uint': 12,
    'float64': 13,
    'float32': 14,
    'uintptr': 15,
    'string': 16,
    'error': 17,
}

type_width = {
    'bool': 4,
    'byte': 4,
    'int': 4,
    'uint8': 1,
    'uint16': 2,
    'uint32': 4,
    'uint64': 8,
    'int8': 1,
    'int16': 2,
    'int32': 4,
    'int64': 8,
    'uint': 4,
    'float32': 4,
    'float64': 8,
    'uintptr': 8,
    'string': 4,
    'error': 0,
}

math_alwd_dict = {
    type_map['bool']: False,
    type_map['byte']: False,
    type_map['int']: True,
    type_map['uint8']: True,
    type_map['uint16']: True,
    type_map['uint32']: True,
    type_map['uint64']: True,
    type_map['int8']: True,
    type_map['int16']: True,
    type_map['int32']: True,
    type_map['int64']: True,
    type_map['uint']: True,
    type_map['float32']: True,
    type_map['float64']: True,
    type_map['uintptr']: True,
    type_map['string']: False,
    type_map['error']: False
}

# PointerType-1
# ArrayType-2
# StructType-3
# Typedef check-5

reserved = {
    'break': 'BREAK',
    'default': 'DEFAULT',
    'func': 'FUNC',
    'interface': 'INTERFACE',
    'case': 'CASE',
    'defer': 'DEFER',
    'map': 'MAP',
    'struct': 'STRUCT',
    'else': 'ELSE',
    'goto': 'GOTO',
    'package': 'PACKAGE',
    'switch': 'SWITCH',
    'const': 'CONST',
    'fallthrough': 'FALLTHROUGH',
    'if': 'IF',
    'range': 'RANGE',
    'type': 'TYPE',
    'continue': 'CONTINUE',
    'for': 'FOR',
    'import': 'IMPORT',
    'return': 'RETURN',
    'var': 'VAR',
    'printInt': 'PRINTINT',
    'printFloat': 'PRINTFLOAT',
    'printStr': 'PRINTSTR',
    'scanInt': 'SCANINT',
    'scanStr': 'SCANSTR',
    'malloc': 'MALLOC',
    'openFile': 'OPENFILE',
    'readFile': 'READFILE',
    'writeFile': 'WRITEFILE',
    'closeFile': 'CLOSEFILE',
    'sin': 'SIN',
    'cos': 'COS',
    'null': 'NULL'
}

types = {
    'bool': 'BOOL',
    'byte': 'BYTE',
    'int': 'INT',
    'uint8': 'UINT8',
    'uint16': 'UINT16',
    'uint32': 'UINT32',
    'uint64': 'UINT64',
    'int8': 'INT8',
    'int16': 'INT16',
    'int32': 'INT32',
    'int64': 'INT64',
    'int': 'INT',
    'uint': 'UINT',
    'float32': 'FLOAT32',
    'float64': 'FLOAT64',
    'uintptr': 'UINTPTR',
    'string': 'STRING',
    'error': 'ERROR',
}

constants = {
    'true': 'TRUE',
    'false': 'FALSE',
    'iota': 'IOTA',
    'nil': 'NIL',
}

combined_map = dict(reserved, **dict(types, **constants))

tokens = [
    'LT',
    'GT',
    'LE',
    'GE',
    'EQ',
    'NE',
    'NOT',
    'LNOT',
    'LOR',
    'LAND',
    'PLUS',
    'MINUS',
    'TIMES',
    'DIVIDE',
    'MODULO',
    'OR',
    'XOR',
    'LSHIFT',
    'RSHIFT',
    'AND',
    'ANDNOT',
    'INCR',
    'DECR',
    'EQUALS',
    'TIMESEQUAL',
    'DIVEQUAL',
    'MODEQUAL',
    'PLUSEQUAL',
    'MINUSEQUAL',
    'LSHIFTEQUAL',
    'RSHIFTEQUAL',
    'ANDEQUAL',
    'OREQUAL',
    'XOREQUAL',
    'AUTOASIGN',
    'ANDNOTEQUAL',
    'ID',
    'LPAREN',
    'RPAREN',
    'LBRACKET',
    'RBRACKET',
    'LBRACE',
    'RBRACE',
    'COMMA',
    'PERIOD',
    'SEMI',
    'COLON',
    'ELLIPSIS',
    'CHARACTER',
    'INTEGER',
    'FLOAT',
    'STRINGVAL',
    'newline',
] + list(set(combined_map.values()))

t_LT = r'<'
t_GT = r'>'
t_LE = r'<='
t_GE = r'>='
t_EQ = r'=='
t_NE = r'!='
t_NOT = r'~'
t_LNOT = r'!'
t_LOR = r'\|\|'
t_LAND = r'&&'
t_PLUS = r'\+'
t_MINUS = r'\-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_MODULO = r'%'
t_OR = r'\|'
t_XOR = r'\^'
t_LSHIFT = r'<<'
t_RSHIFT = r'>>'
t_AND = r'&'
t_ANDNOT = r'&\^'
t_INCR = r'\+\+'
t_DECR = r'\-\-'
t_EQUALS = r'='
t_AUTOASIGN = r':='
t_TIMESEQUAL = r'\*='
t_DIVEQUAL = r'/='
t_MODEQUAL = r'%='
t_PLUSEQUAL = r'\+='
t_MINUSEQUAL = r'\-='
t_LSHIFTEQUAL = r'<<='
t_RSHIFTEQUAL = r'>>='
t_ANDEQUAL = r'&='
t_OREQUAL = r'\|='
t_XOREQUAL = r'\^='
t_ANDNOTEQUAL = r'&\^='
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACKET = r'\['
t_RBRACKET = r'\]'
t_LBRACE = r'\{'
t_RBRACE = r'\}'
t_COMMA = r'\,'
t_PERIOD = r'\.'
t_SEMI = r';'
t_COLON = r':'
t_ELLIPSIS = r'\.\.\.'
t_STRINGVAL = r'\"([^\\\n]|(\\.))*?\"'
t_CHARACTER = r'(L)?\'([^\\\n]|(\\.))*?\''
t_ignore = ' \t'


def t_FLOAT(t):
    r'(\d+\.\d*(e|E)[\+|\-]?\d+)|((\d+)(e|E)[\+|\-]?\d+)|(\.\d+(e|E)[\+|\-]?\d+)|(\d+\.\d*)|(\.\d+)'
    return t


def t_INTEGER(t):
    r'0[xX][0-9a-fA-F]+|\d+'
    return t


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = combined_map.get(t.value, 'ID')
    return t


def t_MULTICOMMENT(t):
    r'/\*(.|\n)*?\*/'
    t.lexer.lineno += t.value.count('\n')


def t_COMMENT(t):
    r'//.*\n'
    t.lexer.lineno += 1


def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    return t


def t_error(t):
    print("Illegal character '%s'" % str(t.value[0]))
    print("Value of the illegal token is '%s'" % str(t.value))
    t.lexer.skip(1)


def dump_st():
    for i in cur_symtab[-1].data:
        val = cur_symtab[-1].data[i]
        out_st.write(cur_symtab[-1].label + ',')
        out_st.write(i + ',')
        out_st.write(str(val.type) + ',')
        out_st.write(str(val.offset) + ',')
        out_st.write(str(val.width) + ',')
        out_st.write(str(val.args) + ',')
        out_st.write(str(val.place) + ',')
        out_st.write(str(cur_symtab[-1].typedef_map) + '\n')


def p_Start(p):
    '''
    Start : SourceFile
    '''
    # print "Succesfully completed."
    p[0] = p[1]
    dump_st()
    # print '-' * 40
    # print "main symtab"
    # print "symtab data:", cur_symtab[len(cur_symtab) - 1].data
    # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
    # print "total offset:", cur_offset[len(cur_offset) - 1]
    # print "typedef_map", cur_symtab[len(cur_symtab) - 1].typedef_map
    # print "struct_name_map", cur_symtab[len(cur_symtab) - 1].struct_name_map
    # print '-' * 40
    with open('code.pickle', 'wb') as handle:
        pickle.dump(p[0].leaf["code"], handle)
    for code in p[0].leaf["code"]:
        out_ir.write(','.join(map(lambda x: str(x).strip(), code)) + '\n')
    out_st.write('-' * 60 + '\n')
    out_st.write('tmp-label,offset,width\n')
    # for i in addr_3ac_offset:
    #     out_st.write(i + ',' + str(addr_3ac_offset[i][1]) + ',' + str(addr_3ac_offset[i][2]) + '\n')


def p_SourceFile(p):
    '''
    SourceFile : RepeatNewline PackageClause ImportClause A RepeatTopLevelDecl
    '''
    p[0] = Node("void", [p[2], p[3], p[5]], {"label": "Start"})
    p[0].leaf["code"] = p[5].leaf["code1"] + p[5].leaf["code2"]
    p[0].leaf["place"] = None
    cur_activation[-1].total = func_offset[-1]-4
    set_of_activation["global"] = cur_activation[-1]
    cur_activation.pop()


def p_A(p):
    '''
    A : empty
    '''
    cur_symtab.append(symtab())
    cur_offset.append(0)
    func_offset.append(4)
    cur_activation.append(activation_record())


def p_PackageClause(p):
    '''
    PackageClause : PACKAGE PackageName StatementEnd
    '''
    p[0] = Node("void", [Node("void", [], {"label": "package"}), p[2]],
                {"label": "PackageClause"})


def p_PackageName(p):
    '''
    PackageName : ID
    '''
    p[0] = Node("void", [], {"label": p[1]})


def p_ImportClause(p):
    '''
    ImportClause : ImportStmt StatementEnd ImportClause
                 | empty
    '''
    if len(p) == 2:
        p[0] = Node("void", [], {"label": "ImportClause"})
    else:
        p[0] = Node("void", [p[1]] + p[3].children, {"label": "ImportClause"})


def p_ImportStmt(p):
    '''
    ImportStmt : IMPORT Import
               | IMPORT LPAREN StatementEnd ImportList RPAREN
    '''
    if len(p) == 3:
        p[0] = Node("void", [Node("void", [], {"label": "import"}), p[2]],
                    {"label": "ImportStmt"})
    else:
        p[0] = Node("void",
                    [Node("void", [], {"label": "import"})] + p[4].children,
                    {"label": "ImportStmt"})


def p_ImportList(p):
    '''
    ImportList : Import StatementEnd ImportList
               | Import StatementEnd
               | Import
    '''
    if len(p) == 2:
        p[0] = Node("void", [p[1]], {"label": "Imports"})
    elif len(p) == 3:
        p[0] = Node("void", [p[1]], {"label": "Imports"})
    else:
        p[0] = Node("void", [p[1]] + p[3].children, {"label": "Imports"})


def p_Import(p):
    '''
    Import : ID STRINGVAL
           | STRINGVAL
    '''
    if len(p) == 3:
        p[0] = Node("void", [
            Node("void", [], {"label": p[1]}),
            Node("void", [], {"label": p[2][1:-1]})
        ], {"label": "Import"})
    else:
        p[0] = Node("void", [
            Node("void", [], {"label": ""}),
            Node("void", [], {"label": p[1][1:-1]})
        ], {"label": "Import"})


def p_RepeatTopLevelDecl(p):
    '''
    RepeatTopLevelDecl : TopLevelDecl StatementEnd RepeatTopLevelDecl
                       | TopLevelDecl
                       | empty
    '''
    if len(p) == 2:
        if p[1]:
            if p[1] != 'definition':
                p[0] = Node("void", [p[1]], {"label": "Declarations"})
                p[0].leaf["label"] = p[1].leaf["label"]
                if p[0].leaf["label"] == "Declaration":
                    p[0].leaf["code1"] = p[1].leaf["code"]
                    p[0].leaf["code2"] = []
                else:
                    p[0].leaf["code2"] = p[1].leaf["code"]
                    p[0].leaf["code1"] = []

                p[0].leaf["place"] = p[1].leaf["place"]
            else:
                p[0] = p[1]

        else:
            p[0] = Node("void", [], {
                "label": "empty",
                "code1": [],
                "code2": [],
                "place": None
            })
    if len(p) == 4:
        p[3].children = [p[1]] + p[3].children
        if p[1] != 'definition':
            if p[1].leaf["label"] == "Declaration":
                p[3].leaf["code1"] = p[1].leaf["code"] + p[3].leaf["code1"]
            else:
                p[3].leaf["code2"] = p[1].leaf["code"] + p[3].leaf["code2"]

        p[3].leaf["place"] = None
        p[0] = p[3]


def p_TopLevelDecl(p):
    '''
    TopLevelDecl : Declaration
                 | FunctionDecl
    '''
    p[0] = p[1]


def p_StatementList(p):
    '''
    StatementList : Statement StatementEnd StatementList
                  | Statement
                  | empty
    '''
    if len(p) == 2:
        if p[1]:
            p[1].leaf["label"] = "StatementList"
            p[0] = p[1]
        else:
            p[0] = Node("void", [], {
                "label": "StatementList",
                "code": [],
                "place": None
            })
    if len(p) == 4:
        p[3].children = [p[1]] + p[3].children
        p[3].leaf["code"] = p[1].leaf["code"] + p[3].leaf["code"]
        p[0] = p[3]


def p_Statement(p):
    '''
    Statement : Declaration
              | LabeledStmt
              | SimpleStmt
              | ReturnStmt
              | BreakStmt
              | ContinueStmt
              | FallthroughStmt
              | GotoStmt
              | Block
              | IfStmt
              | SwitchStmt
              | ForStmt
              | DeferStmt
              | PrintStmt
              | ScanIntStmt
              | ScanStrStmt
    '''
    p[1].leaf["label"] = "Statement"
    p[0] = p[1]


# Declaration   = ConstDecl | TypeDecl | VarDecl .
def p_Declaration(p):
    '''
    Declaration : ConstDecl
                | TypeDecl
                | VarDecl
    '''
    p[1].leaf["label"] = "Declaration"
    p[0] = p[1]


# ConstDecl = "const" ( ConstSpec | "(" { ConstSpec ";" } ")" ) .
def p_ConstDecl(p):
    '''
    ConstDecl : CONST ConstSpec
    '''
    p[2].leaf["label"] = "ConstDecl"
    p[2].children = [Node("void", [], {"label": "const"})] + p[2].children
    p[0] = p[2]


# ConstSpec = IdentifierList [ [ Type ] "=" ExpressionList ] .
def p_ConstSpec(p):
    '''
    ConstSpec : IdentifierList Types
              | IdentifierList Types EQUALS ExpressionList
    '''
    if len(p) == 3:
        p[0] = Node("void", [p[1], p[2]], {"label": "ConstSpec"})
        p[0].leaf["code"] = []
        p[0].leaf["place"] = None
        for child in p[1].children:
            t = lookup(cur_symtab[len(cur_symtab) - 1], child.leaf["label"])
            if t is None:
                # 3AC-code
                type1 = first_nontypedef(
                    p[2].children[0].leaf["type"], cur_symtab[-1])

                if type1[0] == 2 or (type1[0] == 3 and len(type1) % 2 == 0):
                    tmp_name = address_generate_compilername(
                        func_offset[-1], 0, cur_activation[-1].label, 0)
                    func_offset[-1] += p[2].children[0].leaf['width']
                else:
                    isf = is_float(p[2].children[0].leaf["type"])
                    tmp_name = address_generate_compilername(
                        func_offset[-1], p[2].children[0].leaf['width'], cur_activation[-1].label, isf)
                    func_offset[-1] += p[2].children[0].leaf['width']
                    p[0].leaf["code"] = []

                cur_symtab[-1].data[child.leaf["label"]] = values(
                    type=p[2].children[0].leaf["type"],
                    width=p[2].children[0].leaf["width"],
                    offset=cur_offset[-1],
                    place=tmp_name)

                # if type1[0]==3 and len(type1)%2==0:
                #     wi=cur_symtab[len(cur_symtab)-1].struct_name_map[type1[1]].total
                #     p[0].leaf["code"]+=[["assign",tmp_name,"malloc",wi]]
                # else:
                #     p[0].leaf["code"]+=[]

                p[0].leaf["place"] = None
                cur_offset[-1] += p[2].children[0].leaf["width"]
            else:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Redeclaration of " + str(
                        child.leaf["label"]) + " at line " + str(p.lineno(1)))
    else:
        p[0] = Node("void",
                    [p[1], Node("void", [], {"label": "="}), p[4]],
                    {"label": "ConstSpec"})
        len1 = len(p[1].children)
        len2 = len(p[4].children)
        if len1 != len2:
            print("[line:" + str(
                p.lineno(1)) + "]" + "Invalid number of Arguments")

        p[0].leaf["code"] = []
        p[0].leaf["place"] = None
        for ind in range(0, len1):
            t = lookup(cur_symtab[len(cur_symtab) - 1],
                       p[1].children[ind].leaf["label"])
            if t is None:

                width = p[4].children[ind].leaf["width"]
                type1 = first_nontypedef(p[2].children[0].leaf["type"],
                                         cur_symtab[-1])
                type2 = first_nontypedef(p[4].children[ind].leaf["type"],
                                         cur_symtab[-1])
                if check_type(type1, type2, cur_symtab[-1]) == False:
                    if len(type1) != 1 or len(type2) != 1:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Assignment not allowed for given type')
                        exit()
                    elif (type1[0] >= 3
                          and type1[0] <= 12) and (type2[0] >= 13
                                                   and type2[0] <= 14):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Not possible to assign float to int')
                        exit()
                    elif not ((type1[0] >= 3 and type1[0] <= 14) and
                              (type2[0] >= 3 and type2[0] <= 14)):
                        print(
                            "[line:" + str(p.lineno(1)) + "]" +
                            'Arithmetic operation not allowed for given type')
                        exit()
                    width = 4

                p[0].leaf["code"] += p[4].children[ind].leaf["code"]
                if type1[0] > 12 and type1[0] <= 14 and type2[0] <= 12:
                    t2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 1)
                    func_offset[-1] += 4
                    p[0].leaf['code'].append(
                        ['cast-float', t2, p[4].children[ind].leaf['place']])
                    p[4].children[ind].leaf['place'] = t2

                isf = is_float(p[2].children[0].leaf["type"], cur_symtab[-1])
                tmp_name = address_generate_compilername(
                    func_offset[-1], width, cur_activation[-1].label, isf)
                cur_symtab[-1].data[p[1].children[ind].leaf["label"]] = values(
                    type=p[2].children[0].leaf["type"],
                    width=width,
                    offset=cur_offset[-1],
                    place=tmp_name)
                cur_offset[-1] += width
                func_offset[-1] += width
                # 3AC-CODE
                p[0].leaf["place"] = None
                p[0].leaf["code"] += ([["=", tmp_name,
                                      p[4].children[ind].leaf["place"]]])
            else:
                print(("[line:" + str(
                    p.lineno(1)) + "]" + "Redeclaration of " + str(
                        p[1].children[ind].leaf["label"]) + " at line " + str(
                            p.lineno(1))))


# TypeDecl = "type" ( TypeSpec | "(" { TypeSpec ";" } ")" ) .
def p_TypeDecl(p):
    '''
    TypeDecl : TYPE RepeatNewline TypeSpec
    '''
    p[3].children = [Node("void", [], {"label": "type"})] + p[3].children
    p[0] = p[3]
    p[0].leaf["label"] = "TypeDecl"
    p[0].leaf["code"] = []
    p[0].leaf["place"] = None


# TypeSpec = AliasDecl | TypeDef
def p_TypeSpec(p):
    '''
    TypeSpec : TypeDef
    '''
    p[0] = p[1]
    p[0].leaf["label"] = "TypeSpec"


# TypeDef = identifier Type .
def p_TypeDef(p):
    '''
    TypeDef : ID K Types
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]}), p[3]],
                {"label": "TypeDef"})
    cur_symtab[-1].data[p[1]] = values(
        type=p[3].children[0].leaf["type"], width=0, offset=0)
    cur_symtab[-1].typedef_map[p[1]] = {
        "type": p[3].children[0].leaf["type"],
        "width": p[3].children[0].leaf["width"]
    }


def p_K(p):
    '''
    K : empty
    '''
    t = lookup(cur_symtab[-1], p[-1])
    if t is None:
        cur_symtab[-1].data[p[-1]] = values(type=[], width=0, offset=0)
        cur_symtab[-1].typedef_map[p[-1]] = {
            "type": [],
            "width": 0,
        }
    else:
        print("[line:" + str(p.lineno(-1)) + "]" +
              "Redeclaration of " + p[-1] + " at line " + str(p.lineno(-1)))
        exit()


#  VarDecl     = "var" ( VarSpec | "(" { VarSpec ";" } ")" ) .
#  VarSpec = IdentifierList ( Type [ "=" ExpressionList ] | "=" ExpressionList )
def p_VarDecl(p):
    '''
    VarDecl : VAR RepeatNewline VarSpec
    '''
    p[3].children = [Node("void", [], {"label": "var"})] + p[3].children
    p[0] = p[3]


def p_VarSpec(p):
    '''
    VarSpec : IdentifierList Types
            | IdentifierList Types EQUALS RepeatNewline ExpressionList
    '''
    if len(p) == 3:
        p[0] = Node("void", [p[1], p[2]], {"label": "VarSpec"})
        p[0].leaf["code"] = []
        p[0].leaf["place"] = None
        for child in p[1].children:
            t = lookup(cur_symtab[len(cur_symtab) - 1], child.leaf["label"])
            if t is None:
                # 3AC-code
                type1 = first_nontypedef(
                    p[2].children[0].leaf["type"], cur_symtab[-1])

                if type1[0] == 2 or (type1[0] == 3 and len(type1) % 2 == 0):
                    tmp_name = address_generate_compilername(
                        func_offset[-1], 0, cur_activation[-1].label, 0)
                    func_offset[-1] += p[2].children[0].leaf['width']
                else:
                    isf = is_float(
                        p[2].children[0].leaf["type"], cur_symtab[-1])
                    tmp_name = address_generate_compilername(
                        func_offset[-1], p[2].children[0].leaf['width'], cur_activation[-1].label, isf)
                    func_offset[-1] += p[2].children[0].leaf['width']
                    p[0].leaf["code"] = []

                cur_symtab[-1].data[child.leaf["label"]] = values(
                    type=p[2].children[0].leaf["type"],
                    width=p[2].children[0].leaf["width"],
                    offset=cur_offset[-1],
                    place=tmp_name)

                # if type1[0]==3 and len(type1)%2==0:
                #     wi=cur_symtab[len(cur_symtab)-1].struct_name_map[type1[1]].total
                #     p[0].leaf["code"]+=[["assign",tmp_name,"malloc",wi]]
                # else:
                #     p[0].leaf["code"]+=[]

                p[0].leaf["place"] = None
                cur_offset[-1] += p[2].children[0].leaf["width"]

            else:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Redeclaration of " + str(
                        child.leaf["label"]) + " at line " + str(p.lineno(1)))
                exit()
    else:
        p[0] = Node("void",
                    [p[1], Node("void", [], {"label": "="}), p[5]],
                    {"label": "VarSpec"})
        len1 = len(p[1].children)
        len2 = len(p[5].children)
        width = 0
        if len1 != len2:
            print("[line:" + str(
                p.lineno(1)) + "]" + "Invalid number of Arguments")

        p[0].leaf["code"] = []
        p[0].leaf["place"] = None

        for ind in range(0, len1):
            t = lookup(cur_symtab[len(cur_symtab) - 1],
                       p[1].children[ind].leaf["label"])
            if t is None:
                width = p[5].children[ind].leaf["width"]
                type1 = first_nontypedef(p[2].children[0].leaf["type"],
                                         cur_symtab[-1])
                type2 = first_nontypedef(p[5].children[ind].leaf["type"],
                                         cur_symtab[-1])
                if check_type(type1, type2, cur_symtab[-1]) == False:
                    if len(type1) != 1 or len(type2) != 1:
                        print(
                            "[line:" + str(p.lineno(1)) + "]" +
                            'Arithmetic operation not allowed for given type')
                        exit()
                    elif (type1[0] >= 3
                          and type1[0] <= 12) and (type2[0] >= 13
                                                   and type2[0] <= 14):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Not possible to assign float to int')
                        exit()
                    elif not ((type1[0] >= 3 and type1[0] <= 14) and
                              (type2[0] >= 3 and type2[0] <= 14)):
                        print(
                            "[line:" + str(p.lineno(1)) + "]" +
                            'Arithmetic operation not allowed for given type')
                        exit()
                    width = 4

                p[0].leaf["code"] += p[5].children[ind].leaf["code"]
                if type1[0] > 12 and type1[0] <= 14 and type2[0] <= 12:
                    t2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 1)
                    func_offset[-1] += 4
                    p[0].leaf['code'].append(
                        ['cast-float', t2, p[5].children[ind].leaf['place']])
                    p[5].children[ind].leaf['place'] = t2

                isf = is_float(p[2].children[0].leaf["type"], cur_symtab[-1])
                tmp_name = address_generate_compilername(
                    func_offset[-1], width, cur_activation[-1].label, isf)
                cur_symtab[-1].data[p[1].children[ind].leaf["label"]] = values(
                    type=p[2].children[0].leaf["type"],
                    width=width,
                    offset=cur_offset[-1],
                    place=tmp_name)
                cur_offset[-1] += width
                func_offset[-1] += width
                # 3AC-CODE
                p[0].leaf["place"] = None
                p[0].leaf["code"] += ([["=", tmp_name,
                                      p[5].children[ind].leaf["place"]]])
            else:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Redeclaration of " + str(
                        p[1].children[ind].leaf["label"]) + " at line " + str(
                            p.lineno(1)))
                exit()


# FunctionDecl = "func" FunctionName Signature [ FunctionBody ] .
# FunctionName = identifier .
# FunctionBody = Block .
def p_FunctionDecl(p):
    '''
    FunctionDecl : FunctionMarker  FunctionBody
                 | FunctionMarker
    '''

    # print "-" * 40
    # print "function symtab"
    # print "symtab data:"
    # for key, val in cur_symtab[-1].data.items():
    #     print key, "-->", val.type
    # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
    # print "total offset:", cur_offset[len(cur_offset) - 1]
    # print "-" * 40
    if len(p) == 3:
        top = cur_symtab[-1]
        top.total = cur_offset[-1]
        dump_st()
        cur_activation[-1].total = func_offset[-1]-4
        set_of_activation[cur_symtab[-1].label_map[0]] = cur_activation[-1]
        cur_symtab.pop()
        cur_offset.pop()
        func_offset.pop()

        cur_activation.pop()
        # t = lookup(cur_symtab[-1], p[1].children[1].leaf["label"])
        p[2].leaf["label"] = "FunctionBody"
        p[1].children = p[1].children + [p[2]]
        p[1].leaf["label"] = "Function"
        p[0] = p[1]
        p[0].leaf["label"] = "FunctionDecl"
        p[0].leaf["code"] = [[p[1].children[1].leaf["label"], ":"]]
        p[0].leaf["code"] += p[2].leaf["code"]
        if p[1].children[1].leaf["label"] == "main":
            p[0].leaf["code"] += [["returnm"]]
        else:
            p[0].leaf["code"] += [["return"]]
        p[0].leaf["place"] = None
    else:
        cur_symtab.pop()
        cur_offset.pop()
        cur_activation.pop()
        func_offset.pop()
        p[0] = 'definition'


def p_FunctionMarker(p):
    '''
    FunctionMarker : FUNC RepeatNewline FunctionName Signature
    '''

    p[0] = Node("void",
                [Node("void", [], {"label": "func"}), p[3]] + p[4].children,
                {"label": "marker"})
    t = lookup(cur_symtab[-2], p[0].children[1].leaf["label"])
    if t is None:
        cur_symtab[-2].data[p[0].children[1].leaf["label"]] = values(
            type=p[0].children[3].leaf["type"],
            offset=cur_offset[-2],
            width=p[0].children[3].leaf["width"],
            args=p[0].children[2].leaf["type"],
            args_width=p[0].children[2].leaf["width"])

        cur_offset[-2] += p[0].children[3].leaf["width"]
        cur_symtab[-1].label_map.insert(0, p[3].leaf["label"])
    else:
        if t.args is None:
            print("[line:" + str(p.lineno(1)) + "]" + "Redeclaration of " + str(
                p[3].leaf["label"]) + " at line " + str(p.lineno(1)))
            exit()
        else:
            # print t.type
            # print p[0].children[3].leaf["type"]
            if check_type(t.type, p[0].children[3].leaf["type"], cur_symtab[-2]) == True and len(t.args) == len(p[0].children[2].leaf["type"]):
                for x in range(0, len(t.args)):
                    if check_type(t.args[x], p[0].children[2].leaf["type"][x], cur_symtab[-2]) == 0:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              "Function does not align with definition at line " + str(p.lineno(1)))
                        exit()
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      "Function does not align with definition at line " + str(p.lineno(1)))
                exit()
            cur_symtab[-1].label_map.insert(0, p[3].leaf["label"])


def p_FunctionName(p):
    '''
    FunctionName : ID
    '''
    p[0] = Node("void", [], {"label": p[1]})
    t_new = symtab(cur_symtab[len(cur_symtab) - 1])
    a_new = activation_record(cur_activation[-1])
    a_new.label = p[1]
    t_new.label = "func"
    cur_symtab[len(cur_symtab) - 1].children[p[1]] = t_new
    cur_symtab.append(t_new)
    cur_offset.append(0)
    func_offset.append(4)
    cur_activation.append(a_new)


# Didn't include variadic functions, it is defined by ... below
#  Signature      = Parameters [ Result ] .
#  Result         = Parameters | Type .
#  Parameters     = "(" [ ParameterList [ "," ] ] ")" .
#  ParameterList  = ParameterDecl { "," ParameterDecl } .
#  ParameterDecl = [ IdentifierList ] [ "..." ] Type .


def p_Signature(p):
    '''
    Signature : Parameters
              | Parameters Result
    '''
    if len(p) == 2:
        p[0] = Node("void", [
            p[1],
            Node("void", [], {
                "label": "Result",
                "type": [],
                "width": 0
            })
        ], {"label": "Signature"})
    else:
        p[0] = Node("void", [p[1], p[2]], {"label": "Signature"})
    running_offset = -4  # frame pointer
    for i in reversed(range(0, len(p[1].leaf["list"]))):
        running_offset -= p[1].leaf["width"][i]
        cur_symtab[-1].data[p[1].leaf["list"][i]].offset = running_offset
        cur_activation[-1].data[cur_symtab[-1].data[p[1].leaf["list"]
                                                    [i]].place]["func_offset"] = running_offset
    cur_activation[-1].ret_value_addr = running_offset-4


# Parameters can't end in ,
def p_Parameters(p):
    '''
    Parameters : LPAREN RepeatNewline RPAREN
               | LPAREN RepeatNewline ParameterList RPAREN
    '''
    if len(p) == 4:
        p[0] = Node("void", [
            Node("void", [], {"label": "("}),
            Node("void", [], {"label": ")"})
        ], {
            "label": "Arguments",
            "type": [],
            "width": [0],
            "list": []
        })
    else:
        p[0] = Node("void", p[3].children, {
            "label": "Arguments",
            "type": p[3].leaf["type"],
            "width": p[3].leaf["width"],
            "list": p[3].leaf["label"]
        })


def p_ParameterList(p):
    '''
    ParameterList : ParameterDecl RepeatParameterDecl
    '''
    p[2].children = [p[1]] + p[2].children
    p[2].leaf["type"].insert(0, p[1].leaf["type"])
    p[2].leaf["width"].insert(0, p[1].leaf["width"])
    p[2].leaf["label"].insert(0, p[1].leaf["label"])
    p[0] = p[2]


def p_RepeatParameterDecl(p):
    '''
    RepeatParameterDecl : COMMA RepeatNewline ParameterDecl RepeatParameterDecl
                        | empty
    '''
    if len(p) == 2:
        p[0] = Node("void", [], {"label": [], "type": [], "width": []})
    else:
        p[4].children = [p[3]] + p[4].children
        p[0] = p[4]
        p[0].leaf["type"].insert(0, p[3].leaf["type"])
        p[0].leaf["width"].insert(0, p[3].leaf["width"])
        p[0].leaf["label"].insert(0, p[3].leaf["label"])


def p_ParameterDecl(p):
    '''
    ParameterDecl : ID Types
                  | Types
    '''
    if len(p) == 3:

        t = lookup(cur_symtab[len(cur_symtab) - 1], p[1])
        if t is None:
            type1 = first_nontypedef(
                p[2].children[0].leaf["type"], cur_symtab[-1])
            if type1[0] == 2 or type1[0] == 3 and len(type1) % 2 == 0:
                temp_name = address_generate_compilername(
                    cur_offset[-1], 4, cur_activation[-1].label, 0)
                wi = 4
            else:
                isf = is_float(p[2].children[0].leaf["type"], cur_symtab[-1])
                temp_name = address_generate_compilername(
                    cur_offset[-1], p[2].children[0].leaf["width"], cur_activation[-1].label, isf)
                wi = p[2].children[0].leaf["width"]

            cur_symtab[len(cur_symtab) - 1].data[p[1]] = values(
                type=p[2].children[0].leaf["type"],
                width=p[2].children[0].leaf["width"],
                offset=cur_offset[-1],
                place=temp_name)
            p[0] = Node(
                "void", p[2].children[0].children, {
                    "label": p[1],
                    "type": p[2].children[0].leaf["type"],
                    "width": wi
                })
        else:
            print("[line:" + str(
                p.lineno(1)) + "]" + "Redeclaration of " + str(
                    child.leaf["label"]) + " at line " + str(p.lineno(1)))
    else:
        p[0] = Node(
            "void", p[1].children[0].children, {
                "label": str(p[1].children[0].leaf["label"]),
                "type": p[1].children[0].leaf["type"]
            })


def p_Result(p):
    '''
    Result :  Types
    '''
    p[0] = p[1]
    if p[1].leaf['label'] == 'Types':
        p[0].leaf["type"] = p[1].leaf["type"]
    p[1].leaf["label"] = "Return Values"
    p[0].leaf["width"] = p[1].leaf["width"]


def p_FunctionBody(p):
    '''
    FunctionBody : Block
    '''
    p[0] = p[1]


# LabeledStmt = Label ":" Statement .
# Label       = identifier .
def p_LabeledStmt(p):
    '''
    LabeledStmt : Label COLON RepeatNewline Statement
    '''
    p[0] = Node("void", p[1].children + [p[4]], {"label": "LabeledStmt"})
    if (p[1].children[0].leaf["label"] in cur_symtab[-1].label_map):
        print("[line:" + str(
            p.lineno(1)) + "]" + "Label " + p[1].children[0].leaf["label"] +
            " redeclared at line no: " + str(p.lineno(1)) + "\n")
        exit()
    else:
        cur_symtab[-1].label_map.append(p[1].children[0].leaf["label"])
        p[0].leaf["code"] = [['label', p[1].children[0].leaf["label"]]
                             ] + p[4].leaf["code"]
        p[0].leaf["place"] = None


def p_Label(p):
    '''
    Label : ID
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "Label"})


# SimpleStmt = EmptyStmt | ExpressionStmt | SendStmt | IncDecStmt | Assignment | ShortVarDecl .
# EmptyStmt = .
# ExpressionStmt = Expression .
# IncDecStmt = Expression ( "++" | "--" ) .
# Assignment = ExpressionList assign_op ExpressionList .
# assign_op = [ add_op | mul_op ] "=" .
# ShortVarDecl = IdentifierList ":=" ExpressionList .
def p_SimpleStmt(p):
    '''
    SimpleStmt : Assignment
               | ShortVarDecl
               | IncDecStmt
               | ExpressionStmt
    '''
    p[0] = p[1]
    p[0].leaf["label"] = "SimpleStmt"


def p_ExpressionStmt(p):
    '''
    ExpressionStmt : Expression
    '''
    p[0] = p[1]
    p[0].leaf["label"] = "ExpressionStmt"
    if "statement" not in p[1].leaf:
        print("Only function Callings can be Expression Statements.Error at lineno " + str(
            p.lineno(1)))
        exit()


def p_IncDecStmt(p):
    '''
    IncDecStmt : Expression INCR
               | Expression DECR
    '''
    p[0] = Node("void", [p[1]] + [Node("void", [], {"label": p[2]})],
                {"label": "IncDecStmt"})
    if "marked" not in p[1].children[0].leaf:
        print("Increment/Decrement allowed only to Identifiers.Error at lineno " + str(
            p.lineno(1)))
        exit()
    type1 = p[1].leaf["type"]
    bas = first_nontypedef(type1, cur_symtab[-1])
    if len(bas) != 1 or not (bas[0] >= 3 and bas[0] <= 14):
        print("[line:" + str(p.lineno(1)) + "]" +
              'Increment only allowed for numeric types')
        exit()

    tmp_name = address_generate_compilername(
        func_offset[-1], 4, cur_activation[-1].label, 0)
    func_offset[-1] += 4
    if p[2] == "++":
        p[0].leaf["code"] = p[1].leaf["code"] + [[
            "=", tmp_name, 1
        ], ["+", p[1].leaf["place"], p[1].leaf["place"], tmp_name]]
    else:
        p[0].leaf["code"] = p[1].leaf["code"] + [[
            "=", tmp_name, 1
        ], ["-", p[1].leaf["place"], p[1].leaf["place"], tmp_name]]


def p_AssignOp(p):
    '''
    AssignOp : TIMESEQUAL
             | DIVEQUAL
             | MODEQUAL
             | PLUSEQUAL
             | MINUSEQUAL
             | LSHIFTEQUAL
             | RSHIFTEQUAL
             | ANDEQUAL
             | OREQUAL
             | XOREQUAL
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "AssignOp"})


def p_Assignments(p):
    '''
    Assignment : ExpressionList AssignOp RepeatNewline ExpressionList
               | ExpressionList EQUALS RepeatNewline ExpressionList
               | ExpressionList EQUALS MallocExp
               | ExpressionList EQUALS SinExp
               | ExpressionList EQUALS CosExp
               | ExpressionList EQUALS OpenFileExp
               | ReadFileExp
               | WriteFileExp
               | CloseFileExp
               | ExpressionList EQUALS NULL

    '''
    if len(p) == 4:
        if p[3] == 'null':
            p[0] = Node("void",
                        [p[1], Node("void", [], {"label": p[2]}), p[3]],
                        {"label": "Assignment"})
            p[0].leaf["place"] = None
            len1 = len(p[1].children)
            if len1 != 1:
                print("Malloc allowed on only 1 id at a time " + str(p.lineno(1)))
                exit()
            if "marked" not in p[1].children[0].children[0].leaf:
                print("Assignment allowed only to Identifiers.Error at lineno " + str(
                    p.lineno(1)))
                exit()
            p[0].leaf["code"] = [["=", p[1].children[0].leaf["place"], 0]]
        elif p[3].leaf["label"] == 'malloc':
            p[0] = Node("void",
                        [p[1], Node("void", [], {"label": p[2]}), p[3]],
                        {"label": "Assignment"})
            p[0].leaf["place"] = None
            len1 = len(p[1].children)
            if len1 != 1:
                print("Malloc allowed on only 1 id at a time " + str(p.lineno(1)))
                exit()
            if "marked" not in p[1].children[0].children[0].leaf:
                print(
                    "Assignment allowed only to Identifiers. Error at lineno " + str(p.lineno(1)))
                exit()
            p[0].leaf["code"] = p[1].leaf["code"]+p[3].leaf["code"] + \
                [["malloc", p[1].children[0].leaf["place"], p[3].leaf["place"]]]
        elif p[3].leaf['label'] == 'openFile':
            p[0] = Node('void', [p[1], Node('void', [], {'label': p[2]}), p[3]], {
                        'label': 'Assignment'})
            p[0].leaf['place'] = None
            len1 = len(p[1].children)
            if len1 != 1:
                print("openFile allowed on only 1 id at a time " + str(p.lineno(1)))
                exit()
            if "marked" not in p[1].children[0].children[0].leaf:
                print(
                    "Assignment allowed only to Identifiers. Error at lineno " + str(p.lineno(1)))
                exit()
            p[0].leaf['code'] = p[1].leaf['code'] + p[3].leaf['code']
            p[0].leaf['code'].append(['openFile', p[1].children[0].leaf['place'], p[3].children[0].leaf['place'],
                                     p[3].children[1].leaf['place'], p[3].children[2].leaf['place']])
        elif p[3].leaf['label'] == 'sin':
            p[0] = Node('void', [p[1], Node('void', [], {'label': p[2]}), p[3]], {
                        'label': 'Assignment'})
            p[0].leaf['place'] = None
            len1 = len(p[1].children)
            if len1 != 1:
                print("sin allowed on only 1 id at a time " + str(p.lineno(1)))
                exit()
            if "marked" not in p[1].children[0].children[0].leaf:
                print(
                    "Assignment allowed only to Identifiers. Error at lineno " + str(p.lineno(1)))
                exit()
            p[0].leaf['code'] = p[1].leaf['code'] + p[3].leaf['code']
            p[0].leaf['code'].append(
                ['sin', p[1].children[0].leaf['place'], p[3].children[0].leaf['place']])
        elif p[3].leaf['label'] == 'cos':
            p[0] = Node('void', [p[1], Node('void', [], {'label': p[2]}), p[3]], {
                        'label': 'Assignment'})
            p[0].leaf['place'] = None
            len1 = len(p[1].children)
            if len1 != 1:
                print("cos allowed on only 1 id at a time " + str(p.lineno(1)))
                exit()
            if "marked" not in p[1].children[0].children[0].leaf:
                print(
                    "Assignment allowed only to Identifiers. Error at lineno " + str(p.lineno(1)))
                exit()
            p[0].leaf['code'] = p[1].leaf['code'] + p[3].leaf['code']
            p[0].leaf['code'].append(
                ['cos', p[1].children[0].leaf['place'], p[3].children[0].leaf['place']])
    elif len(p) == 2:
        if p[1].leaf['label'] == 'readFile':
            p[0] = Node('void', [p[1]], {'label': 'Assignment'})
            p[0].leaf['place'] = None
            p[0].leaf['code'] = p[1].leaf['code']
            p[0].leaf['code'].append(['readFile', p[1].children[0].leaf['place'],
                                     p[1].children[1].leaf['place'], p[1].children[2].leaf['place']])
        elif p[1].leaf['label'] == 'writeFile':
            p[0] = Node('void', [p[1]], {'label': 'Assignment'})
            p[0].leaf['place'] = None
            p[0].leaf['code'] = p[1].leaf['code']
            p[0].leaf['code'].append(['writeFile', p[1].children[0].leaf['place'],
                                     p[1].children[1].leaf['place'], p[1].children[2].leaf['place']])
        elif p[1].leaf['label'] == 'closeFile':
            p[0] = Node('void', [p[1]], {'label': 'Assignment'})
            p[0].leaf['place'] = None
            p[0].leaf['code'] = p[1].leaf['code']
            p[0].leaf['code'].append(
                ['closeFile', p[1].children[0].leaf['place']])
    else:
        len1 = len(p[1].children)
        len2 = len(p[4].children)
        if len1 != len2:
            print("Mismatch in number of arguments at lineno " + str(p.lineno(1)))
            exit()
        for ind in range(0, len1):
            if "marked" not in p[1].children[ind].children[0].leaf:
                print("Assignment allowed only to Identifiers.Error at lineno " + str(
                    p.lineno(1)))
                exit()

        if p[2] == "=":
            p[0] = Node("void",
                        [p[1], Node("void", [], {"label": p[2]}), p[4]],
                        {"label": "Assignment"})
            p[0].leaf["code"] = []
            p[0].leaf["place"] = None
            for ind in range(0, len1):
                type1 = first_nontypedef(p[1].children[ind].leaf["type"],
                                         cur_symtab[-1])
                type2 = first_nontypedef(p[4].children[ind].leaf["type"],
                                         cur_symtab[-1])
                if check_type(type1, type2, cur_symtab[-1]) == False:
                    if len(type1) != 1 or len(type2) != 1:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()
                    elif (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 13 and
                                                                 type2[0] <= 14):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Not possible to assign float to int')
                        exit()
                    elif not ((type1[0] >= 3 and type1[0] <= 14) and
                              (type2[0] >= 3 and type2[0] <= 14)):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()

                p[0].leaf["code"] += (p[1].children[ind].leaf["code"] +
                                      p[4].children[ind].leaf["code"])
                if type1[0] > 12 and type1[0] <= 14 and type2[0] <= 12:
                    t2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 1)
                    func_offset[-1] += 4
                    p[0].leaf['code'].append(
                        ['cast-float', t2, p[4].children[ind].leaf['place']])
                    p[4].children[ind].leaf['place'] = t2

                p[0].leaf["code"] += ([[
                    "=", p[1].children[ind].leaf["place"],
                    p[4].children[ind].leaf["place"]
                ]])
        else:

            p[0] = Node("void", [p[1], p[2].children[0], p[4]],
                        {"label": "AssignOp"})
            p[0].leaf["code"] = []
            p[0].leaf["place"] = None

            if p[2].children[0].leaf["label"] in [
                    "&=", "^=", "|=", ">>=", "<<=", "%="
            ]:
                for ind in range(0, len1):
                    type1 = first_nontypedef(p[1].children[ind].leaf["type"],
                                             cur_symtab[-1])
                    type2 = first_nontypedef(p[4].children[ind].leaf["type"],
                                             cur_symtab[-1])

                    if len(type1) != 1 or len(type2) != 1:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()
                    if not ((type1[0] >= 3 and type1[0] <= 12) and
                            (type2[0] >= 3 and type2[0] <= 12)):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()
                    p[0].leaf["code"] += (p[1].children[ind].leaf["code"] +
                                          p[4].children[ind].leaf["code"] + [[
                                              p[2].children[0].leaf["label"][0],
                                              p[1].children[ind].leaf["place"],
                                              p[1].children[ind].leaf["place"],
                                              p[4].children[ind].leaf["place"]
                                          ]])
                    p[0].leaf["place"] = None
            elif p[2].children[0].leaf["label"] in ["/=", "*=", "-="]:

                for ind in range(0, len1):
                    type1 = first_nontypedef(p[1].children[ind].leaf["type"],
                                             cur_symtab[-1])
                    type2 = first_nontypedef(p[4].children[ind].leaf["type"],
                                             cur_symtab[-1])

                    if len(type1) != 1 or len(type2) != 1:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()
                    elif (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 13 and
                                                                 type2[0] <= 14):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Not possible to assign float to int')
                        exit()
                    elif not ((type1[0] >= 3 and type1[0] <= 14) and
                              (type2[0] >= 3 and type2[0] <= 14)):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()

                    p[0].leaf['code'] = p[1].children[ind].leaf['code'] + \
                        p[4].children[ind].leaf['code']

                    operator = ""
                    if type1[0] > 12 and type1[0] <= 14 and type2[0] <= 12:
                        tmp_name = address_generate_compilername(
                            func_offset[-1], 4, cur_activation[-1].label, 1)
                        func_offset[-1] += 4
                        p[0].leaf['code'].append(
                            ['cast-float', t2, p[4].children[ind].leaf['place']])
                        p[4].children[ind].leaf['place'] = t2
                        operator = p[2].children[0].leaf["label"][0] + "float"
                    elif type1[0] >= 12:
                        operator = p[2].children[0].leaf["label"][0] + "float"
                    else:
                        operator = p[2].children[0].leaf["label"][0] + "int"

                    p[0].leaf["code"] += ([[
                        operator,
                        p[1].children[ind].leaf["place"],
                        p[1].children[ind].leaf["place"],
                        p[4].children[ind].leaf["place"]
                    ]])
                    p[0].leaf["place"] = None

            elif p[2].children[0].leaf["label"] == "+=":
                for ind in range(0, len1):
                    type1 = first_nontypedef(p[1].children[ind].leaf["type"],
                                             cur_symtab[-1])
                    type2 = first_nontypedef(p[4].children[ind].leaf["type"],
                                             cur_symtab[-1])

                    if len(type1) != 1 or len(type2) != 1:
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Arithmetic operation not allowed for given type')
                        exit()
                    elif (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 13 and
                                                                 type2[0] <= 14):
                        print("[line:" + str(p.lineno(1)) + "]" +
                              'Not possible to assign float to int')
                        exit()
                    elif not (type1[0] == 16 and type2[0] == 16):
                        if not ((type1[0] >= 3 and type1[0] <= 14) and
                                (type2[0] >= 3 and type2[0] <= 14)):
                            print(
                                "[line:" + str(p.lineno(1)) + "]" +
                                'Arithmetic operation not allowed for given type')
                            exit()

                    p[0].leaf['code'] += p[1].children[ind].leaf['code'] + \
                        p[4].children[ind].leaf['code']
                    operator = ""
                    if type1[0] > 12 and type1[0] <= 14 and type2[0] <= 12:
                        t2 = address_generate_compilername(
                            func_offset[-1], 4, cur_activation[-1].label, 1)
                        func_offset[-1] += 4
                        p[0].leaf['code'].append(
                            ['cast-float', t2, p[4].children[ind].leaf['place']])
                        p[4].children[ind].leaf['place'] = t2
                        operator = p[2].children[0].leaf["label"][0] + "float"
                    elif type1[0] >= 12 and type1[0] <= 14:
                        operator = p[2].children[0].leaf["label"][0] + "float"
                    elif type1[0] == 16:
                        operator = p[2].children[0].leaf["label"][0] + "string"
                    else:
                        operator = p[2].children[0].leaf["label"][0] + "int"

                    p[0].leaf["code"] += ([[
                        operator,
                        p[1].children[ind].leaf["place"],
                        p[1].children[ind].leaf["place"],
                        p[4].children[ind].leaf["place"]
                    ]])
                    p[0].leaf["place"] = None

            else:
                print("ERROR NOT POSSIBLE IN ASSIGNMENT CASE")
                exit()


def p_ShortVarDecl(p):
    '''
    ShortVarDecl : ID AUTOASIGN RepeatNewline Expression
    '''
    p[0] = Node("void", [
        Node("void", [], {"label": p[1]}),
        Node("void", [], {"label": p[2]}), p[4]
    ], {"label": "Assignment"})

    t = lookup(cur_symtab[-1], p[1])
    if t is None:
        isf = is_float(p[4].children[0].leaf["type"], cur_symtab[-1])
        tmp_name = address_generate_compilername(
            func_offset[-1], p[4].children[0].leaf["width"], cur_activation[-1].label, isf)
        cur_symtab[-1].data[p[1]] = values(
            type=p[4].children[0].leaf["type"],
            offset=cur_offset[-1],
            width=p[4].children[0].leaf["width"],
            place=tmp_name)
        cur_offset[-1] += p[4].children[0].leaf["width"]
        func_offset[-1] += p[4].children[0].leaf["width"]
        p[0].leaf["place"] = None
        p[0].leaf["code"] = (p[4].leaf["code"] +
                             [["=", tmp_name, p[4].leaf["place"]]])
    else:
        print("Variable already declared.Error at lineno " + str(p.lineno(1)))
        exit()


def p_ReturnStmt(p):
    '''
    ReturnStmt : RETURN
               | RETURN ExpressionList
    '''
    top = cur_symtab[-1]
    while (top.label not in ["func", "global"]):
        top = top.previous
    if (top.label == "global"):
        print("[line:" + str(
            p.lineno(1)
        ) + "]" + "Return statement should be inside function", p.lineno(1))
        exit()
    func = top.label_map[0]
    top = top.previous
    ret_type = top.data[func].type
    if len(p) == 2:
        if len(ret_type) != 0:
            print("[line:" + str(
                p.lineno(1)) + "]" + "No return expression given but expected")
            exit()
        p[0] = Node("void", [Node("void", [], {"label": "return"})],
                    {"label": "ReturnStmt"})
        if func == "main":
            p[0].leaf["code"] = [["returnm"]]
        else:
            p[0].leaf["code"] = [["return"]]

        p[0].leaf["place"] = None
    else:
        if len(p[2].leaf["type"]) != 1:
            print("[line:" + str(
                p.lineno(1)) + "]" + "Only a single return type allowed")
            exit()
        if check_type(p[2].leaf["type"][0], ret_type, cur_symtab[-1]) == False:
            print("[line:" + str(p.lineno(1)) + "]" + "Wrong Return Type")
            exit()
        p[0] = Node("void", [Node("void", [], {"label": "return"}), p[2]],
                    {"label": "ReturnStmt"})
        if func == "main":
            p[0].leaf["code"] = p[2].leaf["code"] + [[
                "returnm", p[2].leaf["place"][0]
            ]]
        else:
            p[0].leaf["code"] = p[2].leaf["code"] + [[
                "return", p[2].leaf["place"][0]
            ]]
        p[0].leaf["place"] = None


def p_FallthroughStmt(p):
    '''
    FallthroughStmt : FALLTHROUGH
    '''
    p[0] = Node("void", [Node("void", [], {"label": "fallthrough"})],
                {"label": "FallthroughStmt"})


def p_BreakStmt(p):
    '''
    BreakStmt : BREAK
              | BREAK Label
    '''
    top = cur_symtab[len(cur_symtab) - 1]
    while (top.label in ["if", "else", "elif"]):
        top = top.previous

    if (top.label not in ["for", "case", "default"]):
        print("[line:" + str(
            p.lineno(1)
        ) + "]" + "Break is not inside inside switch or for at ", p.lineno(1))
        exit()

    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": "break"})],
                    {"label": "BreakStmt"})
        p[0].leaf["code"] = [["goto ", top.label_map[0] + ".next"]]

    else:
        p[0] = Node("void",
                    [Node("void", [], {"label": "break"}), p[2].children[0]],
                    {"label": "BreakStmt"})


def p_ContinueStmt(p):
    '''
    ContinueStmt : CONTINUE
                 | CONTINUE Label
    '''
    top = cur_symtab[len(cur_symtab) - 1]
    while (top.label in ["if", "else", "elif"]):
        top = top.previous

    if (top.label != "for"):
        print("[line:" + str(p.lineno(
            1)) + "]" + "Continue is not inside for loop at ", p.lineno(1))

    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": "continue"})],
                    {"label": "ContinueStmt"})
        p[0].leaf["code"] = [["goto ", top.label_map[0] + ".post"]]

    else:
        p[0] = Node(
            "void",
            [Node("void", [], {"label": "continue"}), p[2].children[0]],
            {"label": "ContinueStmt"})


def p_GotoStmt(p):
    '''
    GotoStmt : GOTO Label
    '''
    p[0] = Node("void",
                [Node("void", [], {"label": "goto"}), p[2].children[0]],
                {"label": "GotoStmt"})
    if (p[2].children[0].leaf["label"] not in cur_symtab[len(cur_symtab) -
                                                         1].label_map):
        print("[line:" + str(p.lineno(1)) + "]" + "Label: " +
              p[2].children[0].leaf["label"] + " undefined at line no: " + str(
                  p.lineno(1)) + "\n")
        exit()


def p_Block(p):
    '''
    Block : LBRACE RepeatNewline  StatementList RBRACE
    '''
    p[0] = Node("void", [p[3]], {"label": "Block"})
    p[0].leaf["code"] = p[3].leaf["code"]
    p[0].leaf["place"] = p[3].leaf["place"]


def p_IfExp(p):
    '''
    IfExp : IfMarker RepeatNewline Expression
    '''
    type1 = p[3].leaf["type"]
    bas = first_nontypedef(type1, cur_symtab[-1])
    if (len(bas) != 1) or (bas[0] != 1):
        print("[line:" + str(p.lineno(1)) + "]" +
              'Expression not of type Boolean ')
        exit()
    p[0] = Node("void", [p[1], p[3]], {"label": "If_Expression"})

    # IR Code
    name = p[1].leaf["label"]
    p[0].leaf["code"] = p[3].leaf["code"] + [[
        "iffalse ", p[3].leaf["place"], " goto ", name + ".false"
    ]]
    p[0].leaf["place"] = None
    p[0].leaf["label"] = name

    if p[-2] == "else":
        p[0].leaf["next"] = p[-5].leaf["next"]
    else:
        p[0].leaf["next"] = name + ".next"


def p_IfStmt(p):
    '''
    IfStmt : IF IfExp Block
           | IF IfExp Block EndIfMarker ELSE ElseMarker Block
           | IF IfExp Block EndIfMarker ELSE IfStmt
    '''
    global elif_count

    if len(p) == 4:

        p[0] = Node(
            "void",
            [Node("void", [], {"label": "if"}), p[2].children[1], p[3]],
            {"label": "IfStmt"})
        dump_st()
        # print "-" * 40
        # print "End of symtabl ", cur_symtab[len(cur_symtab) - 1].label
        # print "symtab data:", cur_symtab[len(cur_symtab) - 1].data
        # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
        # print "total offset:", cur_offset[len(cur_offset) - 1]
        # print "-" * 40

        top = cur_symtab[len(cur_symtab) - 1]
        top.total = cur_offset[len(cur_offset) - 1]
        cur_symtab.pop()
        cur_offset.pop()

        # elif_count = 0
        p[0].leaf["code"] = p[2].leaf["code"] + p[3].leaf["code"] + [[
            p[2].leaf["label"] + ".false", ":"
        ]]
        p[0].leaf["place"] = None
        if p[-1] == "else":
            p[0].leaf["code"] += [[p[2].leaf["next"], ":"]]

    elif len(p) == 8:
        p[0] = Node("void", [
            Node("void", [], {"label": "if"}), p[2].children[1], p[3],
            Node("void", [], {"label": "else"}), p[7]
        ], {"label": "IfStmt"})

        # print "-" * 40
        # print "End of symtabl ", cur_symtab[len(cur_symtab) - 1].label
        # print "symtab data:", cur_symtab[len(cur_symtab) - 1].data
        # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
        # print "total offset:", cur_offset[len(cur_offset) - 1]
        # print "-" * 40

        top = cur_symtab[len(cur_symtab) - 1]
        top.total = cur_offset[len(cur_offset) - 1]
        dump_st()
        cur_symtab.pop()
        cur_offset.pop()

        p[0].leaf["code"] = p[2].leaf["code"] + p[3].leaf["code"] + p[4].leaf[
            "code"] + p[6].leaf["code"] + p[7].leaf["code"] + [[
                p[2].leaf["next"], ": "
            ]]
        p[0].leaf["place"] = None

        # elif_count = a-zA-Z_0-9

    elif len(p) == 7:
        p[0] = Node("void", [
            Node("void", [], {"label": "if"}), p[2].children[1], p[3],
            Node("void", [], {"label": "else"}), p[6]
        ], {"label": "IfStmt"})

        p[0].leaf["code"] = p[2].leaf["code"] + p[3].leaf["code"] + p[4].leaf[
            "code"] + [[p[2].leaf["label"] + ".false", ":"]] + p[6].leaf["code"]
        p[0].leaf["place"] = None


def p_IfMarker(p):
    '''
    IfMarker : empty
    '''
    parent = find_parentfunc(cur_symtab[len(cur_symtab) - 1])
    tnew = symtab(cur_symtab[len(cur_symtab) - 1])
    tnew.label = "if"

    if p[-2] == "else":
        # name = p[-5].leaf["label"] + "_1"
        tnew.label = "elif"
        # p[0] = Node("void",[],{"label": name})

        # global elif_count
        # name = "elif_" + str(if_count) + "_" + str(elif_count)
        # elif_count += 1
        # tnew.label = "elif"

    # else:
    name = generate_ifname()
    p[0] = Node("void", [], {"label": name})
    parent.children[name] = tnew
    parent.data[name] = values()
    cur_symtab.append(tnew)
    cur_offset.append(0)


def p_EndIfMarker(p):
    '''
    EndIfMarker : empty
    '''

    top = cur_symtab[len(cur_symtab) - 1]
    top.total = cur_offset[len(cur_offset) - 1]

    dump_st()
    # print "-" * 40
    # print "End of symtabl ", cur_symtab[len(cur_symtab) - 1].label
    # print "symtab data:", cur_symtab[len(cur_symtab) - 1].data
    # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
    # print "total offset:", cur_offset[len(cur_offset) - 1]
    # print "-" * 40

    cur_symtab.pop()
    cur_offset.pop()
    p[0] = Node("void", [], {"label": "endif"})
    p[0].leaf["code"] = [["goto ", p[-2].leaf["next"]]]


def p_ElseMarker(p):
    '''
    ElseMarker : empty
    '''
    parent = find_parentfunc(cur_symtab[len(cur_symtab) - 1])
    tnew = symtab(cur_symtab[len(cur_symtab) - 1])
    name = "else_" + str(if_count)
    parent.children[name] = tnew
    parent.data[name] = values()
    tnew.label = "else"
    cur_symtab.append(tnew)
    cur_offset.append(0)
    p[0] = Node("void", [], {"label": "else"})

    p[0].leaf["code"] = [[p[-4].leaf["label"] + ".false", ":"]]


def p_SwitchStmt(p):
    '''
    SwitchStmt : ExprSwitchStmt
    '''
    p[0] = p[1]


def p_ExprSwitchStmt(p):
    '''
    ExprSwitchStmt : SWITCH RepeatNewline Expression LBRACE RepeatNewline Exp_Inh RepeatExprCaseClause RBRACE
    '''

    p[0] = Node("void", [Node("void", [], {"label": "switch"}), p[3], p[6]],
                {"label": "ExprSwitchStmt"})

    code = p[3].leaf["code"]
    code += p[7].leaf["code1"]
    code += [["goto ", p[6].leaf["label"] + ".next"]]
    code += p[7].leaf["code2"]
    code += [[p[6].leaf["label"] + ".next", ":"]]
    p[0].leaf["code"] = code


def p_Exp_Inh(p):
    '''
    Exp_Inh : empty
    '''
    t1 = generate_switchname()
    p[0] = Node("void", [], {"place": p[-3].leaf["place"], "label": t1})


def p_RepeatExprCaseClause(p):
    '''
    RepeatExprCaseClause : ExprCaseClause RepeatExprCaseClause
                         | empty
    '''
    if len(p) == 3:
        p[2].children = [p[1]] + p[2].children
        p[0] = p[2]
        if len(p[1].leaf["code1"]) == 1:
            if len(p[0].leaf["code1"]) == 0:
                p[0].leaf["code1"] = p[1].leaf["code1"] + p[0].leaf["code1"]
                p[0].leaf["code2"] = p[1].leaf["code2"] + p[0].leaf["code2"]
            elif p[0].leaf["code1"][-1][0] == "iftrue ":
                p[0].leaf["code1"] += p[1].leaf["code1"]
                p[0].leaf["code2"] = p[1].leaf["code2"] + p[0].leaf["code2"]
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Multiple Defaults not allowed')
                exit()

        else:
            p[0].leaf["code1"] = p[1].leaf["code1"] + p[0].leaf["code1"]
            p[0].leaf["code2"] = p[1].leaf["code2"] + p[0].leaf["code2"]

    else:
        p[0] = Node("void", [], {"label": "RepeatExprCaseClause"})
        p[0].leaf["code1"] = []
        p[0].leaf["code2"] = []


def p_ExprCaseClause(p):
    '''
    ExprCaseClause : ExprSwitchCase COLON RepeatNewline StatementList
    '''
    p[0] = Node("void", p[1].children + [p[4]], {
        "label": p[-1].leaf["label"],
        "place": p[-1].leaf["place"]
    })

    if "default" in p[1].leaf["label"]:
        code1 = [["goto ", p[1].leaf["label"]]]
        code2 = [[p[1].leaf["label"], ":"]] + p[4].leaf["code"]
    else:
        t1 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, 0)
        func_offset[-1] += 4
        code1 = p[1].leaf["code"] + [[
            "==", t1, p[-1].leaf["place"], p[1].leaf["place"]
        ], ["iftrue ", t1, "goto ", p[1].leaf["label"]]]
        code2 = [[p[1].leaf["label"], ":"]] + p[4].leaf["code"]
    p[0].leaf["code1"] = code1
    p[0].leaf["code2"] = code2

    top = cur_symtab[len(cur_symtab) - 1]
    top.total = cur_offset[len(cur_offset) - 1]
    cur_symtab.pop()
    cur_offset.pop()


def p_ExprSwitchCase(p):
    '''
    ExprSwitchCase : CASE CaseMarker RepeatNewline Expression
                   | DEFAULT  DefaultMarker RepeatNewline
    '''
    if len(p) == 4:
        p[0] = Node("void", [Node("void", [], {"label": "default"})],
                    {"label": p[2].leaf["label"]})
    else:
        p[0] = Node(
            "void", [Node("void", [], {"label": "case"}), p[4]], {
                "label": p[2].leaf["label"],
                "code": p[4].leaf["code"],
                "place": p[4].leaf["place"]
            })


def p_CaseMarker(p):
    '''
    CaseMarker : empty
    '''
    parent = find_parentfunc(cur_symtab[len(cur_symtab) - 1])
    tnew = symtab(cur_symtab[len(cur_symtab) - 1])
    name = generate_casename()
    parent.children[name] = tnew
    parent.data[name] = values()
    tnew.label_map.insert(0, p[-2].leaf["label"])
    tnew.label = "case"
    cur_symtab.append(tnew)
    cur_offset.append(0)
    p[0] = Node("void", [], {"label": name})


def p_DefaultMarker(p):
    '''
    DefaultMarker : empty
    '''
    parent = find_parentfunc(cur_symtab[len(cur_symtab) - 1])
    tnew = symtab(cur_symtab[len(cur_symtab) - 1])
    # name = "default_" + str(if_count)
    name = generate_defaultname()
    parent.children[name] = tnew
    parent.data[name] = values()
    tnew.label_map.insert(0, p[-2].leaf["label"])
    tnew.label = "default"
    cur_symtab.append(tnew)
    cur_offset.append(0)
    p[0] = Node("void", [], {"label": name})


def p_ForStmt(p):
    '''
    ForStmt : FOR ForMarker RepeatNewline Block
            | FOR ForMarker RepeatNewline Condition Block
            | FOR ForMarker RepeatNewline ForClause Block
    '''
    if len(p) == 5:
        p[0] = Node("void", [Node("void", [], {"label": "for"}), p[3]],
                    {"label": "ForStmt"})
        code = p[4].leaf["code"] + [["goto ", p[2].leaf["label"]]]

        p[0].leaf["code"] = [[p[2].leaf["label"], ":"]] + code

    else:
        p[0] = Node("void", [Node("void", [], {"label": "for"}), p[3], p[4]],
                    {"label": "ForStmt"})
        if p[4].leaf["label"] == "Condition":
            code = [[p[2].leaf["label"], ":"]] + p[4].leaf["code"]
            code += [[
                "iffalse ", p[4].leaf["place"], " goto ",
                p[2].leaf["label"] + ".next"
            ]]
            code += p[5].leaf["code"] + [["goto ", p[2].leaf["label"]]]
            code += [[p[2].leaf["label"] + ".next", ":"]]
            p[0].leaf["code"] = code
        else:
            code = p[4].leaf["code"][0] + [[p[2].leaf["label"], ":"]
                                           ] + p[4].leaf["code"][1]
            if p[4].leaf["place"] is not None:
                code += [[
                    "iffalse ", p[4].leaf["place"], "goto ",
                    p[2].leaf["label"] + ".next"
                ]]
            code += p[5].leaf["code"] + [[
                p[2].leaf["label"] + ".post", ":"]] + p[4].leaf["code"][2] + [["goto ", p[2].leaf["label"]]
                                                                              ] + [[p[2].leaf["label"] + ".next", ":"]]
            p[0].leaf["code"] = code
            p[0].leaf["label"] = None

    # print "-" * 40
    # print "End of symtabl ", cur_symtab[len(cur_symtab) - 1].label
    # print "symtab data:", cur_symtab[len(cur_symtab) - 1].data
    # print "symtab children:", cur_symtab[len(cur_symtab) - 1].children
    # print "total offset:", cur_offset[len(cur_offset) - 1]
    # print "-" * 40

    top = cur_symtab[len(cur_symtab) - 1]
    top.total = cur_offset[len(cur_offset) - 1]
    dump_st()
    cur_symtab.pop()
    cur_offset.pop()


def p_ForMarker(p):
    '''
    ForMarker : empty
    '''
    parent = find_parentfunc(cur_symtab[len(cur_symtab) - 1])
    tnew = symtab(cur_symtab[len(cur_symtab) - 1])
    name = generate_forname()
    parent.children[name] = tnew
    parent.data[name] = values()
    tnew.label = "for"
    tnew.label_map.insert(0, name)
    cur_symtab.append(tnew)
    cur_offset.append(0)
    p[0] = Node("void", [], {"label": name})


def p_ForClause(p):
    '''
    ForClause : terminator terminator
              | InitStmt terminator terminator
              | terminator Condition terminator
              | terminator terminator PostStmt
              | InitStmt terminator Condition terminator
              | InitStmt terminator terminator PostStmt
              | terminator Condition terminator PostStmt
              | InitStmt terminator Condition terminator PostStmt
    '''
    if len(p) == 3:
        p[0] = Node("void", [
            Node("void", [], {"label": "InitStmt"}),
            Node("void", [], {"label": "Condition"}),
            Node("void", [], {"label": "PostStmt"})
        ], {"label": "ForClause"})
        p[0].leaf["place"] = None
        p[0].leaf["code"] = [[], [], []]
    elif len(p) == 4:
        if p[2] == ";" and p[3] == ";":
            p[0] = Node("void", [
                p[1],
                Node("void", [], {"label": "Condition"}),
                Node("void", [], {"label": "PostStmt"})
            ], {"label": "ForClause"})
            p[0].leaf["place"] = None
            p[0].leaf["code"] = [p[1].leaf["code"], [], []]
        elif p[1] == ";" and p[3] == ";":
            p[0] = Node("void", [
                Node("void", [], {"label": "InitStmt"}), p[2],
                Node("void", [], {"label": "PostStmt"})
            ], {"label": "ForClause"})
            p[0].leaf["place"] = p[2].leaf["place"]
            p[0].leaf["code"] = [[], p[2].leaf["code"], []]
        else:
            p[0] = Node("void", [
                Node("void", [], {"label": "InitStmt"}),
                Node("void", [], {"label": "Condition"}), p[3]
            ], {"label": "ForClause"})
            p[0].leaf["place"] = None
            p[0].leaf["code"] = [[], [], p[3].leaf["code"]]

    elif len(p) == 5:
        if p[2] == ";" and p[4] == ";":
            p[0] = Node("void",
                        [p[1], p[3],
                         Node("void", [], {"label": "PostStmt"})],
                        {"label": "ForClause"})
            p[0].leaf["place"] = p[3].leaf["place"]
            p[0].leaf["code"] = [p[1].leaf["code"], p[3].leaf["code"], []]
        elif p[2] == ";" and p[3] == ";":
            p[0] = Node(
                "void",
                [p[1], Node("void", [], {"label": "Condition"}), p[4]],
                {"label": "ForClause"})
            p[0].leaf["place"] = None
            p[0].leaf["code"] = [p[1].leaf["code"], [], p[4].leaf["code"]]

        else:
            p[0] = Node("void",
                        [Node("void", [], {"label": "InitStmt"}), p[2], p[4]],
                        {"label": "ForClause"})
            p[0].leaf["place"] = p[2].leaf["place"]
            p[0].leaf["code"] = [[], p[2].leaf["code"], p[4].leaf["code"]]

    else:
        p[0] = Node("void", [p[1], p[3], p[5]], {"label": "ForClause"})
        p[0].leaf["place"] = p[3].leaf["place"]
        p[0].leaf["code"] = [
            p[1].leaf["code"], p[3].leaf["code"], p[5].leaf["code"]
        ]


def p_InitStmt(p):
    '''
    InitStmt : SimpleStmt
    '''
    p[1].leaf["label"] = "InitStmt"
    p[0] = p[1]


def p_PostStmt(p):
    '''
    PostStmt : SimpleStmt
    '''
    p[1].leaf["label"] = "PostStmt"
    p[0] = p[1]


def p_Condition(p):
    '''
    Condition : Expression
    '''
    p[1].leaf["label"] = "Condition"
    p[0] = p[1]
    type1 = p[1].leaf["type"]
    bas = first_nontypedef(type1, cur_symtab[-1])
    if (len(bas) != 1) or (bas[0] != 1):
        print("[line:" + str(p.lineno(1)) + "]" +
              'Expression not of type Boolean ')
        exit()


def p_DeferStmt(p):
    '''
    DeferStmt : DEFER PrimaryExpr Arguments
    '''
    p[0] = Node(
        "void",
        [Node("void", [], {"label": "defer"})] + p[2].children + [p[3]],
        {"label": "DeferStmt"})


def p_PrintStmt(p):
    '''
    PrintStmt : PrintIntStmt
              | PrintStrStmt
              | PrintFloatStmt
    '''
    p[0] = p[1]


def p_PrintIntStmt(p):
    '''
    PrintIntStmt : PRINTINT Expression
    '''
    p[0] = Node("void", [Node("void", [], {"label": "printInt"}), p[2]], {
                "label": "printInt", "code": p[2].leaf["code"]+[["printInt", p[2].leaf["place"]]]})


def p_PrintFloatStmt(p):
    '''
    PrintFloatStmt : PRINTFLOAT Expression
    '''
    p[0] = Node("void", [Node("void", [], {"label": "printFloat"}), p[2]], {
                "label": "printFloat", "code": p[2].leaf["code"]+[["printFloat", p[2].leaf["place"]]]})


def p_PrintStrStmt(p):
    '''
    PrintStrStmt : PRINTSTR Expression
    '''
    type1 = first_nontypedef(p[2].leaf['type'], cur_symtab[-1])
    if len(type1) != 1 and type1[0] != 16:
        print("[line:" + str(p.lineno(1)) + "]" +
              'Arithmetic operation not allowed for given type')
        exit()
    p[0] = Node("void", [Node("void", [], {"label": "printStr"}), p[2]], {
                "label": "printStr", "code": p[2].leaf['code']+[["printStr", p[2].leaf['place']]]})


def p_ScanIntStmt(p):
    '''
    ScanIntStmt : SCANINT Expression
    '''
    p[0] = Node("void", [Node("void", [], {"label": "ScanInt"}), p[2]], {
                "label": "ScanInt", "code": p[2].leaf["code"]+[["ScanInt", p[2].leaf["place"]]]})


def p_ScanstrStmt(p):
    '''
    ScanStrStmt : SCANSTR Expression
    '''
    name = generate_strname()
    string_map[name] = 255
    p[0] = Node("void", [Node("void", [], {"label": "ScanInt"}), p[2]], {
                "label": "ScanInt", "code": p[2].leaf["code"]+[["ScanStr", p[2].leaf["place"], name]]})


def p_ExpressionList(p):
    '''
    ExpressionList : Expression
                   | Expression COMMA RepeatNewline ExpressionList
    '''
    if len(p) == 2:

        p[0] = Node(
            'void', [p[1]], {
                'label': 'ExpressionList',
                'type': [p[1].leaf['type']],
                'width': [p[1].leaf['width']]
            })
        p[0].leaf['code'] = p[1].leaf['code']
        p[0].leaf['place'] = [
            p[1].leaf['place'],
        ]
    else:
        p[4].children = [p[1]] + p[4].children
        new_t = [p[1].leaf["type"]] + p[4].leaf["type"]

        p[0] = p[4]
        p[0].leaf["type"] = new_t
        p[0].leaf["width"] = [p[1].leaf["width"]] + p[4].leaf["width"]
        p[0].leaf['code'] = []
        p[0].leaf['place'] = []
        for child in p[4].children:
            p[0].leaf['code'] += child.leaf['code']
            p[0].leaf['place'].append(child.leaf['place'])


def p_Expression(p):
    '''
    Expression : Expression LOR RepeatNewline Term1
               | Term1
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Expression"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        type1 = p[1].leaf["type"]
        type2 = p[4].leaf["type"]
        if check_type(type1, type2, cur_symtab[-1]) == 0:
            print("[line:" + str(p.lineno(1)) + "]" +
                  'logical operation not allowed for given type')
            exit()

        if (check_type(type1, [1], cur_symtab[-1]) == 0):
            print("[line:" + str(p.lineno(1)) + "]" +
                  'logical operation not allowed for given type')
            exit()

        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Expression"})
        p[0].leaf["type"] = [type_map['bool']]
        p[0].leaf["width"] = 4
        # IR Gen
        # t1 = address_generate_compilername(func_offset[-1],4,cur_activation[-1].label,0)
        # func_offset[-1]+=4
        # p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
        # p[0].leaf['code'].append(
        #     [p[2], t1, p[1].leaf['place'], p[4].leaf['place']])
        # p[0].leaf['place'] = t1
        t1 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, 0)
        func_offset[-1] += 4

        p[0].leaf['code'] = p[1].leaf['code']
        label1 = generate_label()
        label2 = generate_label()
        p[0].leaf['code'].append(
            ['iftrue', p[1].leaf['place'], 'goto', label1])
        p[0].leaf['code'] += p[4].leaf['code']
        p[0].leaf['code'].append(['=', t1, p[4].leaf['place']])
        p[0].leaf['code'].append(['goto', label2])
        p[0].leaf['code'].append([label1, ':'])
        p[0].leaf['code'].append(['=', t1, 1])
        p[0].leaf['code'].append([label2, ':'])
        p[0].leaf['place'] = t1


def p_Term1(p):
    '''
    Term1 : Term1 LAND RepeatNewline Term2
          | Term2
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Expression"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        type1 = p[1].leaf["type"]
        type2 = p[4].leaf["type"]
        if check_type(type1, type2, cur_symtab[-1]) == 0:
            print(
                f"[line:{str(p.lineno(1))}]logical operation not allowed for given type")
            exit()

        if (check_type(type1, [1], cur_symtab[-1]) == 0):
            print(
                f"[line:{str(p.lineno(1))}]logical operation not allowed for given type")
            exit()

        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Expression"})
        p[0].leaf["type"] = [type_map['bool']]
        p[0].leaf["width"] = 4

        # IR Gen
        # t1 = address_generate_compilername(func_offset[-1],4,cur_activation[-1].label,0)
        # func_offset[-1]+=4
        # p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
        # p[0].leaf['code'].append(
        #     [p[2], t1, p[1].leaf['place'], p[4].leaf['place']])
        # p[0].leaf['place'] = t1

        t1 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, 0)
        func_offset[-1] += 4

        p[0].leaf['code'] = p[1].leaf['code']
        label1 = generate_label()
        label2 = generate_label()
        p[0].leaf['code'].append(
            ['iffalse', p[1].leaf['place'], 'goto', label1])
        p[0].leaf['code'] += p[4].leaf['code']
        p[0].leaf['code'].append(['=', t1, p[4].leaf['place']])
        p[0].leaf['code'].append(['goto', label2])
        p[0].leaf['code'].append([label1, ':'])
        p[0].leaf['code'].append(['=', t1, 0])
        p[0].leaf['code'].append([label2, ':'])
        p[0].leaf['place'] = t1


def p_Term2(p):
    '''
    Term2 : Term2 Relop RepeatNewline Term3
          | Term3
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term2"
        p[0] = p[1]
    elif (p[2].children[0].leaf["label"] !=
          "==") and (p[2].children[0].leaf["label"] != "!="):
        p[4].leaf["label"] = "Expression"
        p[1].leaf["label"] = "Expression"
        type1 = first_nontypedef(p[4].leaf['type'], cur_symtab[-1])
        type2 = first_nontypedef(p[1].leaf['type'], cur_symtab[-1])
        if len(type1) != 1 or len(type2) != 1:
            print("[line:" + str(p.lineno(1)) + "]" +
                  'Arithmetic operation not allowed for given type')
            exit()
        p[0] = Node("void", [
            Node("void", p[1].children + p[4].children,
                 {"label": p[2].children[0].leaf["label"]})
        ], {"label": "Term2"})
        f1 = 0
        f2 = 0
        if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3
                                                   and type2[0] <= 12):
            p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
            p[2] = p[2].children[0].leaf["label"] + "int"
        elif (type1[0] >= 3 and type1[0] <= 14) and (type2[0] >= 3
                                                     and type2[0] <= 14):
            if type1[0] >= 3 and type1[0] <= 12:
                f1 = 1
            if type2[0] >= 3 and type2[0] <= 12:
                f2 = 1
            p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
            p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
            p[2] = p[2].children[0].leaf["label"] + "float"
        else:
            print("[line:" + str(p.lineno(1)) + "]" +
                  'Arithmetic operation not allowed for given type')
            exit()

        p[0].leaf["type"] = [type_map['bool']]
        p[0].leaf["width"] = 4

        # IR Gen

        p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
        if f1 == 1:
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t1, p[4].leaf['place']])
            p[4].leaf['place'] = t1
        if f2 == 1:
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t1, p[1].leaf['place']])
            p[1].leaf['place'] = t1

        t2 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, 0)
        func_offset[-1] += 4
        p[0].leaf['code'].append(
            [p[2], t2, p[1].leaf['place'], p[4].leaf['place']])
        p[0].leaf['place'] = t2

    else:
        if p[4] == 'null':

            p[1].leaf["label"] = "Expression"
            type2 = first_nontypedef(p[1].leaf['type'], cur_symtab[-1])
            p[0] = Node("void", [
                Node("void", p[1].children,
                     {"label": p[2].children[0].leaf["label"]})
            ], {"label": "Term2"})
            p[0].leaf["type"] = [type_map['bool']]
            p[0].leaf["width"] = 4
            p[0].leaf["code"] = p[1].leaf["code"]
            t2 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 0)
            func_offset[-1] += 4
            p[0].leaf['code'].append(
                [p[2].children[0].leaf["label"], t2, p[1].leaf['place'], 0])
            p[0].leaf['place'] = t2

        else:
            p[4].leaf["label"] = "Expression"
            p[1].leaf["label"] = "Expression"
            type1 = first_nontypedef(p[4].leaf['type'], cur_symtab[-1])
            type2 = first_nontypedef(p[1].leaf['type'], cur_symtab[-1])
            if len(type1) != 1 or len(type2) != 1:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()
            p[0] = Node("void", [
                Node("void", p[1].children + p[4].children,
                     {"label": p[2].children[0].leaf["label"]})
            ], {"label": "Term2"})
            f1 = 0
            f2 = 0

            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3
                                                       and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
                p[2] = p[2].children[0].leaf["label"] + "int"

            elif (type1[0] >= 3 and type1[0] <= 14) and (type2[0] >= 3
                                                         and type2[0] <= 14):
                if type1[0] >= 3 and type1[0] <= 12:
                    f1 = 1
                if type2[0] >= 3 and type2[0] <= 12:
                    f2 = 1
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[2] = p[2].children[0].leaf["label"] + "float"

            elif type1[0] == 16 and type2[0] == 16:
                p[0].leaf["type"], p[0].leaf["width"] = [
                    16
                ], p[1].leaf["width"] + p[4].leaf["width"]
                p[2] = p[2].children[0].leaf["label"] + "string"

            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()

            p[0].leaf["type"] = [type_map['bool']]
            p[0].leaf["width"] = 4

            p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
            if f1 == 1:
                t1 = address_generate_compilername(
                    func_offset[-1], 4, cur_activation[-1].label, 1)
                func_offset[-1] += 4
                p[0].leaf['code'].append(
                    ['cast-float', t1, p[4].leaf['place']])
                p[4].leaf['place'] = t1
            if f2 == 1:
                t1 = address_generate_compilername(
                    func_offset[-1], 4, cur_activation[-1].label, 1)
                func_offset[-1] += 4
                p[0].leaf['code'].append(
                    ['cast-float', t1, p[1].leaf['place']])
                p[1].leaf['place'] = t1

            t2 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 0)
            func_offset[-1] += 4

            p[0].leaf['code'].append(
                [p[2], t2, p[1].leaf['place'], p[4].leaf['place']])
            p[0].leaf['place'] = t2


def p_Relop(p):
    '''
    Relop : LT
          | GT
          | LE
          | GE
          | EQ
          | NE
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "Relop"})


def p_Term3(p):
    '''
    Term3 : Term3 PLUS RepeatNewline Term4
          | Term3 MINUS RepeatNewline Term4
          | Term3 OR RepeatNewline Term4
          | Term3 XOR RepeatNewline Term4
          | NULL
          | Term4
    '''
    if len(p) == 2:
        # p[1].leaf["label"] = "Term3"
        p[0] = p[1]
    else:
        # p[4].leaf["label"] = "Expression"
        # p[1].leaf["label"] = "Expression"
        type1 = first_nontypedef(p[4].leaf['type'], cur_symtab[-1])
        type2 = first_nontypedef(p[1].leaf['type'], cur_symtab[-1])

        f1, f2 = 0, 0
        if len(type1) != 1 or len(type2) != 1:
            print("[line:" + str(p.lineno(1)) + "]" +
                  'Arithmetic operation not allowed for given type')
            exit()

        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Term3"})
        # Only Integers allowed
        if p[2] != '+' and p[2] != '-':
            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3 and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()

        # Only Integers and floats allowed
        elif p[2] == '-':
            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3
                                                       and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
                p[2] = '-int'
            elif (type1[0] >= 3 and type1[0] <= 14) and (type2[0] >= 3 and type2[0] <= 14):
                if type1[0] >= 3 and type1[0] <= 12:
                    f1 = 1
                if type2[0] >= 3 and type2[0] <= 12:
                    f2 = 1
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[2] = '-float'
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()

        # Only Integers and floats and strings allowed
        elif p[2] == '+':
            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3 and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
                p[2] = '+int'
            elif (type1[0] >= 3 and type1[0] <= 14) and (type2[0] >= 3 and type2[0] <= 14):
                if type1[0] >= 3 and type1[0] <= 12:
                    f1 = 1
                if type2[0] >= 3 and type2[0] <= 12:
                    f2 = 1
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[2] = '+float'
            elif type1[0] == 16 and type2[0] == 16:
                p[0].leaf["type"], p[0].leaf["width"] = [16], 4
                p[2] = '+string'
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()
        else:
            print("NOT POSSIBLE ERROR IN p_Term3")
            exit()

        # IR Gen

        p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
        isf = 0

        if f1 == 1:
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t1, p[4].leaf['place']])
            p[4].leaf['place'] = t1
            isf = 1
        if f2 == 1:
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t1, p[1].leaf['place']])
            p[1].leaf['place'] = t1
            isf = 1

        t2 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, isf)
        func_offset[-1] += 4
        # if p[2]=='+string':
        #     name=generate_strname()
        #     string_map[name]=255
        #     p[0].leaf['code'].append(['=string',t2,name])

        p[0].leaf['code'].append(
            [p[2], t2, p[1].leaf['place'], p[4].leaf['place']])
        p[0].leaf['place'] = t2


def p_Term4(p):
    '''
    Term4 : Term4 TIMES RepeatNewline Term5
          | Term4 DIVIDE RepeatNewline Term5
          | Term4 MODULO RepeatNewline Term5
          | Term4 LSHIFT RepeatNewline Term5
          | Term4 RSHIFT RepeatNewline Term5
          | Term4 AND RepeatNewline Term5
          | Term4 ANDNOT RepeatNewline Term5
          | Term5
    '''
    if len(p) == 2:
        # p[1].leaf["label"] = "Term4"
        p[0] = p[1]
    else:
        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Term4"})
        type1 = first_nontypedef(p[4].leaf['type'], cur_symtab[-1])
        type2 = first_nontypedef(p[1].leaf['type'], cur_symtab[-1])
        f1, f2 = 0, 0
        if len(type1) != 1 or len(type2) != 1:
            print("[line:" + str(p.lineno(1)) + "]" +
                  'Arithmetic operation not allowed for given type')
            exit()
        # Only Integers allowed
        if p[2] != '*' and p[2] != '/':
            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3 and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()
        # Both integers and float
        else:
            if (type1[0] >= 3 and type1[0] <= 12) and (type2[0] >= 3 and type2[0] <= 12):
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['int']], 4
                p[2] = p[2] + 'int'
            elif (type1[0] >= 3 and type1[0] <= 14) and (type2[0] >= 3 and type2[0] <= 14):
                if type1[0] >= 3 and type1[0] <= 12:
                    f1 = 1
                if type2[0] >= 3 and type2[0] <= 12:
                    f2 = 1
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[0].leaf["type"], p[0].leaf["width"] = [type_map['float32']], 4
                p[2] = p[2] + 'float'
            else:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Arithmetic operation not allowed for given type')
                exit()

        # IR Gen

        p[0].leaf['code'] = p[1].leaf['code'] + p[4].leaf['code']
        isf = 0
        if f1 == 1:
            t2 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t2, p[4].leaf['place']])
            p[4].leaf['place'] = t2
            isf = 1
        if f2 == 1:
            t2 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 1)
            func_offset[-1] += 4
            p[0].leaf['code'].append(['cast-float', t2, p[1].leaf['place']])
            p[1].leaf['place'] = t2
            isf = 1

        t1 = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, isf)
        func_offset[-1] += 4
        p[0].leaf['code'].append(
            [p[2], t1, p[1].leaf['place'], p[4].leaf['place']])
        p[0].leaf['place'] = t1


def p_Term5(p):
    '''
    Term5 : UnaryExp
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term5"
        p[0] = p[1]
        p[0].leaf['type'] = p[0].children[0].leaf['type']
        p[0].leaf['width'] = p[0].children[0].leaf['width']


def p_UnaryExp(p):
    '''
    UnaryExp : PrimaryExpr
             | Literal
             | UnaryOp RepeatNewline UnaryExp
    '''
    if len(p) == 2:
        # p[1].leaf["label"] = "UnaryExp"
        p[0] = p[1]
    elif len(p) == 4:
        p[0] = Node("void", p[3].children + p[1].children,
                    {"label": "BasicLit"})
        type1 = first_nontypedef(p[3].children[0].leaf["type"], cur_symtab[-1])

        if p[1].children[0].leaf["label"] in ["+"]:
            if len(type1) != 1 or not (type1[0] >= 3 and type1[0] <= 14):
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Unary Operation +,- not allowed on given type')
                exit()
            p[0].leaf['code'] = []
            p[0].leaf['place'] = p[3].leaf['place']

        elif p[1].children[0].leaf["label"] in ["-"]:
            if len(type1) != 1 or not (type1[0] >= 3 and type1[0] <= 14):
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Unary Operation +,- not allowed on given type')
                exit()
            # IR Gen
            isf = is_float(type1, cur_symtab[-1])
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, isf)
            func_offset[-1] += 4
            p[0].leaf['code'] = p[3].leaf['code']
            p[0].leaf['code'].append(
                [p[1].children[0].leaf['label'], t1, p[3].leaf['place']])
            p[0].leaf['place'] = t1

        elif p[1].children[0].leaf["label"] in ["!"]:
            if len(type1) != 1 or type1[0] != 1:
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Unary Operation ! not allowed on given type')
                exit()
            t1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, 0)
            func_offset[-1] += 4
            p[0].leaf['code'] = p[3].leaf['code']
            p[0].leaf['code'].append(
                [p[1].children[0].leaf['label'], t1, p[3].leaf['place']])
            p[0].leaf['place'] = t1

        elif p[1].children[0].leaf["label"] in ["*"]:
            if len(type1) == 1 or type1[0] != 1 or p[3].leaf["label"] == "Literal":
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Unary Operation * not allowed on given type')
                exit()
            p[0].children[0].leaf["type"] = type1[2:]
            p[0].children[0].leaf["width"] = type1[1]

            p[0].leaf['code'] = p[3].leaf['code']

            if p[3].leaf["place"][0] == "*":
                v1 = address_generate_compilername(
                    func_offset[-1], p[0].children[0].leaf["width"], cur_activation[-1].label, 0)
                func_offset[-1] += p[0].children[0].leaf["width"]
                p[0].leaf["code"] += [["=", v1, p[3].leaf["place"]]]
                p[0].leaf["place"] = "*"+v1

            elif p[3].leaf["place"][-1] == "]" or len(p[3].leaf["place"].split(".")) != 1:
                v1 = address_generate_compilername(
                    func_offset[-1], p[0].children[0].leaf["width"], cur_activation[-1].label, 0)
                func_offset[-1] += p[0].children[0].leaf["width"]
                p[0].leaf["code"] += [["=", v1, p[3].leaf["place"]]]
                p[0].leaf["place"] = "*"+v1

            else:
                p[0].leaf["place"] = "*"+p[3].leaf["place"]

        elif p[1].children[0].leaf["label"] in ["&"]:
            if p[3].leaf["label"] == "Literal":
                print("[line:" + str(p.lineno(1)) + "]" +
                      'Unary Operation & not allowed on given type')
                exit()
            p[0].children[0].leaf["type"] = [
                1, p[0].children[0].leaf["width"]
            ] + type1
            p[0].children[0].leaf["width"] = 4

            p[0].leaf["code"] = p[3].leaf["code"]

            if p[3].leaf["place"][-1] == "]":
                p[0].leaf["place"] = "&"+p[3].leaf["place"]
            else:
                v1 = address_generate_compilername(
                    func_offset[-1], 4, cur_activation[-1].label, 0)
                func_offset[-1] += 4
                p[0].leaf["code"] += [["=", v1, "&"+p[3].leaf["place"]]]
                p[0].leaf["place"] = v1


def p_UnaryOp(p):
    '''
    UnaryOp : PLUS
            | MINUS
            | LNOT
            | TIMES
            | AND
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "UnaryOp"})


def p_PrimaryExpr(p):
    '''
    PrimaryExpr : OperandName2
                | PrimaryExpr Selector
                | PrimaryExpr Index
                | PrimaryExpr Arguments
                |  LPAREN RepeatNewline Expression RPAREN
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "PrimaryExpr"
        p[0] = p[1]
    elif len(p) == 3:
        p[0] = Node("void", p[1].children + [p[2]], {"label": "PrimaryExp"})
        code = p[1].leaf['code'] + p[2].leaf['code']
        # print "here"
        # print p[2].leaf["code"]
        place = ''
        if p[2].leaf["label"] == "Selector":
            type_p = first_nontypedef(p[1].children[0].leaf["type"],
                                      cur_symtab[-1])
            if len(type_p) == 1:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Unexpected . with the given input ")
                exit()
            elif type_p[0] != 3 and not (len(type_p) >= 4 and type_p[0] == 1 and type_p[2] == 5):
                print(type_p)
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Unexpected . with the given input ")
                exit()
            else:
                nam = p[2].children[0].leaf["label"]

                if type_p[0] == 3:
                    if nam not in cur_symtab[-1].struct_name_map[type_p[1]].data:
                        print("[line:" + str(
                            p.lineno(1)) + "]" + "id not in Structure ")
                        exit()
                    t = cur_symtab[-1].struct_name_map[type_p[1]
                                                       ].data[nam].type
                    w = cur_symtab[-1].struct_name_map[type_p[1]
                                                       ].data[nam].width
                    p[0].children[0].leaf["type"] = t
                    p[0].children[0].leaf["width"] = w
                    offset = cur_symtab[-1].struct_name_map[type_p[1]
                                                            ].data[nam].offset
                else:
                    type_p2 = first_nontypedef(type_p[2:], cur_symtab[-1])
                    if nam not in cur_symtab[-1].struct_name_map[type_p2[1]].data:
                        print("[line:" + str(
                            p.lineno(1)) + "]" + "id not in Structure ")
                        exit()

                    t = cur_symtab[-1].struct_name_map[type_p2[1]
                                                       ].data[nam].type
                    w = cur_symtab[-1].struct_name_map[type_p2[1]
                                                       ].data[nam].width
                    p[0].children[0].leaf["type"] = t
                    p[0].children[0].leaf["width"] = w
                    offset = cur_symtab[-1].struct_name_map[type_p2[1]
                                                            ].data[nam].offset

                # IR Gen

                var1 = p[1].leaf['place']
                if len(var1.split('[')) != 1 or len(var1.split('.')) != 1:
                    v1 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    code += [["=", v1, "&"+str(var1)]]
                    place = v1+"."+str(offset)
                else:
                    place = var1+"."+str(offset)

        elif p[2].leaf["label"] == "Index":
            type_p = first_nontypedef(p[1].children[0].leaf["type"],
                                      cur_symtab[-1])
            if len(type_p) == 1:
                print("[line:" + str(p.lineno(
                    1)) + "]" + "Unexpected Indexing with the given input ")
                exit()
            elif type_p[0] != 2:
                print("[line:" + str(p.lineno(
                    1)) + "]" + "Unexpected indexing with the given input ")
                exit()
            else:
                p[0].children[0].leaf["width"] = p[1].children[0].leaf["width"] / type_p[1]
                p[0].children[0].leaf["type"] = type_p[2:]

                if p[1].leaf["place"][-1] == "]":
                    v1 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v3 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v4 = p[2].leaf['place']
                    ind = (p[1].leaf["place"].split("["))[1][:-1]
                    code.append(['=', v1, p[0].children[0].leaf['width']])
                    code.append(["*", v2, v4, v1])
                    code.append(['+', v3, ind, v2])
                    place = p[1].leaf['place'].split("[")[0]+"["+v3+"]"
                elif len(p[1].leaf["place"].split(".")) != 1:
                    v3 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    code += [["=", v3, "&"+p[1].leaf["place"]]]
                    v1 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v4 = p[2].leaf['place']
                    code.append(['=', v1, p[0].children[0].leaf['width']])
                    code.append(["*", v2, v4, v1])
                    place = v3+"["+v2+"]"
                elif p[1].leaf['place'][0] == '*':
                    v1 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v4 = p[2].leaf['place']
                    code.append(['=', v1, p[0].children[0].leaf['width']])
                    code.append(["*", v2, v4, v1])
                    place = p[1].leaf["place"][1:]+"["+v2+"]"

                else:
                    v1 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v2 = address_generate_compilername(
                        func_offset[-1], 4, cur_activation[-1].label, 0)
                    func_offset[-1] += 4
                    v4 = p[2].leaf['place']
                    code.append(['=', v1, p[0].children[0].leaf['width']])
                    code.append(["*", v2, v4, v1])
                    place = p[1].leaf["place"]+"["+v2+"]"

                # IR Gen

        elif p[2].leaf["label"] == "Arguments":
            nam = p[1].children[0].leaf['label']
            if nam not in cur_symtab[0].data:
                print("[line:" + str(p.lineno(1)) + "]" + "Function not exists")
                exit()
            type1 = cur_symtab[0].data[nam].args
            type2 = cur_symtab[0].data[nam].type

            if len(p[1].children) != 1:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Only function calling allowed ")
                exit()
            if type1 is None:
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Given ID is not a function")
                exit()
            type_arg = p[2].leaf["type"]
            if len(type_arg) != len(type1):
                print("[line:" + str(
                    p.lineno(1)) + "]" + "Mismatch number of Arguments")
                exit()
            for ind in range(0, len(type1)):
                if check_type(type_arg[ind], type1[ind], cur_symtab[0]) == 0:
                    print("[line:" + str(p.lineno(
                        1)) + "]" + "Type Mismatch in function definition")
                    exit()
            p[0].children[0].leaf["type"] = type2
            p[0].children[0].leaf["width"] = cur_symtab[0].data[nam].width
            p[0].leaf["statement"] = 1

            # IR Gen
            isf = is_float(type2, cur_symtab[-1])
            v1 = address_generate_compilername(
                func_offset[-1], 4, cur_activation[-1].label, isf)
            # print v1
            # print isf
            func_offset[-1] += 4
            code.append(['push'])
            for i in range(len(type1)):
                if len(p[2].leaf["place"][i].split(".")) != 1 or len(p[2].leaf["place"][i].split("[")) != 1:
                    typ = p[2].leaf["type"][i]
                    typ = first_nontypedef(typ, cur_symtab[-1])
                    if (typ[0] == 3 or typ[0] == 2) and len(typ) != 1:
                        # isf=is_float(type2,cur_symtab[-1])
                        v2 = address_generate_compilername(
                            func_offset[-1], 4, cur_activation[-1].label, 0)
                        func_offset[-1] += 4
                        code.append(['=', v2, '&'+p[2].leaf['place'][i]])
                        code.append(['push', v2])
                else:
                    code.append(['push', p[2].leaf['place'][i]])
            code.append(['call', nam, len(type1)])

            # pop_width_list = cur_symtab[0].data[nam].args_width
            # for pop_width in pop_width_list:
            #     for count in xrange(pop_width/4):
            #         code.append(['pop'])
            for i in range(len(type1)):
                code.append(['pop'])
            code.append(['pop', v1])
            place = v1
        p[0].leaf['place'] = place
        p[0].leaf['code'] = code
        p[0].leaf['width'] = p[0].children[0].leaf['width']
    else:
        p[3].leaf["label"] = "Term5"
        p[0] = p[3]
        p[0].children[0].leaf["type"] = p[0].leaf["type"]
        p[0].children[0].leaf["width"] = p[0].leaf["width"]


# Literal = BasicLit | CompositeLit | FunctionLit .
def p_Literal(p):
    '''
    Literal : BasicLit
            | CompositeLit
    '''
    p[1].leaf["label"] = "Literal"
    p[0] = p[1]


# BasicLit = int_lit | float_lit | imaginary_lit | rune_lit | string_lit .
def p_BasicLit(p):
    '''
    BasicLit : intLit
             | floatLit
             | stringLit
    '''

    # string not handles
    if p[1].leaf['label'] == 'String':
        p[1].leaf['place'] = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, 0)
        func_offset[-1] += 4
        name = generate_strname()
        p[1].leaf["label"] = "BasicLit"
        p[0] = p[1]
        string_map[name] = p[0].children[0].leaf['label']
        p[0].leaf['code'] = [
            ['=string', p[0].leaf['place'], name],
        ]
    else:
        p[1].leaf["label"] = "BasicLit"
        p[0] = p[1]
        isf = is_float(p[0].children[0].leaf["type"], cur_symtab[-1])
        p[0].leaf['place'] = address_generate_compilername(
            func_offset[-1], 4, cur_activation[-1].label, isf)
        func_offset[-1] += 4
        p[0].leaf['code'] = [
            ['=', p[0].leaf['place'], p[0].children[0].leaf['label']],
        ]


# int_lit = decimal_lit | octal_lit | hex_lit .
def p_intLit(p):
    '''
    intLit : INTEGER
    '''
    if len(p[1]) > 2 and p[1][:2] == '0x':
        p[1] = int(p[1], base=16)
    p[0] = Node("void", [
        Node("void", [], {
            "label": int(p[1]),
            "type": [type_map['int']],
            "width": type_width['int']
        })
    ], {"label": "Int"})


# float_lit = decimals "." [ decimals ] [ exponent ] |decimals exponent |"." decimals [ exponent ] .
def p_floatLit(p):
    '''
    floatLit : FLOAT
    '''
    p[0] = Node("void", [
        Node(
            "void", [], {
                "label": float(p[1]),
                "type": [type_map['float32']],
                "width": type_width['float32']
            })
    ], {"label": "Float"})


# string_lit = raw_string_lit | interpreted_string_lit .
def p_stringLit(p):
    '''
    stringLit : STRINGVAL
              | CHARACTER
    '''
    p[0] = Node("void", [
        Node(
            "void", [], {
                "label": p[1],
                "type": [type_map['string']],
                "width": 4
            })
    ], {"label": "String"})


# CompositeLit = LiteralType LiteralValue .
def p_CompositeLit(p):
    '''
    CompositeLit : LiteralType LiteralValue
    '''
    p[1].leaf["type"] = p[1].children[0].leaf["type"]
    p[1].leaf["width"] = p[1].children[0].leaf["width"]
    p[0] = Node("void", [p[1], p[2]], {"label": "CompositeLit"})


# LiteralType = StructType | ArrayType | "[" "..." "]" ElementType |SliceType | MapType | TypeName .
def p_LiteralType(p):
    '''
    LiteralType : ArrayType
                | StructType
                | SliceType
    '''
    p[0] = p[1]


def p_Mytypes(p):
    '''
    Mytypes : BOOL
            | BYTE
            | INT
            | UINT8
            | UINT16
            | UINT32
            | UINT64
            | INT8
            | INT16
            | INT32
            | INT64
            | UINT
            | FLOAT32
            | FLOAT64
            | UINTPTR
            | STRING
            | ERROR
    '''
    p[0] = Node("void", [
        Node("void", [], {
            "label": p[1],
            "type": [type_map[p[1]]],
            "width": type_width[p[1]]
        })
    ], {"label": "Mytypes"})


def p_Types(p):
    '''
    Types : Mytypes
          | TypeLit
          | OperandName
    '''
    p[1].leaf["label"] = "Types"
    p[0] = p[1]
    p[0].leaf["type"] = p[0].children[0].leaf["type"]
    p[0].leaf["width"] = p[0].children[0].leaf["width"]


def p_Typelit(p):
    '''
    TypeLit : StructType
            | ArrayType
            | PointerType
            | SliceType
    '''
    p[1].leaf["label"] = "TypeLit"
    p[0] = p[1]


def p_SliceType(p):
    '''
    SliceType : LBRACKET RBRACKET Types
    '''
    p[0] = Node("void", [
        Node(
            "void", [Node("void", [], {"label": "[]"})] + p[3].children, {
                "label": "SliceType",
                "type": [4] + p[3].children[0].leaf["type"],
                "width": 12
            })
    ], {"label": "Types"})


def p_PointerType(p):
    '''
    PointerType : TIMES Types
    '''
    p[0] = Node("void", [
        Node(
            "void", p[2].children[0].children, {
                "label": p[1] + p[2].children[0].leaf["label"],
                "type":
                [1, p[2].leaf["width"]] + p[2].children[0].leaf["type"],
                "width": 4
            })
    ], {"Label": "PointerType"})


def p_StructType(p):
    '''
    StructType : STRUCT M RepeatNewline LBRACE RepeatNewline RepeatFieldDecl RBRACE
    '''

    # print "-" * 40
    # print "struct symtab"
    # print "symtab data:\n"
    # for key, val in cur_symtab[-1].data.items():
    #     print key, "-->type: ", val.type, " width: ", val.width
    # print "total offset:", cur_offset[len(cur_offset) - 1]
    # print "-" * 40
    top = cur_symtab[len(cur_symtab) - 1]
    top.total = cur_offset[len(cur_offset) - 1]

    for key in cur_symtab[-1].data:
        type1 = cur_symtab[-1].data[key].type
        if len(type1) % 2 == 0:
            if len(type1) >= 4 and type1[-4] == 1 and type1[-3] == 0:
                cur_symtab[-1].data[key].type[-3] = top.total

    dump_st()
    cur_symtab.pop()
    cur_offset.pop()
    p[6].leaf["label"] = "Fields"
    p[0] = Node("void", [
        Node("void", p[6].children, {
            "label": "struct",
            "type": [3, p[2]],
            "width": top.total
        })
    ], {"label": "StructType"})


def p_M(p):
    '''
    M : empty
    '''
    name = generate_name()
    top = structtab(cur_symtab[-1])
    cur_symtab[len(cur_symtab) - 1].struct_name_map[name] = top
    cur_symtab.append(top)
    cur_offset.append(0)
    p[0] = name


def p_RepeatFieldDecl(p):
    '''
    RepeatFieldDecl : FieldDecl StatementEnd RepeatFieldDecl
                    | FieldDecl
                    | empty
    '''
    if len(p) == 2:
        if p[1]:
            p[0] = Node("void", [p[1]], {"label": "RepeatFieldDecl"})
        else:
            p[0] = Node("void", [], {"label": "RepeatFieldDecl"})
    if len(p) == 4:
        p[3].children = [p[1]] + p[3].children
        p[0] = p[3]


def p_FieldDecl(p):
    '''
    FieldDecl : IdentifierList Types
    '''
    p[0] = Node("void", [p[1], p[2]], {"label": "Field"})
    for child in p[1].children:
        t = lookup(cur_symtab[len(cur_symtab) - 1], child.leaf["label"])
        if t is None:
            type1 = p[2].children[0].leaf["type"]
            if len(type1) > 1:
                if type1[-2] == 5 and len(type1) % 2 == 0:
                    val = cur_symtab[-1].typedef_map[type1[-1]]["type"]
                    if len(val) == 0:
                        if len(type1) > 3:
                            if type1[-4] != 1:
                                print("[line:" + str(p.lineno(
                                    2)) + "]" + "Recursive Struct not allowed!")
                                exit()
                        else:
                            print("[line:" + str(p.lineno(
                                2)) + "]" + "Recursive Struct not allowed!")
                            exit()

            cur_symtab[len(cur_symtab) - 1].data[child.leaf["label"]] = values(
                type=type1,
                width=p[2].leaf["width"],
                offset=cur_offset[len(cur_offset) - 1])
            cur_offset[len(cur_offset) - 1] += p[2].leaf["width"]
        else:
            print("[line:" + str(
                p.lineno(1)) + "]" + "Redeclaration of " + str(
                    child.leaf["label"]) + " at line " + str(p.lineno(1)))


# ArrayType   = "[" ArrayLength "]" ElementType .
def p_ArrayType(p):
    '''
    ArrayType : LBRACKET RepeatNewline ArrayLength RBRACKET Types
    '''
    p[0] = Node("void", [
        Node(
            "void", [
                Node(
                    "void", [],
                    {"label": "[" + str(p[3].children[0].leaf["label"]) + "]"})
            ] + p[5].children, {
                "label":
                "ArrayType",
                "type": [2, int(p[3].children[0].leaf["label"])] +
                p[5].children[0].leaf["type"],
                "width":
                int(p[3].children[0].leaf["label"]) *
                p[5].children[0].leaf["width"]
            })
    ], {"label": "Types"})


def p_ArrayLength(p):
    '''
    ArrayLength : INTEGER
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "ArrayLength"})


# LiteralValue  = "{" [ ElementList [ "," ] ] "}" .
def p_LiteralValue(p):
    '''
    LiteralValue : LBRACE RepeatNewline  RBRACE
                 | LBRACE RepeatNewline ElementList RBRACE
    '''
    if len(p) == 4:
        p[0] = Node("void", [Node("void", [], {"label": "empty"})],
                    {"label": "LiteralValue"})
    else:
        p[3].leaf["label"] = "LiteralValue"
        p[0] = p[3]


def p_Elementlist(p):
    '''
    ElementList : KeyedElement RepeatKeyedElement
    '''
    p[0] = Node("void", [p[1]] + p[2].children, {"label": "ElementList"})


def p_RepeatKeyedElement(p):
    '''
    RepeatKeyedElement : COMMA RepeatNewline KeyedElement RepeatKeyedElement
                       | empty
    '''
    if len(p) == 2:
        p[0] = Node("void", [], {"label": "RepeatKeyedElement"})
    else:
        p[4].children = [p[3]] + p[4].children
        p[0] = p[4]


# KeyedElement  = [ Key ":" ] Element .
def p_KeyedElement(p):
    '''
    KeyedElement : Element
    '''
    p[1].leaf["label"] = "KeyedElement"
    p[0] = p[1]


# Element  = Expression | LiteralValue .
def p_Element(p):
    '''
    Element : BasicLit
    '''
    p[1].leaf["label"] = "Element"
    p[0] = p[1]


# OperandName = identifier | QualifiedIdent.
def p_OperandName(p):
    '''
    OperandName : ID
    '''
    if p[1] in cur_symtab[len(cur_symtab) - 1].typedef_map:
        val = cur_symtab[len(cur_symtab) - 1].typedef_map[p[1]]
        p[0] = Node("void", [
            Node("void", [], {
                "label": p[1],
                "type": [5, p[1]],
                "width": val["width"]
            })
        ], {"label": "OperandName"})
    else:
        print("[line:" + str(
            p.lineno(1)) + "]" + "Type " + p[1] + " used but not declared")
        exit()


def p_OperandName2(p):
    '''
    OperandName2 : ID
    '''
    tmp = lookup_top(cur_symtab[-1], p[1])
    if tmp is None:
        print("[line:" + str(p.lineno(1)) + "]" + "Variable " + p[1] +
              " undeclared in OperandName2.")
        exit()
    p[0] = Node("void", [
        Node("void", [], {
            "label": p[1],
            "type": tmp.type,
            "width": tmp.width,
            "marked": 1
        })
    ], {"label": "OperandName2"})
    p[0].leaf['code'] = []
    p[0].leaf['place'] = tmp.place


def p_Selector(p):
    '''
    Selector : PERIOD RepeatNewline ID
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[3]})],
                {"label": "Selector"})
    p[0].leaf['code'] = []


def p_Index(p):
    '''
    Index : LBRACKET RepeatNewline Expression RBRACKET
    '''
    p[0] = Node("void", p[3].children, {"label": "Index"})
    type1 = first_nontypedef(p[3].leaf["type"], cur_symtab[-1])
    if len(type1) != 1 or not (type1[0] >= 3 and type1[0] <= 12):
        print("[line:" + str(p.lineno(1)) + "]" + 'Array Index not integer')
        exit()
    p[0].leaf['code'] = p[3].leaf['code']
    p[0].leaf['place'] = p[3].leaf['place']


# Arguments = "(" [ ( ExpressionList | Type [ "," ExpressionList ] ) [ "..." ] [ "," ] ] ")" .
def p_Argument(p):
    '''
    Arguments : LPAREN RepeatNewline ExpressionList RPAREN
              | LPAREN RepeatNewline RPAREN
    '''
    if len(p) == 4:
        p[0] = Node("void", [], {"label": "Arguments"})
        p[0].leaf["type"] = []
        p[0].leaf['code'] = []
        p[0].leaf['place'] = []
    else:
        p[0] = Node("void", p[3].children, {"label": "Arguments"})
        p[0].leaf["type"] = p[3].leaf["type"]
        p[0].leaf['code'] = p[3].leaf['code']
        p[0].leaf['place'] = p[3].leaf['place']


def p_IdentifierList(p):
    '''
    IdentifierList : ID
                   |  IdentifierList COMMA RepeatNewline ID
    '''
    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                    {"label": "IdentifierList"})
    else:
        p[1].children.append(Node("void", [], {"label": p[4]}))
        p[0] = p[1]


def p_MallocExp(p):
    '''
    MallocExp : MALLOC LPAREN Expression RPAREN
    '''
    p[0] = p[3]
    p[0].leaf['label'] = 'malloc'


def p_OpenFileExp(p):
    '''
    OpenFileExp : OPENFILE LPAREN Expression COMMA Expression COMMA Expression RPAREN
    '''
    p[0] = Node('void', [p[3], p[5], p[7]], {'label': 'openFile'})
    p[0].leaf['code'] = p[3].leaf['code'] + \
        p[5].leaf['code'] + p[7].leaf['code']


def p_ReadFileExp(p):
    '''
    ReadFileExp : READFILE LPAREN Expression COMMA Expression COMMA Expression RPAREN
    '''
    p[0] = Node('void', [p[3], p[5], p[7]], {'label': 'readFile'})
    p[0].leaf['code'] = p[3].leaf['code'] + \
        p[5].leaf['code'] + p[7].leaf['code']


def p_WriteFileExp(p):
    '''
    WriteFileExp : WRITEFILE LPAREN Expression COMMA Expression COMMA Expression RPAREN
    '''
    p[0] = Node('void', [p[3], p[5], p[7]], {'label': 'writeFile'})
    p[0].leaf['code'] = p[3].leaf['code'] + \
        p[5].leaf['code'] + p[7].leaf['code']


def p_CloseFileExp(p):
    '''
    CloseFileExp : CLOSEFILE LPAREN Expression RPAREN
    '''
    p[0] = Node('void', [p[3]], {'label': 'closeFile'})
    p[0].leaf['code'] = p[3].leaf['code']


def p_SinExp(p):
    '''
    SinExp : SIN LPAREN Expression RPAREN
    '''
    p[0] = Node('void', [p[3]], {'label': 'sin'})
    p[0].leaf['code'] = p[3].leaf['code']


def p_CosExp(p):
    '''
    CosExp : COS LPAREN Expression RPAREN
    '''
    p[0] = Node('void', [p[3]], {'label': 'cos'})
    p[0].leaf['code'] = p[3].leaf['code']


def p_empty(p):
    '''
    empty :
    '''
    pass


def p_terminator(p):
    '''
    terminator : SEMI
    '''
    p[0] = p[1]


def p_StatementEnd(p):
    '''
    StatementEnd : terminator StatementEnd
                 | newline StatementEnd
                 | terminator
                 | newline
    '''


def p_RepeatNewline(p):
    '''
    RepeatNewline : newline RepeatNewline
                  | empty
    '''


def p_error(p):
    if p:
        print("Syntax error at line no:", p.lineno, "and position", p.lexpos,
              "with token value ", p.value, "\n")
    else:
        print("Syntax error at EOF")


def main():
    global out_ir, out_st
    global parser
    global set_of_activation

    parser = argparse.ArgumentParser(description='A Parser for Golang')
    parser.add_argument('--ir', required=True,
                        help='Output file for 3 Address Code')
    parser.add_argument('--st', required=True,
                        help='Output file for Symbol Table')
    parser.add_argument('input', help='input golang file')
    args = parser.parse_args()
    with open(args.input, 'r') as f:
        program = ''.join(f.readlines())
    lexer = lex.lex()
    parser = yacc.yacc()
    out_ir = open(args.ir, 'w+')
    out_st = open(args.st, 'w+')
    out_st.write('scope-type,label,type,offset,width,args,place,typedef-map\n')
    yacc.parse(program, tracking=True)
    out_ir.close()
    out_st.close()
    with open('activation.pickle', 'wb') as handle:
        pickle.dump(set_of_activation, handle)
    with open('string_map.pickle', 'wb') as handle:
        pickle.dump(string_map, handle)


if __name__ == '__main__':
    main()
