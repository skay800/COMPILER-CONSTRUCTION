import argparse
import re
import sys

import ply.lex as lex
import ply.yacc as yacc
import lexer as lexr

gcounter, outfile = 0, None


class Node:
    def __init__(self, type, children=None, leaf=None):
        self.type = type
        self.children = children or []
        self.leaf = leaf


def dfs(a, lcounter):
    global gcounter
    if a is not None:
        string = ""
        string = (
            f"{string}a{str(lcounter)}" + " [label=\"" + str(a.leaf["label"])
        ) + "\"];\n"
        outfile.write(string)
        string = ""
        for x in a.children:
            if x is not None:
                string = (
                    f"{string}a{str(lcounter)} -> a{str(gcounter + 1)}" + ";\n")
                outfile.write(string)
                string = ""
                gcounter += 1
                dfs(x, gcounter)


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
    print(f"Illegal character '{str(t.value[0])}'")
    print(f"Value of the illegal token is '{str(t.value)}'")
    t.lexer.skip(1)


def p_Start(p):
    '''
    Start : SourceFile
    '''
    print("Succesfully completed.")
    p[0] = p[1]
    dfs(p[0], 0)
    outfile.write("}")


def p_SourceFile(p):
    '''
    SourceFile : RepeatNewline PackageClause ImportClause RepeatTopLevelDecl
    '''
    p[0] = Node("void", [p[2], p[3], p[4]], {"label": "Start"})


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
    if len(p) in {2, 3}:
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
            p[0] = Node("void", [p[1]], {"label": "Declarations"})
        else:
            p[0] = Node("void", [], {"label": "Declarations"})
    if len(p) == 4:
        p[3].children = [p[1]] + p[3].children
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
            p[0] = Node("void", [], {"label": "StatementList"})
    if len(p) == 4:
        p[3].children = [p[1]] + p[3].children
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
    ConstSpec : IdentifierList
              | IdentifierList EQUALS ExpressionList
    '''
    if len(p) == 2:
        p[0] = Node("void", [p[1]], {"label": "ConstSpec"})
    else:
        p[0] = Node("void",
                    [p[1], Node("void", [], {"label": "="}), p[3]],
                    {"label": "ConstSpec"})


# TypeDecl = "type" ( TypeSpec | "(" { TypeSpec ";" } ")" ) .
def p_TypeDecl(p):
    '''
    TypeDecl : TYPE RepeatNewline TypeSpec
    '''
    p[3].children = [Node("void", [], {"label": "type"})] + p[3].children
    p[0] = p[3]
    p[0].leaf["label"] = "TypeDecl"


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
    TypeDef : ID Types
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]}), p[2]],
                {"label": "TypeDef"})


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
            | IdentifierList EQUALS RepeatNewline ExpressionList
    '''
    if len(p) == 3:
        p[0] = Node("void", [p[1], p[2]], {"label": "Varspec"})
    elif len(p) == 6:
        p[0] = Node(
            "void",
            [p[1], p[2], Node("void", [], {"label": "="}), p[5]],
            {"label": "Varspec"})
    else:
        p[0] = Node("void",
                    [p[1], Node("void", [], {"label": "="}), p[4]],
                    {"label": "Varspec"})


# FunctionDecl = "func" FunctionName Signature [ FunctionBody ] .
# FunctionName = identifier .
# FunctionBody = Block .
def p_FunctionDecl(p):
    '''
    FunctionDecl : FunctionMarker  FunctionBody
                 | FunctionMarker
    '''
    if len(p) == 3:
        p[2].leaf["label"] = "FunctionBody"
        p[1].children = p[1].children + [p[2]]
    p[1].leaf["label"] = "Function"
    p[0] = p[1]


def p_FunctionMarker(p):
    '''
    FunctionMarker : FUNC RepeatNewline FunctionName Signature
    '''
    p[0] = Node("void",
                [Node("void", [], {"label": "func"}), p[3]] + p[4].children,
                {"label": "marker"})


def p_FunctionName(p):
    '''
    FunctionName : ID
    '''
    p[0] = Node("void", [], {"label": p[1]})


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
        p[0] = Node("void", [p[1]], {"label": "Signature"})
    else:
        p[0] = Node("void", [p[1], p[2]], {"label": "Signature"})


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
        ], {"label": "Arguments"})
    else:
        p[0] = Node("void", p[3].children, {"label": "Arguments"})


def p_ParameterList(p):
    '''
    ParameterList : ParameterDecl RepeatParameterDecl
    '''
    p[2].children = [p[1]] + p[2].children
    p[2].leaf["label"] = "ParameterList"
    p[0] = p[2]


def p_RepeatParameterDecl(p):
    '''
    RepeatParameterDecl : COMMA RepeatNewline ParameterDecl RepeatParameterDecl
                        | empty
    '''
    if len(p) == 2:
        p[0] = Node("void", [], {"label": "RepeatDecl"})
    else:
        p[4].children = [p[3]] + p[4].children
        p[0] = p[4]


def p_ParameterDecl(p):
    '''
    ParameterDecl : ID Types
                  | Types
    '''
    if len(p) == 3:
        p[0] = Node(
            "void",
            p[2].children[0].children,
            {"label": f"{p[1]} " + str(p[2].children[0].leaf["label"])},
        )
    else:
        p[0] = Node("void", p[1].children[0].children,
                    {"label": str(p[1].children[0].leaf["label"])})


def p_Result(p):
    '''
    Result : Parameters
           | Types
    '''
    p[1].leaf["label"] = "Return Values"
    p[0] = p[1]


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


def p_IncDecStmt(p):
    '''
    IncDecStmt : Expression INCR
               | Expression DECR
    '''
    p[0] = Node("void", [p[1]] + [Node("void", [], {"label": p[2]})],
                {"label": "IncDecStmt"})


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
             | ANDNOTEQUAL
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "AssignOp"})


def p_Assignments(p):
    '''
    Assignment : ExpressionList AssignOp RepeatNewline ExpressionList
               | ExpressionList EQUALS RepeatNewline ExpressionList
    '''
    if p[2] == "=":
        p[0] = Node("void",
                    [p[1], Node("void", [], {"label": p[2]}), p[4]],
                    {"label": "Assignment"})
    else:
        p[0] = Node("void", [p[1], p[2].children[0], p[4]],
                    {"label": "AssignOp"})


def p_ShortVarDecl(p):
    '''
    ShortVarDecl : ExpressionList AUTOASIGN RepeatNewline ExpressionList
    '''
    p[0] = Node("void", [p[1], Node("void", [], {"label": p[2]}), p[4]],
                {"label": "Assignment"})


def p_ReturnStmt(p):
    '''
    ReturnStmt : RETURN
               | RETURN ExpressionList
    '''
    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": "return"})],
                    {"label": "ReturnStmt"})
    else:
        p[0] = Node("void", [Node("void", [], {"label": "return"}), p[2]],
                    {"label": "ReturnStmt"})


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
    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": "break"})],
                    {"label": "BreakStmt"})
    else:
        p[0] = Node("void",
                    [Node("void", [], {"label": "break"}), p[2].children[0]],
                    {"label": "BreakStmt"})


def p_ContinueStmt(p):
    '''
    ContinueStmt : CONTINUE
                 | CONTINUE Label
    '''
    if len(p) == 2:
        p[0] = Node("void", [Node("void", [], {"label": "continue"})],
                    {"label": "ContinueStmt"})
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


def p_Block(p):
    '''
    Block : LBRACE RepeatNewline Marker StatementList RBRACE
    '''
    p[0] = Node("void", [p[4]], {"label": "Block"})


def p_Marker(p):
    '''
    Marker : empty
    '''


def p_IfStmt(p):
    '''
    IfStmt : IF RepeatNewline Expression Block
           | IF RepeatNewline Expression Block ELSE Block
           | IF RepeatNewline Expression Block ELSE IfStmt
           | IF RepeatNewline SimpleStmt terminator Expression Block
           | IF RepeatNewline SimpleStmt terminator Expression Block ELSE IfStmt
           | IF RepeatNewline SimpleStmt terminator Expression Block ELSE Block
    '''
    if len(p) == 5:
        p[0] = Node("void", [Node("void", [], {"label": "if"}), p[3], p[4]],
                    {"label": "IfStmt"})
    elif len(p) == 7 and p[4] == ";":
        p[0] = Node("void",
                    [Node("void", [], {"label": "if"}), p[3], p[5], p[6]],
                    {"label": "IfStmt"})
    elif len(p) == 7:
        p[0] = Node("void", [
            Node("void", [], {"label": "if"}), p[3], p[4],
            Node("void", [], {"label": "else"}), p[6]
        ], {"label": "IfStmt"})
    else:
        p[0] = Node("void", [
            Node("void", [], {"label": "if"}), p[3], p[5], p[6],
            Node("void", [], {"label": "else"}), p[8]
        ], {"label": "IfStmt"})


def p_SwitchStmt(p):
    '''
    SwitchStmt : ExprSwitchStmt
    '''
    p[0] = p[1]


def p_ExprSwitchStmt(p):
    '''
    ExprSwitchStmt : SWITCH RepeatNewline LBRACE RepeatNewline RepeatExprCaseClause RBRACE
                   | SWITCH RepeatNewline Expression LBRACE RepeatNewline RepeatExprCaseClause RBRACE
    '''
    if len(p) == 7:
        p[0] = Node("void", [Node("void", [], {"label": "switch"}), p[5]],
                    {"label": "ExprSwitchStmt"})
    else:
        p[0] = Node("void",
                    [Node("void", [], {"label": "switch"}), p[3], p[6]],
                    {"label": "ExprSwitchStmt"})


def p_RepeatExprCaseClause(p):
    '''
    RepeatExprCaseClause : ExprCaseClause RepeatExprCaseClause
                         | empty
    '''
    if len(p) == 3:
        p[2].children = [p[1]] + p[2].children
        p[0] = p[2]
    else:
        p[0] = Node("void", [], {"label": "RepeatExprCaseClause"})


def p_ExprCaseClause(p):
    '''
    ExprCaseClause : ExprSwitchCase COLON RepeatNewline StatementList
    '''
    p[0] = Node("void", p[1].children + [p[4]], {"label": "ExprCaseClause"})


def p_ExprSwitchCase(p):
    '''
    ExprSwitchCase : CASE RepeatNewline Expression
                   | DEFAULT  RepeatNewline
    '''
    if len(p) == 3:
        p[0] = Node("void", [Node("void", [], {"label": "default"})],
                    {"label": "ExprSwitchCase"})
    else:
        p[0] = Node("void", [Node("void", [], {"label": "case"}), p[3]],
                    {"label": "ExprSwitchCase"})


def p_ForStmt(p):
    '''
    ForStmt : FOR RepeatNewline Block
            | FOR RepeatNewline Condition Block
            | FOR RepeatNewline ForClause Block
    '''
    if len(p) == 4:
        p[0] = Node("void", [Node("void", [], {"label": "for"}), p[3]],
                    {"label": "ForStmt"})
    else:
        p[0] = Node("void", [Node("void", [], {"label": "for"}), p[3], p[4]],
                    {"label": "ForStmt"})


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
    elif len(p) == 4:
        if p[2] == ";" and p[3] == ";":
            p[0] = Node("void", [
                p[1],
                Node("void", [], {"label": "Condition"}),
                Node("void", [], {"label": "PostStmt"})
            ], {"label": "ForClause"})
        elif p[1] == ";" and p[3] == ";":
            p[0] = Node("void", [
                Node("void", [], {"label": "InitStmt"}), p[2],
                Node("void", [], {"label": "PostStmt"})
            ], {"label": "ForClause"})
        else:
            p[0] = Node("void", [
                Node("void", [], {"label": "InitStmt"}),
                Node("void", [], {"label": "Condition"}), p[3]
            ], {"label": "ForClause"})
    elif len(p) == 5:
        if p[2] == ";" and p[4] == ";":
            p[0] = Node("void",
                        [p[1], p[3],
                         Node("void", [], {"label": "PostStmt"})],
                        {"label": "ForClause"})
        elif p[2] == ";" and p[3] == ";":
            p[0] = Node(
                "void",
                [p[1], Node("void", [], {"label": "Condition"}), p[4]],
                {"label": "ForClause"})
        else:
            p[0] = Node("void",
                        [Node("void", [], {"label": "InitStmt"}), p[2], p[4]],
                        {"label": "ForClause"})
    else:
        p[0] = Node("void", [p[1], p[3], p[5]], {"label": "ForClause"})


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


def p_DeferStmt(p):
    '''
    DeferStmt : DEFER PrimaryExpr Arguments
    '''
    p[0] = Node(
        "void",
        [Node("void", [], {"label": "defer"})] + p[2].children + [p[3]],
        {"label": "DeferStmt"})


def p_ExpressionList(p):
    '''
    ExpressionList : Expression
                   | Expression COMMA RepeatNewline ExpressionList
    '''
    if len(p) == 2:
        p[0] = Node("void", [p[1]], {"label": "ExpressionList"})
    else:
        p[4].children = [p[1]] + p[4].children
        p[0] = p[4]


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
        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Expression"})


def p_Term1(p):
    '''
    Term1 : Term1 LAND RepeatNewline Term2
          | Term2
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term1"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        p[1].leaf["label"] = "Expression"
        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Term1"})


def p_Term2(p):
    '''
    Term2 : Term2 Relop RepeatNewline Term3
          | Term3
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term2"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        p[1].leaf["label"] = "Expression"
        p[0] = Node("void", [
            Node("void", p[1].children + p[4].children,
                 {"label": p[2].children[0].leaf["label"]})
        ], {"label": "Term2"})


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
          | Term4
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term3"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        p[1].leaf["label"] = "Expression"
        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Term3"})


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
        p[1].leaf["label"] = "Term4"
        p[0] = p[1]
    else:
        p[4].leaf["label"] = "Expression"
        p[1].leaf["label"] = "Expression"
        p[0] = Node(
            "void",
            [Node("void", p[1].children + p[4].children, {"label": p[2]})],
            {"label": "Term4"})


def p_Term5(p):
    '''
    Term5 : LPAREN RepeatNewline Expression RPAREN
          | UnaryExp
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "Term5"
        p[0] = p[1]
    else:
        p[3].leaf["label"] = "Term5"
        p[0] = p[3]


def p_UnaryExp(p):
    '''
    UnaryExp : PrimaryExpr
             | UnaryOp RepeatNewline UnaryExp
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "UnaryExp"
        p[0] = p[1]
    else:
        p[0] = Node("void", p[1].children + p[3].children,
                    {"label": "UnaryExp"})


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
    PrimaryExpr : Operand
                | PrimaryExpr Selector
                | PrimaryExpr Index
                | PrimaryExpr Arguments
    '''
    if len(p) == 2:
        p[1].leaf["label"] = "PrimaryExpr"
        p[0] = p[1]
    else:
        p[0] = Node("void", p[1].children + [p[2]], {"label": "PrimaryExp"})


# Operand = Literal | OperandName | "(" Expression ")" .
def p_Operand(p):
    '''
    Operand : Literal
            | OperandName
    '''
    p[1].leaf["label"] = "Operand"
    p[0] = p[1]


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
    p[1].leaf["label"] = "BasicLit"
    p[0] = p[1]


# int_lit = decimal_lit | octal_lit | hex_lit .
def p_intLit(p):
    '''
    intLit : INTEGER
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})], {"label": "Int"})


# float_lit = decimals "." [ decimals ] [ exponent ] |decimals exponent |"." decimals [ exponent ] .
def p_floatLit(p):
    '''
    floatLit : FLOAT
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "Float"})


# string_lit = raw_string_lit | interpreted_string_lit .
def p_stringLit(p):
    '''
    stringLit : STRINGVAL
              | CHARACTER
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1][1:-1]})],
                {"label": "String"})


# CompositeLit = LiteralType LiteralValue .
def p_CompositeLit(p):
    '''
    CompositeLit : LiteralType LiteralValue
    '''
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
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "Mytypes"})


def p_Types(p):
    '''
    Types : Mytypes
          | TypeLit
          | OperandName
    '''
    p[1].leaf["label"] = "Types"
    p[0] = p[1]


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
        Node("void", [Node("void", [], {"label": "[]"})] + p[3].children,
             {"label": "SliceType"})
    ], {"label": "Types"})


def p_PointerType(p):
    '''
    PointerType : TIMES Types
    '''
    p[0] = Node("void", [
        Node("void", p[2].children[0].children,
             {"label": p[1] + p[2].children[0].leaf["label"]})
    ], {"Label": "PointerType"})


def p_StructType(p):
    '''
    StructType : STRUCT RepeatNewline LBRACE RepeatNewline RepeatFieldDecl RBRACE
    '''
    p[5].leaf["label"] = "Fields"
    p[0] = Node("void", [Node("void", p[5].children, {"label": "struct"})],
                {"label": "rub"})


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


# ArrayType   = "[" ArrayLength "]" ElementType .
def p_ArrayType(p):
    '''
    ArrayType : LBRACKET RepeatNewline ArrayLength RBRACKET Types
    '''
    p[0] = Node("void", [
        Node("void", [
            Node("void", [],
                 {"label": "[" + str(p[3].children[0].leaf["label"]) + "]"})
        ] + p[5].children, {"label": "ArrayType"})
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
    Element : Expression
    '''
    p[1].leaf["label"] = "Element"
    p[0] = p[1]


# OperandName = identifier | QualifiedIdent.
def p_OperandName(p):
    '''
    OperandName : ID
    '''
    p[0] = Node("void", [Node("void", [], {"label": p[1]})],
                {"label": "OperandName"})


def p_Selector(p):
    '''
    Selector : PERIOD RepeatNewline ID
    '''
    p[0] = Node(
        "void",
        [Node("void", [], {"label": f".{p[3]}"})],
        {"label": "Selector"},
    )


def p_Index(p):
    '''
    Index : LBRACKET RepeatNewline Expression RBRACKET
    '''
    p[0] = Node("void", p[3].children, {"label": "Index"})


# Arguments = "(" [ ( ExpressionList | Type [ "," ExpressionList ] ) [ "..." ] [ "," ] ] ")" .
def p_Argument(p):
    '''
    Arguments : LPAREN RepeatNewline ExpressionList RPAREN
              | LPAREN RepeatNewline RPAREN
    '''
    if len(p) == 4:
        p[0] = Node("void", [], {"label": "Arguments"})
    else:
        p[0] = Node("void", p[3].children, {"label": "Arguments"})


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


def p_empty(p):
    '''
    empty :
    '''
    pass


def p_terminator(p):
    '''
    terminator : SEMI
    '''


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
        print("Syntax error at lexpos %s:%s at lineno %s\n" %
              (p.lexpos, p.value, str(p.lineno)))
    else:
        print("Syntax error at EOF")


def main():
    global outfile
    parser = argparse.ArgumentParser(description='A Parser for Golang')
    parser.add_argument('--output', required=True, help='output dot file')
    parser.add_argument('input', help='input golang file')
    args = parser.parse_args()
    with open(args.input, 'r') as f:
        program = ''.join(f.readlines())
    lexer = lex.lex()
    yacc.yacc()
    with open(args.output, 'w+') as outfile:
        outfile.write("digraph G{\n")
        yacc.parse(program, tracking=True)


if __name__ == '__main__':
    main()
