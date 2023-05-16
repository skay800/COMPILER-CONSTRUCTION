#!/usr/bin/env python2

import argparse
import re
import sys

import ply.lex as lex


class GoLexer(object):

    reserved = {
        'break': 'BREAK',
        'default': 'DEFAULT',
        'func': 'FUNC',
        'interface': 'INTERFACE',
        'select': 'SELECT',
        'case': 'CASE',
        'defer': 'DEFER',
        'go': 'GO',
        'map': 'MAP',
        'struct': 'STRUCT',
        'chan': 'CHAN',
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
        'LT', 'GT', 'LE', 'GE', 'EQ', 'NE', 'NOT', 'LNOT', 'LOR', 'LAND',
        'LARROW', 'PLUS', 'MINUS', 'TIMES', 'DIVIDE', 'MODULO', 'OR', 'XOR',
        'LSHIFT', 'RSHIFT', 'AND', 'ANDNOT', 'INCR', 'DECR', 'EQUALS',
        'TIMESEQUAL', 'DIVEQUAL', 'MODEQUAL', 'PLUSEQUAL', 'MINUSEQUAL',
        'LSHIFTEQUAL', 'RSHIFTEQUAL', 'ANDEQUAL', 'OREQUAL', 'XOREQUAL',
        'AUTOASIGN', 'ANDNOTEQUAL', 'ID', 'LPAREN', 'RPAREN', 'LBRACKET',
        'RBRACKET', 'LBRACE', 'RBRACE', 'COMMA', 'PERIOD', 'SEMI', 'COLON',
        'ELLIPSIS', 'CHARACTER', 'COMMENT', 'MULTICOMMENT', 'INTEGER', 'FLOAT',
        'STRINGVAL'
    ] + list(set(combined_map.values()))

    # Regular expression rules for operators

    # Relation operators
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
    t_LARROW = r'<\-'

    # Arithmetic operators
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

    # Assignment operators
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

    def t_FLOAT(self, t):
        r'(\d+\.\d*(e|E)[\+|\-]?\d+)|((\d+)(e|E)[\+|\-]?\d+)|(\.\d+(e|E)[\+|\-]?\d+)|(\d+\.\d*)|(\.\d+)'
        return t

    def t_INTEGER(self, t):
        r'0[xX][0-9a-fA-F]+|\d+'
        return t

    def t_ID(self, t):
        r'[a-zA-Z_][a-zA-Z_0-9]*'
        t.type = self.combined_map.get(t.value, 'ID')
        return t

    def t_MULTICOMMENT(self, t):
        r'/\*(.|\n)*?\*/'
        t.lexer.lineno += t.value.count('\n')
        return t

    def t_COMMENT(self, t):
        r'//.*\n'
        t.lexer.lineno += 1
        return t

    def t_newline(self, t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    def t_error(self, t):
        print(f"Illegal character '{str(t.value[0])}'")
        print(f"Value of the illegal token is '{str(t.value)}'")
        t.lexer.skip(1)

    def build(self, **kwargs):
        self.lexer = lex.lex(module=self, **kwargs)

    def find_column(self, raw_data, token):
        line_start = raw_data.rfind('\n', 0, token.lexpos) + 1
        return (token.lexpos - line_start) + 1

    def lex(self, raw_data, out_file, config_file):
        self.lexer.input(raw_data)
        tok = self.lexer.token()
        line, pos = tok.lineno, tok.lexpos
        while tok:
            print(str(tok).replace('LexToken', ''))
            if tok.type == 'COMMENT':
                pos -= 1
            tok = self.lexer.token()

            # print error if token is not found


def main():
    parser = argparse.ArgumentParser(description='A Lexer for Golang')
    parser.add_argument(
        '--cfg', required=True, help='color configuration file')
    parser.add_argument('input', help='input Golang file')
    parser.add_argument('--out', required=True, help='output file')
    args = parser.parse_args()
    with open(args.input, 'r') as f:
        raw_data = ''.join(f.readlines())
    raw_data = re.sub(r'\t', '    ', raw_data)
    lexer = GoLexer()
    lexer.build()
    lexer.lex(raw_data, args.out, args.cfg)


if __name__ == '__main__':
    main()
