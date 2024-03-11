import random
import re
from unittest import mock
from unittest.mock import patch

import pytest

from grammar import build_tree


def assert_in_transformation(code: str, content: str):
    def normalize(string):
        res = string.strip().replace("\t", "    ")
        res = re.sub(r"problem(\d+)\+=", "problem+=", res)
        return res
    tree = normalize(str(build_tree(code)))
    assert normalize(content) in tree


def test_build_tree_entity():
    assert_in_transformation("@entity Color: value: any;", """
@atom
class Color:
    value: any
    """)


def test_build_tree_aggregate():
    assert_in_transformation("""
@entity Digit:
    value: int;
    
@entity Cell: 
    row: int,
    col: int;

@entity BlockType:
    value: str;

@entity Block:
    type: BlockType,
    index: int;

@entity BlockCell:
    block: Block,
    cell: Cell;

@entity Assign:
    cell: Cell,
    digit: Digit;
    
guess from Cell
    exactly 1
        Assign
            from Digit
                where Assign.cell = Cell and Assign.digit = Digit
;    
    """, """
with Cell() as c_1, Digit() as d_2, Assign(cell = c_1, digit = d_2) as a_0:
    problem17+=When(c_1).guess({a_0:(d_2)}, exactly=1)
    """)
