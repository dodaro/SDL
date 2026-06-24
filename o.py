from pyspel.pyspel import *

@atom
class Color:
	value: any
@atom
class Node:
	value: int
@atom
class Edge:
	node1: Node
	node2: Node
@atom
class Assign:
	node: Node
	color: Color
@atom
class Ciao:
	assign: Assign
	int2: int

problem78 = Problem()

with Assign() as a_0:
	problem78+=When(a_0.node.value==1, a_0.color.value=='"blue"').define(a_0)
with Ciao() as a2_1, Assign() as a_2:
	problem78+=When(a_2, Literal(Atom(Predicate(f"{a2_1.assign.node}=={a_2.node}")), True), a2_1.assign.color.value==a_2.color.value, a2_1.int2==2).define(a2_1)
with Color() as c_3:
	problem78+=When(c_3.value=='"red"').define(c_3)
with Node() as n_4:
	problem78+=When(n_4.value==1).define(n_4)
with Node() as n_5, Assign() as a2_7, Assign() as a4_8, Assign() as a_6:
	problem78+=When(a_6, Max({(a2_7.node.value):(a2_7, a2_7.node.value==1)})>=n_5.value, Sum({(a4_8.node.value):(a4_8)})==1, n_5.value==a_6.node.value).define(n_5)
with Color() as c_9, Assign() as a_10, Node() as n_11:
	problem78+=When(a_10, n_11, Literal(Atom(Predicate(f"{a_10.color}=={c_9}")), True), n_11.value==5).define(c_9)
with Node() as n_12, Assign() as a_13:
	problem78+=When(a_13, Literal(Atom(Predicate(f"{a_13.node}=={n_12}")), True), n_12.value>1).define(n_12)
with Edge() as e_14, Edge() as e2_15, Assign() as a_16:
	problem78+=When(e2_15, a_16, Literal(Atom(Predicate(f"{e2_15.node1}=={e_14.node1}")), True), Literal(Atom(Predicate(f"{e_14.node2}=={a_16.node}")), True)).define(e_14)

print(problem78)
