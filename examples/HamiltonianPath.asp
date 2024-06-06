1 <= {inCycle(node(X), node(Y)) : arc(node(X1), node(Y1)), node(X)==node(X1), node(Y)==node(Y1)} = 1 :- node(X).
:- node(X), #count{node(Y) : inCycle(node(Y1), node(X1)), node(Y)==node(Y1), node(X)==node(X1)} <= 1.
reached(node(X1)) :- start(node(X)), node(X)==node(X1).
reached(node(X1)) :- reached(node(Y1)), inCycle(node(Y), node(X)), node(X)==node(X1), node(Y)==node(Y1).
:- node(X), not reached(node(X1)), node(X)==node(X1).