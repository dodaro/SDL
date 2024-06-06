
assign(node(N1),color(C1)) : color(C), color(C1)==color(C), node(N1)==node(N)} = 1 :- node(N).

:- assign(node(X1),color(C1)), assign(node(X2),color(C2)), edge(node(X3),node(X4)), node(X1) != node(X2), node(X1) == node(X3), node(X1) == node(X4).