int: node_len = 4;
array[1..node_len] of int: node_id = [1, 2, 3, 4];

int: arc_len = 6;
array[1..arc_len] of int: arc_first_id = [1, 1, 2, 2, 3, 4];
array[1..arc_len] of int: arc_second_id = [2, 3, 3, 4, 4, 1];

int: start_len = 1;
array[1..start_len] of int: start_node_id = [1];

array[1..node_len] of var 1..arc_len: incycle;
constraint forall(incycle_node in 1..node_len)(
    (incycle_node == arc_first_id[incycle[incycle_node]])
);

array[1..node_len] of var bool: reached;
array[1..node_len] of var 0..node_len: rank_reached;

constraint forall(reached_node in 1..node_len)(
    reached[reached_node] <-> (
      (exists(Start_base in 1..start_len)(
        start_node_id[Start_base] == reached_node
    ))
      \/ (exists(r2_node in 1..node_len, InCycle_node_base in 1..node_len)(
        reached[r2_node] /\ r2_node == arc_first_id[incycle[InCycle_node_base]] /\ reached_node == arc_second_id[incycle[InCycle_node_base]]
    ))
    )
);


constraint forall(reached_node in 1..node_len)(
    reached[reached_node] -> (
      (exists(Start_base in 1..start_len)(
        start_node_id[Start_base] == reached_node
    ))
      \/ (exists(r2_node in 1..node_len, InCycle_node_base in 1..node_len)(
        (reached[r2_node] /\ rank_reached[reached_node] > rank_reached[r2_node]) /\ r2_node == arc_first_id[incycle[InCycle_node_base]] /\ reached_node == arc_second_id[incycle[InCycle_node_base]]
    ))
    )
);

constraint forall(Node_base in 1..node_len)(
    not ((sum(InCycle_node_aggr in 1..node_len)(bool2int(Node_base == arc_second_id[incycle[InCycle_node_aggr]]))) != 1)
);
constraint forall(Node_base in 1..node_len)(
    not (not (reached[Node_base]))
);
output [
    "InCycle(Node(\(node_id[i_1]))) -> Arc(Node(\(arc_first_id[fix(incycle[i_1])])), Node(\(arc_second_id[fix(incycle[i_1])])))\n"
    | i_1 in 1..node_len where fix(incycle[i_1]) > 0
];

solve satisfy;
