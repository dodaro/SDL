int: global_strings_len = 2;
array[1..global_strings_len] of string: global_strings = ["blue", "red"];

int: color_len = 2;
array[1..color_len] of int: color_value = [1, 2];

int: node_len = 1;
array[1..node_len] of int: node_value = [1];

int: assign_len = 1;
array[1..assign_len] of int: assign_node_value = [1];
array[1..assign_len] of int: assign_color_value = [1];


array[1..node_len, 1..node_len] of var bool: edge;
array[1..node_len, 1..node_len] of var 0..node_len * node_len: rank_edge;

constraint forall(edge_node1 in 1..node_len, edge_node2 in 1..node_len)(
    edge[edge_node1, edge_node2] <-> (
      (exists(e2_node2 in 1..node_len, a_base in 1..assign_len)(
        edge[edge_node1, e2_node2] /\ edge_node2 == assign_node_value[a_base]
    ))
    )
);


constraint forall(edge_node1 in 1..node_len, edge_node2 in 1..node_len)(
    edge[edge_node1, edge_node2] -> (
      (exists(e2_node2 in 1..node_len, a_base in 1..assign_len)(
        (edge[edge_node1, e2_node2] /\ rank_edge[edge_node1, edge_node2] > rank_edge[edge_node1, e2_node2]) /\ edge_node2 == assign_node_value[a_base]
    ))
    )
);

array[1..node_len, 1..color_len] of var bool: assign;
array[1..color_len] of var bool: color;
array[1..node_len] of var bool: node;
constraint forall(assign_node in 1..node_len, assign_color in 1..color_len)(
    assign[assign_node, assign_color] <-> (
      (node_value[assign_node] == 1 /\ color_value[assign_color] == 1)
    )
);

constraint forall(color_base in 1..color_len)(
    color[color_base] <-> (
      (color_value[color_base] == 2)
      \/ (exists(Assign_base in 1..assign_len, n_base in 1..node_len)(
        color_value[color_base] == assign_color_value[Assign_base] /\ node_value[n_base] == 5
    ))
    )
);

constraint forall(node_base in 1..node_len)(
    node[node_base] <-> (
      (node_value[node_base] == 1)
      \/ (exists(a_base in 1..assign_len)(
        node_value[node_base] == assign_node_value[a_base] /\ ((
        exists(a2_aggr in 1..assign_len)(
            assign_node_value[a2_aggr] == 1
        )
    ) /\ (max([ assign_node_value[a2_aggr] | a2_aggr in 1..assign_len  where assign_node_value[a2_aggr] == 1 ])) >= node_value[node_base]) /\ (sum(a4_aggr in 1..assign_len)(assign_node_value[a4_aggr])) == 1
    ))
      \/ (exists(a_base in 1..assign_len)(
        node_value[node_base] == assign_node_value[a_base] /\ node_value[node_base] > 1
    ))
    )
);

output [
    "Assign(Node(\(node_value[i_1])), Color(\(global_strings[color_value[i_2]])))\n"
    | i_1 in 1..node_len, i_2 in 1..color_len where fix(assign[i_1, i_2])
];
output [
    "Color(\(global_strings[color_value[i_1]]))\n"
    | i_1 in 1..color_len where fix(color[i_1])
];
output [
    "Node(\(node_value[i_1]))\n"
    | i_1 in 1..node_len where fix(node[i_1])
];
output [
    "Edge(Node(\(node_value[i_1])), Node(\(node_value[i_2])))\n"
    | i_1 in 1..node_len, i_2 in 1..node_len where fix(edge[i_1, i_2])
];

solve satisfy;
