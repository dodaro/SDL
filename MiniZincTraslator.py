import re

class MinizincGenerator:
    def __init__(self, validator, list_show):
        self.v = validator 
        self.list_show = list_show

    def _build_output_string(self, root_rec, current_rec, idx_var, prefix=""):
        parts = []
        for ad in self.v.get_flattened_attrs(current_rec):
            attr_name = ad['name']
            attr_type = ad['type']
            arr_name = f"{root_rec.lower()}_{attr_name}"
            if attr_type in ['int', 'str', 'any']:
                if self._is_string_attr(current_rec, attr_name):
                    parts.append(f"\\(global_strings[{arr_name}[{idx_var}]])")
                else:
                    parts.append(f"\\({arr_name}[{idx_var}])")
            else:
                inner = self._build_output_string(root_rec, attr_type, idx_var, f"{prefix}{attr_name}_")
                parts.append(f"{attr_type}({inner})")
        return ", ".join(parts)
        
    def _is_string_attr(self, record_name, attr_name):
        attrs = self.v.records.get(record_name, [])
        attr_type = None
        for ad in attrs:
            if ad['name'] == attr_name:
                attr_type = ad['type']
                break
        
        if attr_type is None:
            return False
            
        if attr_type == 'str':
            return True
        if attr_type == 'any':
            flat_attrs = self.v.get_flattened_attrs(record_name)
            col_idx = None
            for i, fad in enumerate(flat_attrs):
                if fad['name'] == attr_name:
                    col_idx = i
                    break
            if col_idx is not None:
                fact_list = self.v.facts.get(record_name, [])
                for tup in fact_list:
                    if col_idx < len(tup):
                        val = tup[col_idx]
                        if val is not None and val in self.v.id_to_string:
                            return True
            return False
            
        return False
    
    def generate(self):
        minizinc_code = ""
        if self.v.string_counter > 1:
            mzn_strings = [self.v.id_to_string[i] for i in range(1, self.v.string_counter)]
            formatted_strings = "[" + ", ".join(f'"{s}"' for s in mzn_strings) + "]"
            minizinc_code += f"int: global_strings_len = {self.v.string_counter - 1};\n"
            minizinc_code += f"array[1..global_strings_len] of string: global_strings = {formatted_strings};\n\n"
        
        for record_name in self.v.records.keys():
            is_guess = record_name in getattr(self.v, 'guess_domains', {})
            is_idb = record_name in getattr(self.v, 'rule_bodies', {})
            has_attrs = len(self.v.records.get(record_name, [])) > 0
            fact_list = self.v.facts.get(record_name, [])
            unique_sorted_facts = sorted(list(set(fact_list)))
            length = len(unique_sorted_facts)
            is_used_as_type = any(
                ad['type'] == record_name
                for rec_attrs in self.v.records.values()
                for ad in rec_attrs
            )
            if length == 0 and has_attrs:
                if is_used_as_type:
                    raise ValueError(f"Domain error: No static facts provided for record '{record_name}'. You must define at least one static fact.")
                elif not is_guess and not is_idb:
                    raise ValueError(f"Domain error: No facts provided or inferred for record '{record_name}'. You must define at least one static fact.")
            if length > 0:
                minizinc_code += f"int: {record_name.lower()}_len = {length};\n"
                record_attributes = self.v.get_flattened_attrs(record_name)
                for col_idx, attr_dict in enumerate(record_attributes):
                    attr_name = attr_dict["name"]
                    col_values = [tup[col_idx] for tup in unique_sorted_facts]
                    if None in col_values:
                        continue
                    arr_name = f"{record_name.lower()}_{attr_name}"
                    mzn_type = "int" 
                    formatted_vals = str(col_values)
                    minizinc_code += f"array[1..{record_name.lower()}_len] of {mzn_type}: {arr_name} = {formatted_vals};\n"
                minizinc_code += "\n"
        for record_name in self.v.records.keys():
            fact_list = self.v.facts.get(record_name, [])
            if not fact_list: continue
            unique_sorted_facts = sorted(list(set(fact_list)))
            record_attributes = self.v.get_flattened_attrs(record_name)
            for col_idx, attr_dict in enumerate(record_attributes):
                col_values = [tup[col_idx] for tup in unique_sorted_facts]
                if None in col_values:
                    attr_name = attr_dict["name"]
                    arr_name = f"{record_name.lower()}_{attr_name}"
                    minizinc_code += f"array[1..{record_name.lower()}_len] of var int: {arr_name};\n"
        processed_groups = set()
        for rec_name, g_dom in self.v.guess_domains.items():
            limits = g_dom.get('limits', [])
            header = self.v.rule_headers.get(rec_name, {})
            num_from = len(g_dom['from'])
            base_iters = header.get('indices', [f"i{idx}" for idx in range(num_from)])[:num_from]
            base_ranges = header.get('iters', [f"i{idx} in 1..{g_dom['from'][idx].lower()}_len" for idx in range(num_from)])[:num_from]
            
            def make_val_expr(val_str):
                val_str = str(val_str)
                if not val_str.isdigit():
                    def replacer(match):
                        token = match.group(0)
                        if token in ["div", "mod", "sum", "max", "min", "count"]: return token
                        if "." in token:
                            parts = token.split(".")
                            base, attr = parts[0].lower(), "_".join(parts[1:])
                            from_lower = [r.lower() for r in g_dom['from']]
                            if base in from_lower:
                                idx = from_lower.index(base)
                                return f"{from_lower[idx]}_{attr}[{base_iters[idx]}]"
                            elif len(from_lower) == 1:
                                return f"{from_lower[0]}_{attr}[{base_iters[0]}]"
                            return f"{base}_{attr}[{base_iters[0]}]"
                        return token
                    return re.sub(r'\b[a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z0-9_]+)*\b', replacer, val_str)
                return val_str
            if g_dom.get('fallback_bool'):
                dim_list = [f"1..{r.lower()}_len" for r in g_dom.get('from', [])] + [f"1..{tr.lower()}_len" for tr in g_dom.get('to_recs', [])]
                arr_declaration = f"array[{', '.join(dim_list)}] of var bool: {rec_name.lower()};\n"
                minizinc_code += arr_declaration  
                if limits:
                    group_id = g_dom.get('group_id')
                    if group_id:
                        if group_id not in processed_groups:
                            processed_groups.add(group_id)
                            group_recs = [name for name, dom in self.v.guess_domains.items() if dom.get('group_id') == group_id]
                            iters = [f"i{idx}" for idx in range(len(g_dom['from']))]
                            ranges = [f"{iters[idx]} in 1..{r.lower()}_len" for idx, r in enumerate(g_dom['from'])]
                            sum_exprs = []
                            for g_rec in group_recs:
                                g_to_recs = self.v.guess_domains[g_rec].get('to_recs', [])
                                g_val_iters = [f"i_val_{g_rec.lower()}_{idx}" for idx in range(len(g_to_recs))]
                                g_val_dims = [f"{g_val_iters[idx]} in 1..{g_to_recs[idx].lower()}_len" for idx in range(len(g_to_recs))]
                                sum_exprs.append(f"(sum({', '.join(g_val_dims)})(bool2int({g_rec.lower()}[{', '.join(iters + g_val_iters)}])))")
                            combined_sum = " + ".join(sum_exprs)
                            sub_conds = []
                            for lim in limits:
                                val_expr = make_val_expr(lim['val'])
                                op = "==" if lim['type'] == 'exactly' else ">=" if lim['type'] == 'at least' else "<="
                                sub_conds.append(f"({combined_sum}) {op} {val_expr}")
                            minizinc_code += f"constraint forall({', '.join(ranges)})(\n    " + ' /\\ '.join(sub_conds) + "\n);\n"

                    else:
                        iters = base_iters
                        ranges = base_ranges
                        to_recs = g_dom.get('to_recs', [])
                        val_iters = [f"i_val_{idx}" for idx in range(len(to_recs))]
                        val_dims = [f"{val_iters[idx]} in 1..{to_recs[idx].lower()}_len" for idx in range(len(to_recs))]
                        if not val_dims:
                            global_sub_conds = []
                            local_sub_conds = []
                            access_str = f"[{', '.join(iters)}]" if iters else ""
                            sum_expr_global = f"sum({', '.join(ranges)})(bool2int({rec_name.lower()}{access_str}))" if ranges else f"bool2int({rec_name.lower()}{access_str})"
                            expr_local = f"bool2int({rec_name.lower()}{access_str})"
                            for lim in limits:
                                val_expr = make_val_expr(lim['val'])
                                op = "==" if lim['type'] == 'exactly' else ">=" if lim['type'] == 'at least' else "<="
                                if ranges and op == "<=" and str(val_expr) == "1":
                                    pass
                                elif ranges and op in ["==", ">="]: 
                                    local_sub_conds.append(f"{expr_local} {op} {val_expr}")
                                else:
                                    global_sub_conds.append(f"{sum_expr_global} {op} {val_expr}")
                            preconds = header.get('preconds', [])
                            if preconds or local_sub_conds:
                                precond_str = " /\\ ".join(preconds) if preconds else ""
                                local_body = " /\\ ".join(local_sub_conds) if local_sub_conds else "true"
                                zero_cond = f"{rec_name.lower()}{access_str} == false"
                                if ranges:
                                    if precond_str:
                                        minizinc_code += f"constraint forall({', '.join(ranges)})(\n    if {precond_str} then {local_body} else {zero_cond} endif\n);\n"
                                    else:
                                        minizinc_code += f"constraint forall({', '.join(ranges)})(\n    {local_body}\n);\n"
                                else:
                                    if precond_str:
                                        minizinc_code += f"constraint if {precond_str} then {local_body} else {zero_cond} endif;\n"
                                    else:
                                        minizinc_code += f"constraint {local_body};\n"
                            if global_sub_conds:
                                minizinc_code += f"constraint {' /\\ '.join(global_sub_conds)};\n"
                        else:
                            access_str = f"[{', '.join(iters + val_iters)}]" if (iters + val_iters) else ""
                            sum_expr = f"sum({', '.join(val_dims)})(bool2int({rec_name.lower()}{access_str}))"
                            sub_conds = []
                            for lim in limits:
                                val_expr = make_val_expr(lim['val'])
                                op = "==" if lim['type'] == 'exactly' else ">=" if lim['type'] == 'at least' else "<="
                                sub_conds.append(f"{sum_expr} {op} {val_expr}")
                            if sub_conds:
                                preconds = header.get('preconds', [])
                                if ranges:
                                    if preconds:
                                        precond_str = " /\\ ".join(preconds)
                                        card_limits = " /\\ ".join(sub_conds)
                                        zero_cond = f"{sum_expr} == 0"
                                        minizinc_code += f"constraint forall({', '.join(ranges)})(\n    if {precond_str} then {card_limits} else {zero_cond} endif\n);\n"
                                    else:
                                        minizinc_code += f"constraint forall({', '.join(ranges)})(\n    {' /\\ '.join(sub_conds)}\n);\n"
                                else:
                                    if preconds:
                                        precond_str = " /\\ ".join(preconds)
                                        card_limits = " /\\ ".join(sub_conds)
                                        zero_cond = f"{sum_expr} == 0"
                                        minizinc_code += f"constraint if {precond_str} then {card_limits} else {zero_cond} endif;\n"
                                    else:
                                        minizinc_code += f"constraint {' /\\ '.join(sub_conds)};\n"
            else:
                dim_list = [f"1..{r.lower()}_len" for r in g_dom['from']]
                dim_str = ", ".join(dim_list)
                to_recs = g_dom.get('to_recs', [])
                to_rec = to_recs[0] if to_recs else ''
                preconds = header.get('preconds', [])
                actual_to = to_rec if to_rec else rec_name
                has_facts = len(set(self.v.facts.get(actual_to, []))) > 0
                to_len = f"{actual_to.lower()}_len" if has_facts else "1"
                is_exactly_1 = len(limits) == 1 and limits[0]['type'] == 'exactly' and str(limits[0]['val']).strip() == "1" and not preconds
                is_at_most_1 = len(limits) == 1 and limits[0]['type'] == 'at most' and str(limits[0]['val']).strip() == "1" and not preconds
                def get_decl(mzn_type):
                    return f"array[{dim_str}] of var {mzn_type}: {rec_name.lower()};\n" if dim_str else f"var {mzn_type}: {rec_name.lower()};\n"
                if not to_rec or to_rec.lower() == rec_name.lower():
                    if is_exactly_1:
                        minizinc_code += get_decl(f"1..{to_len}")
                    elif is_at_most_1:
                        minizinc_code += get_decl(f"0..{to_len}")
                    else:
                        minizinc_code += get_decl("0..1")
                else:
                    if is_exactly_1:
                        minizinc_code += get_decl(f"1..{to_len}")
                    elif is_at_most_1:
                        minizinc_code += get_decl(f"0..{to_len}")
                    else:
                        arr_declaration = get_decl(f"set of 1..{to_len}")
                        if not limits:
                            minizinc_code += arr_declaration
                        else:
                            iters = base_iters
                            ranges = base_ranges
                            sub_conds = []
                            arr_acc = f"{rec_name.lower()}[{', '.join(iters)}]" if iters else rec_name.lower()
                            for lim in limits:
                                val_expr = make_val_expr(lim['val'])
                                op = "==" if lim['type'] == 'exactly' else ">=" if lim['type'] == 'at least' else "<="
                                sub_conds.append(f"card({arr_acc}) {op} {val_expr}")
                            if preconds:
                                precond_str = " /\\ ".join(preconds)
                                card_limits = " /\\ ".join(sub_conds)
                                zero_cond = f"card({arr_acc}) == 0"
                                constraint = f"constraint forall({', '.join(ranges)})(\n    if {precond_str} then {card_limits} else {zero_cond} endif\n);\n" if ranges else f"constraint if {precond_str} then {card_limits} else {zero_cond} endif;\n"
                                minizinc_code += arr_declaration + constraint
                            else:
                                constraint = f"constraint forall({', '.join(ranges)})( {' /\\ '.join(sub_conds)} );\n" if ranges else f"constraint {' /\\ '.join(sub_conds)};\n"
                                minizinc_code += arr_declaration + constraint
            if rec_name in self.v.rule_bodies and self.v.rule_bodies[rec_name]:
                header = self.v.rule_headers.get(rec_name)
                if header:
                    combined_body = "\n      \\/ ".join(f"({b})" for b in self.v.rule_bodies[rec_name])
                    clean_test = "".join(combined_body.split())
                    if clean_test not in ["(true)", "true", "((true))"]:
                        is_bool = g_dom.get('fallback_bool')
                        is_set = not is_bool and len(header['indices']) > len(g_dom['from'])
                        if is_bool:
                            arr_access = f"{rec_name.lower()}[{', '.join(header['indices'])}]"
                            logic_constraint = f"constraint forall({', '.join(header['iters'])})(\n    {arr_access} -> ({combined_body})\n);\n"
                        elif is_set:
                            set_val = header['indices'][-1]         
                            set_keys = header['indices'][:-1]       
                            arr_access = f"{set_val} in {rec_name.lower()}[{', '.join(set_keys)}]"
                            logic_constraint = f"constraint forall({', '.join(header['iters'])})(\n    {arr_access} -> ({combined_body})\n);\n"
                        else:
                            logic_constraint = f"constraint forall({', '.join(header['iters'])})(\n    {combined_body}\n);\n"
                        minizinc_code += logic_constraint
        normal_idb_declarations = ""
        normal_idb_constraints = ""
        recursive_declarations = ""
        recursive_constraints = ""
        for rec_name, bodies in self.v.rule_bodies.items():
            if rec_name in self.v.guess_domains:
                continue  
            header = self.v.rule_headers[rec_name]
            is_recursive = getattr(self.v, 'is_recursive_active', False) and rec_name in getattr(self.v, 'recursive_records', set())
            arr_base_name = rec_name.lower()
            if is_recursive:
                if header['dims']:
                    upper_bounds = [d.split("..")[1] for d in header['dims']]
                    max_depth_str = " * ".join(upper_bounds)
                else:
                    max_depth_str = "1"
                dim_str = ", ".join(header['dims'])
                indices_str = ", ".join(header['indices'])
                iters_str = ", ".join(header['iters'])
                if dim_str:
                    arr_declaration = f"array[{dim_str}] of var bool: {arr_base_name};\n"
                    rank_declaration = f"array[{dim_str}] of var 0..{max_depth_str}: rank_{arr_base_name};\n"
                else:
                    arr_declaration = f"var bool: {arr_base_name};\n"
                    rank_declaration = f"var 0..{max_depth_str}: rank_{arr_base_name};\n"
                recursive_declarations += f"\n{arr_declaration}{rank_declaration}"
                bodies_acyclic = getattr(self.v, 'rule_bodies_acyclic', {}).get(rec_name, bodies)
                combined_body_logical = "\n      \\/ ".join(f"({b})" for b in bodies) 
                combined_body_acyclic = "\n      \\/ ".join(f"({b})" for b in bodies_acyclic)
                arr_access = f"{arr_base_name}[{indices_str}]" if indices_str else arr_base_name
                if iters_str:
                    constraint_logical = f"\nconstraint forall({iters_str})(\n    {arr_access} <-> (\n      {combined_body_logical}\n    )\n);\n"
                    constraint_acyclic = f"\nconstraint forall({iters_str})(\n    {arr_access} -> (\n      {combined_body_acyclic}\n    )\n);\n"
                else:
                    constraint_logical = f"\nconstraint {arr_access} <-> (\n      {combined_body_logical}\n);\n"
                    constraint_acyclic = f"\nconstraint {arr_access} -> (\n      {combined_body_acyclic}\n);\n"
                recursive_constraints += constraint_logical + "\n" + constraint_acyclic + "\n"
            else:
                if header['dims']:
                    arr_declaration = f"array[{', '.join(header['dims'])}] of var bool: {arr_base_name};\n"
                else:
                    arr_declaration = f"var bool: {arr_base_name};\n"
                combined_body = "\n      \\/ ".join(f"({b})" for b in bodies)
                arr_access = f"{arr_base_name}[{', '.join(header['indices'])}]" if header['indices'] else arr_base_name
                if header['iters']:
                    constraint = f"constraint forall({', '.join(header['iters'])})(\n    {arr_access} <-> (\n      {combined_body}\n    )\n);\n"
                else:
                    constraint = f"constraint {arr_access} <-> (\n      {combined_body}\n);\n"
                normal_idb_declarations += arr_declaration
                normal_idb_constraints += constraint + "\n"
        minizinc_code += recursive_declarations
        minizinc_code += recursive_constraints
        minizinc_code += normal_idb_declarations
        minizinc_code += normal_idb_constraints
        if self.v.deny_constraints:
            for deny_mzn in self.v.deny_constraints:
                minizinc_code += deny_mzn + "\n"
        
        for target_rec, g_dom in self.v.guess_domains.items():
            to_recs = g_dom.get('to_recs', [])
            to_rec_name = to_recs[0] if to_recs else ''
            limits = g_dom.get('limits', [])
            is_bool = g_dom.get('fallback_bool', False)
            preconds = self.v.rule_headers.get(target_rec, {}).get('preconds', [])
            is_functional = (len(limits) == 1 and 
                             limits[0]['type'] in ['exactly', 'at most'] and 
                             str(limits[0]['val']).strip() == "1" and 
                             not preconds and not is_bool)
            arr_name = target_rec.lower()
            from_dims = g_dom.get('from', [])
            idx_vars = [f"i_{idx+1}" for idx in range(len(from_dims))]
            idx_loops = [f"{idx_vars[idx]} in 1..{dim.lower()}_len" for idx, dim in enumerate(from_dims)]
            loops_str = ", ".join(idx_loops) 
            arr_access = f"{arr_name}[{', '.join(idx_vars)}]" if idx_vars else arr_name
            from_exprs = []
            for idx, dim in enumerate(from_dims):
                dim_idx_var = idx_vars[idx]
                dim_actual = dim
                has_facts = len(set(self.v.facts.get(dim_actual, []))) > 0
                if dim_actual in self.v.records and self.v.records[dim_actual] and has_facts:
                    inner_str = self._build_output_string(dim_actual, dim_actual, dim_idx_var)
                    from_exprs.append(f"{dim_actual}({inner_str})")
                else:
                    from_exprs.append(f"{dim_actual}(\\({dim_idx_var}))")
            display_keys = ", ".join(from_exprs)
            is_multi_target = len(to_recs) > 1
            if is_bool:
                if to_recs:
                    target_vals = [f"c_{idx}" for idx in range(len(to_recs))]
                    bool_acc = f"{arr_name}[{', '.join(idx_vars + target_vals)}]" if idx_vars else f"{arr_name}[{', '.join(target_vals)}]"
                    extra_loops = [f"{target_vals[idx]} in 1..{to_recs[idx].lower()}_len" for idx in range(len(to_recs))]
                    extra_loop = ", ".join(extra_loops)
                    
                    if is_multi_target:
                        val_expr = "(" + ", ".join([f"\\({tv})" for tv in target_vals]) + ")"
                        to_rec_name = ", ".join(to_recs)
                        target_val = ""
                    else:
                        target_val = target_vals[0]
                else:
                    bool_acc = f"{arr_name}[{', '.join(idx_vars)}]" if idx_vars else arr_name
                    extra_loop = ""
                    target_val = ""
                    
                condition = f"fix({bool_acc})"
            elif is_functional:
                target_val = f"fix({arr_access})"
                extra_loop = ""
                condition = f"fix({arr_access}) > 0"
            elif not to_rec_name or to_rec_name.lower() == target_rec.lower():
                actual_to = to_rec_name if to_rec_name else target_rec
                has_facts = len(set(self.v.facts.get(actual_to, []))) > 0
                target_val = f"fix({arr_access})" if has_facts else "1"
                extra_loop = ""
                condition = f"fix({arr_access}) > 0"
            else:
                target_val = "c"
                extra_loop = f"c in fix({arr_access})"
                condition = "true"
            if not (is_bool and is_multi_target):
                actual_to = to_rec_name if to_rec_name else target_rec
                has_actual_facts = len(set(self.v.facts.get(actual_to, []))) > 0

                if actual_to in self.v.records and self.v.records[actual_to] and has_actual_facts:
                    inner_str = self._build_output_string(actual_to, actual_to, target_val)
                    val_expr = f"{actual_to}({inner_str})"
                else:
                    val_expr = f"{actual_to}(\\({target_val}))"
            display_name = f"{target_rec}({display_keys})" if display_keys else target_rec
            if to_rec_name:
                string_to_print = f'"{display_name} -> {val_expr}\\n"'
            else:
                string_to_print = f'"{display_name}\\n"'
                
            loop_parts = []
            if loops_str: loop_parts.append(loops_str)
            if extra_loop: loop_parts.append(extra_loop)
            final_loop_str = ", ".join(loop_parts)

            minizinc_code += "output [\n"
            if final_loop_str:
                minizinc_code += f'    {string_to_print}\n'
                if condition and condition != "true":
                    minizinc_code += f"    | {final_loop_str} where {condition}\n"
                else:
                    minizinc_code += f"    | {final_loop_str}\n"
            else:
                if condition and condition != "true":
                    minizinc_code += f'    if {condition} then {string_to_print} else "" endif\n'
                else:
                    minizinc_code += f'    {string_to_print}\n'
            minizinc_code += "];\n"
        
        for target_rec, bodies in self.v.rule_bodies.items():
            if target_rec in self.v.guess_domains or target_rec not in self.list_show:
                continue
            header = self.v.rule_headers.get(target_rec)
            if not header:
                continue
            dims = header.get('dims', [])
            idx_vars = [f"i_{idx+1}" for idx in range(len(dims))]
            idx_loops = [f"{idx_vars[idx]} in {dims[idx]}" for idx in range(len(dims))]
            loops_str = ", ".join(idx_loops)
            from_exprs = []
            for idx, dim_str in enumerate(dims):
                dim_idx_var = idx_vars[idx]
                dim_name = dim_str.split("..")[-1].replace("_len", "").strip()
                dim_actual = next((k for k in self.v.records.keys() if k.lower() == dim_name), dim_name)
                has_facts = len(set(self.v.facts.get(dim_actual, []))) > 0
                if dim_actual in self.v.records and self.v.records[dim_actual] and has_facts:
                    inner_str = self._build_output_string(dim_actual, dim_actual, dim_idx_var)
                    if inner_str.startswith(f"{dim_actual}("):
                         from_exprs.append(inner_str)
                    else:
                         from_exprs.append(f"{dim_actual}({inner_str})")
                else:
                    from_exprs.append(f"{dim_actual}(\\({dim_idx_var}))")
            
            display_keys = ", ".join(from_exprs)
            arr_access = f"{target_rec.lower()}[{', '.join(idx_vars)}]" if idx_vars else target_rec.lower()
            minizinc_code += "output [\n"
            if not idx_vars:
                minizinc_code += f'    if fix({arr_access}) then "{target_rec}\\n" else "" endif\n'
            else:
                if display_keys.startswith(f"{target_rec}("):
                    display_name = display_keys
                else:
                    display_name = f"{target_rec}({display_keys})"
                minizinc_code += f'    "{display_name}\\n"\n'
                minizinc_code += f"    | {loops_str} where fix({arr_access})\n"
            minizinc_code += "];\n"
            
        for record_name in self.list_show:
            if record_name in self.v.guess_domains:
                continue  
            if record_name in self.v.rule_bodies:
                continue 
            fact_list = self.v.facts.get(record_name, [])
            if not fact_list:
                continue
            unique_sorted_facts = sorted(list(set(fact_list)))
            if len(unique_sorted_facts) == 0:
                continue
            idx_var = "i_1"
            loop_str = f"{idx_var} in 1..{record_name.lower()}_len"
            inner_str = self._build_output_string(record_name, record_name, idx_var)
            display_name = f"{record_name}({inner_str})" if inner_str else record_name
            minizinc_code += "output [\n"
            minizinc_code += f'    "{display_name}\\n"\n'
            minizinc_code += f"    | {loop_str} where fix({record_name.lower()}[{idx_var}])\n" 
            minizinc_code += "];\n"

        if hasattr(self.v, 'weak_constraints') and self.v.weak_constraints:
            levels_dict = {}
            for wc in self.v.weak_constraints:
                lvl = wc['level']
                if lvl not in levels_dict:
                    levels_dict[lvl] = []
                levels_dict[lvl].append(wc)
            sorted_levels = sorted(levels_dict.keys())
            minizinc_code += "\n"
            level_max_costs = {}
            for lvl in sorted_levels:
                cost_exprs = [wc['max_cost_expr'] for wc in levels_dict[lvl]]
                combined_max = " + ".join(cost_exprs)
                minizinc_code += f"int: max_cost_lvl{lvl} = {combined_max};\n"
                level_max_costs[lvl] = f"max_cost_lvl{lvl}"
            multiplier_vars = {}
            prev_mult = "1"
            for idx, lvl in enumerate(sorted_levels):
                if idx == 0:
                    multiplier_vars[lvl] = "1"
                else:
                    prev_lvl = sorted_levels[idx-1]
                    mult_name = f"mult_lvl{lvl}"
                    minizinc_code += f"int: {mult_name} = {prev_mult} * ({level_max_costs[prev_lvl]} + 1);\n"
                    multiplier_vars[lvl] = mult_name
                    prev_mult = mult_name
            minizinc_code += "\n"
            penalty_vars = []
            for lvl in sorted_levels:
                for wc in levels_dict[lvl]:
                    lex_multiplier = multiplier_vars[lvl]
                    wc_expr_mapped = wc['expr'] 
                    minizinc_code += f"var int: {wc['name']} = ({wc_expr_mapped}) * {lex_multiplier};\n"
                    penalty_vars.append(wc['name'])
            minizinc_code += f"\nvar int: total_penalty = {' + '.join(penalty_vars)};\n"
            minizinc_code += "solve minimize total_penalty;\n"
            minizinc_code += "output [\"\\n Current Penalty Value: \\(total_penalty)\\n\"];\n"
        else:
            minizinc_code += "\nsolve satisfy;\n"
        return minizinc_code