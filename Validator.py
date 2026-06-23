import os
import uuid
import re
import traceback
import itertools
from lark import Lark, Transformer, exceptions, Token
from collections import defaultdict
import fileinput
import subprocess
from optparse import OptionParser
import error_messages
from MiniZincTraslator import MinizincGenerator
from PyspelTranslator import PyspelTransformer


class Graph:
    def __init__(self):
        self.graph = defaultdict(list)
        self.time_ = 0
        self.V = 0
        
    def add_vertex(self, v):
        if v not in self.graph:
            self.graph[v] = []
            self.V += 1

    def add_edge(self, u, v):
        self.add_vertex(u)
        self.add_vertex(v)
        self.graph[u].append(v)

    def scc_util(self, u, low, disc, stack_member, st):
        disc[u] = self.time_
        low[u] = self.time_
        self.time_ += 1
        stack_member[u] = True
        st.append(u)
        for v in self.graph[u]:
            if disc[v] == -1:
                self.scc_util(v, low, disc, stack_member, st)
                low[u] = min(low[u], low[v])
            elif stack_member[v]:
                low[u] = min(low[u], disc[v])
        w = -1
        length = 0
        if low[u] == disc[u]:
            while w != u:
                length += 1
                w = st.pop()
                stack_member[w] = False
        if length > 1 and recursive:
            raise ValueError(error_messages.CYCLIC_DEPENDENCY)
        
    def scc(self):
        disc = [-1] * self.V
        low = [-1] * self.V
        stack_member = [False] * self.V
        st = []
        for i in range(self.V):
            if disc[i] == -1:
                self.scc_util(i, low, disc, stack_member, st)

records_global = {}
pyspel_guess_alias = {}
guess = {}
guess_alias = {}
guess_records = {}
number = 0
target ="pyspel"
g = Graph()
num_pred = {}
num = 0
list_show = []
asp_block = ""
recursive = False

class DeclarationTransformer(Transformer):
    def __init__(self):
        self.count_guess = 0
        self.count = 0
        guess[0] = []
        guess_alias[0] = {}
        guess_records[0] = {}
        guess_alias[0]["number"] = 0
        pyspel_guess_alias[0] = {}
        pyspel_guess_alias[0]["number"] = 0

    def record_declaration(self, args):
        record_name = args[0]
        declarations = args[2].children
        if record_name in records_global.keys():
            raise ValueError(error_messages.record_defined(record_name))
        records_global[record_name] = []
        for i in range(0, len(declarations), 2):
            attr = declarations[i].children
            token = attr[2].children
            attr_type = token[0]
            if attr_type == record_name:
                raise ValueError(error_messages.RECURSIVE_DEPENDENCY_BETWEEN_RECORDS)
            attr[0].type = str(attr_type)
            records_global[record_name].append(attr[0])
        return args
    
    def guess(self, _):
        self.count_guess += 1
        self.count=0
        guess[self.count_guess] = []
        guess_records[self.count_guess] = {}
        guess_alias[self.count_guess] = {}
        guess_alias[self.count_guess]["number"] = 0
        pyspel_guess_alias[self.count_guess] = {}
        pyspel_guess_alias[self.count_guess]["number"] = 0

    def guess_definition(self, args):
        if len(args) >= 3:
            if args[1] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.alias_defined(args[1]))
            guess_alias[self.count_guess][args[1]] = args[1]
            pyspel_guess_alias[self.count_guess][args[1]] = self.add_number(args[1])
            guess_records[self.count_guess][args[1]] = args[0]
        else:
            if args[0] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.record_defined(args[0]))
            guess_alias[self.count_guess][args[0]] = args[0]
            pyspel_guess_alias[self.count_guess][args[0]] = self.number(args[0])
            guess_records[self.count_guess][args[0]] = args[0]
        guess_alias[self.count_guess]["number"] += 1
        pyspel_guess_alias[self.count_guess]["number"] += 1
    def guess_record(self, args):
        index = 0
        if args[0] == "not":
            index = 1
        if len(args) > index + 1:
            if args[index + 1] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.alias_defined(args[index + 1]))
            guess_records[self.count_guess][args[index + 1]] = args[index]
            guess[self.count_guess].append(args[index + 1])
        else:
            if args[index] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.record_defined(args[index]))
            guess_records[self.count_guess][args[index]] = args[index]
            guess[self.count_guess].append(args[index])

    def record_guess(self, args):
        index = 0
        if args[0] == "not":
            index = 1
        if len(args) > index + 1:
            if args[index + 1] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.alias_defined(args[index + 1]))
        else:
            if args[index] in guess_records[self.count_guess].keys():
                raise ValueError(error_messages.record_defined(args[index]))
        return args

    def number(self, args):
        letter = args[0].lower()
        letter += "_" + f"{self.count}"
        self.count += 1
        return letter

    def add_number(self, args):
        args = args + "_" + f"{self.count}"
        self.count += 1
        return args
    

class SDLValidator(Transformer):
    def __init__(self):
        self.facts = defaultdict(list)
        self.current_alias_map = {} 
        self.current_record = None
        self.current_alias = None
        self.current_fact_attrs = {} 
        self.records = {}
        self.records_attributes = []
        self.define_expressions = []
        self.dependencies = {}
        self.declared_alias = {}
        self.aggr_new_alias = {}
        self.defined_records = set()
        self.redefined_record = {}
        self.attributes = {}
        self.negated_atoms = []
        self.defined_record = set()
        self.guess_records = set()
        self.guess_alias = {}
        self.count_guess = 0
        self.aggr_alias = []
        self.guess_check = []
        self.negated = {}
        self.aggregate_records = set()
        self.aggr_guess_record = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.aggregate_with = []
        self.recursive_records = set()
        self.rule_bodies = defaultdict(list)
        self.rule_bodies_acyclic = defaultdict(list)
        self.rule_headers = {}
        self.guess_domains = {}
        self.raw_rules = []
        self.deny_constraints = []
        self.is_recursive_active = False
        self.string_to_id = {}
        self.id_to_string = {}
        self.string_counter = 1
        
    def start(self, args):
        global target
        if(target=="minizinc"):
            self.process_rules()
        return self
    
    def extract_scc(self):
        global g
        disc = [-1] * g.V
        low = [-1] * g.V
        stack_member = [False] * g.V
        st = []
        
        def extract_scc_util(u):
            disc[u] = g.time_
            low[u] = g.time_
            g.time_ += 1
            stack_member[u] = True
            st.append(u)
            
            for v in g.graph[u]:
                if disc[v] == -1:
                    extract_scc_util(v)
                    low[u] = min(low[u], low[v])
                elif stack_member[v]:
                    low[u] = min(low[u], disc[v])
                    
            w = -1
            length = 0
            cycle_nodes = []
            if low[u] == disc[u]:
                while w != u:
                    length += 1
                    w = st.pop()
                    cycle_nodes.append(w)
                    stack_member[w] = False
            
            
            if length > 0 and (length > 1 or u in g.graph[u]):
                for node_idx in cycle_nodes:
                    record_name = next((k for k, v in num_pred.items() if v == node_idx), None)
                    if record_name:
                        self.recursive_records.add(record_name)

        for i in range(g.V):
            if disc[i] == -1:
                extract_scc_util(i)

    def get_base_domain_columns(self, record_n):
        cols = []
        for attr in self.records.get(record_n, []):
            a_type = attr['type']
            actual_type = next((k for k in self.records.keys() if k.lower() == a_type.lower()), None)
            if actual_type:
                if self.is_base_domain(actual_type) and len(self.records[actual_type]) == 1:
                    cols.append(actual_type)
                else:
                    cols.extend(self.get_base_domain_columns(actual_type))
            else:
                cols.append(None)
        return cols
    
    def _process_static_facts(self):
        for rule in self.raw_rules:
            if not rule.get('is_define') or rule.get('from_records'):
                continue
            conditions = rule.get('conditions', [])
            target_alias = rule.get('targets')
            if isinstance(target_alias, list): target_alias = target_alias[0]
            
            self.current_alias_map = rule['alias_map_snapshot'].copy()
            target_record = self.current_alias_map.get(target_alias, target_alias)

            fact_attrs = {}
            range_attrs = {}
            for left, op, right in conditions:
                if op == "==" and "." in left:
                    parts = left.split(".")
                    alias = parts[0]
                    attr = "_".join(parts[1:]) 
                    
                    if alias == target_alias:
                        str_right = str(right)
                        
                        if ".." in str_right:
                            bounds = str_right.split("..")
                            range_attrs[attr] = (int(bounds[0]), int(bounds[1]))
                        else:
                            if str_right.startswith(('"', "'")):
                                val = self.get_string_id(str_right)
                            else:
                                try:
                                    val = int(eval(str_right))
                                except Exception:
                                    val = str_right 
                            fact_attrs[attr] = val
            flattened_attrs = self.get_flattened_attrs(target_record)
            if range_attrs:
                keys = list(range_attrs.keys())
                ranges = [range(range_attrs[k][0], range_attrs[k][1] + 1) for k in keys]
                for combo in itertools.product(*ranges):
                    temp_attrs = fact_attrs.copy()
                    for i, key in enumerate(keys):
                        temp_attrs[key] = combo[i]
                    ordered_tuple = []
                    for attr_dict in flattened_attrs:
                        ordered_tuple.append(temp_attrs.get(attr_dict["name"]))
                    self.facts[target_record].append(tuple(ordered_tuple))
            else:
                ordered_tuple = []
                for attr_dict in flattened_attrs:
                    ordered_tuple.append(fact_attrs.get(attr_dict["name"]))
                self.facts[target_record].append(tuple(ordered_tuple))
            fact_attrs = {}
            range_attr = None
        for rec_name, fact_list in list(self.facts.items()):
            flat_attrs = self.get_flattened_attrs(rec_name)
            is_idb_record = False
            for rule in self.raw_rules:
                t_alias = rule.get('targets')
                if isinstance(t_alias, list) and len(t_alias) > 0: 
                    t_alias = t_alias[0]
                t_rec = rule.get('alias_map_snapshot', {}).get(t_alias, t_alias)
                if t_rec == rec_name and (rule.get('aggregates') or rule.get('from_records') or rule.get('is_guess')):
                    is_idb_record = True
                    break
            for tup in fact_list:
                if None in tup:
                    if is_idb_record:
                        continue 
                    missing_indices = [i for i, val in enumerate(tup) if val is None]
                    missing_attrs = [flat_attrs[i]['name'].replace('_', '.') for i in missing_indices]
                    raise ValueError(f"Incomplete definition for static record '{rec_name}'. Missing: {', '.join(missing_attrs)}")
        for r_name in list(self.facts.keys()):
            fact_list = self.facts[r_name]
            bd_cols = self.get_base_domain_columns(r_name)
            for i, bd_type in enumerate(bd_cols):
                if bd_type:
                    unique_vals = set(tup[i] for tup in fact_list)
                    for val in unique_vals:
                        if (val,) not in self.facts[bd_type]:
                            self.facts[bd_type].append((val,))

    def _clean_rule_aliases(self, rule):
        
        if 'from_records' in rule:
            cleaned_from = []
            for r_n, r_a in rule['from_records']:
                c_n = r_n[4:] if r_n.startswith("not ") else r_n
                c_a = r_a[4:] if r_a.startswith("not ") else r_a
                cleaned_from.append((c_n, c_a))
            rule['from_records'] = cleaned_from
            
        clean_snap = {}
        for k, v in rule.get('alias_map_snapshot', {}).items():
            ck = k[4:] if k.startswith("not ") else k
            cv = v[4:] if v.startswith("not ") else v
            clean_snap[ck] = cv
        rule['alias_map_snapshot'] = clean_snap
        self.current_alias_map = clean_snap.copy()
    
    def resolve_math_expr(self, expr_str, local_iter_map, rule):
        expr_str = str(expr_str)
        
        if expr_str.isdigit() or (expr_str.startswith('-') and expr_str[1:].isdigit()):
            return expr_str
        if expr_str.startswith(('"', "'")):
            return str(self.get_string_id(expr_str))
            
        pattern = re.compile(r'\b[a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z0-9_]+)*\b')
        
        def replacer(match):
            token = match.group(0)
            if token in ["div", "mod", "sum", "max", "min", "count"]: 
                return token
            
            parts = token.split(".")
            alias = parts[0]
            if alias in local_iter_map:
                res = self.resolve_op(alias, parts, local_iter_map)
                if res: 
                    return res
                iter_name = local_iter_map[alias].get('BASE')
                if iter_name:
                    rec_name = self.current_alias_map.get(alias) or rule.get('alias_map_snapshot', {}).get(alias)
                    if not rec_name and alias in [rule.get('target_alias'), rule.get('target_record')]:
                        rec_name = rule.get('target_record')
                    if rec_name:
                        if len(parts) >= 2:
                            current_rec = rec_name
                            current_iter = iter_name
                            is_edb = self.is_base_domain(current_rec) or len(self.facts.get(current_rec, [])) > 0
                            if not is_edb and len(parts) > 2:
                                rel_attr = parts[1]
                                attr_type = next((ad['type'] for ad in self.records.get(current_rec, []) if ad['name'] == rel_attr), None)
                                if attr_type and attr_type not in ['int', 'str', 'any']:
                                    current_iter = local_iter_map[alias].get(rel_attr) or current_iter
                                    current_rec = attr_type
                                    parts_to_process = parts[2:]
                                else:
                                    parts_to_process = parts[1:]
                            else:
                                parts_to_process = parts[1:]
                            for i in range(len(parts_to_process) - 1):
                                attr = parts_to_process[i]
                                attr_type = next((ad['type'] for ad in self.records.get(current_rec, []) if ad['name'] == attr), None)
                                if attr_type and attr_type not in ['int', 'str', 'any']:
                                    current_iter = f"{current_rec.lower()}_{attr}[{current_iter}]"
                                    current_rec = attr_type
                            last_attr = parts_to_process[-1]
                            return f"{current_rec.lower()}_{last_attr}[{current_iter}]"
            return token 
        return pattern.sub(replacer, expr_str)

    def resolve_op(self, alias, parts, local_iter_map):
        attr = parts[1] if len(parts) > 1 else 'BASE'
        rec_n = self.current_alias_map.get(alias)
        if not rec_n:
            rec_n = next((v for k, v in self.current_alias_map.items() if k.lower() == alias.lower()), None)
            if not rec_n: return None
        actual_alias = next((k for k in local_iter_map.keys() if k.lower() == alias.lower()), alias)
        is_guess = rec_n in getattr(self, 'guess_domains', {})
        if is_guess:
            g_dom = self.guess_domains[rec_n]
            if g_dom.get('fallback_bool', False):
                pass 
            else:
                to_rec = g_dom.get('to_recs', [None])[0]
                from_recs_g = [r.lower() for r in g_dom.get('from', [])]
                if to_rec and to_rec != rec_n and attr != 'BASE':
                    flat_attrs_to = self.get_flattened_attrs(to_rec)
                    exists_in_to = any(ad['name'] == attr or ad['name'].startswith(attr + "_") for ad in flat_attrs_to)
                    is_domain_attr = False
                    dom_key = attr.lower()
                    if attr.lower() in from_recs_g:
                        is_domain_attr = True
                    elif not exists_in_to:
                        actual_rec_n = next((k for k in self.records.keys() if k.lower() == rec_n.lower()), rec_n)
                        attr_def = next((ad for ad in self.records.get(actual_rec_n, []) if ad['name'].lower() == attr.lower()), None)
                        if attr_def and attr_def['type'].lower() in from_recs_g:
                            is_domain_attr = True
                            dom_key = attr_def['type'].lower()
                    if is_domain_attr:
                        val = local_iter_map.get(actual_alias, {}).get(dom_key)
                        if not val and len(from_recs_g) == 1:
                            val = local_iter_map.get(actual_alias, {}).get('BASE')
                        if len(parts) > 2:
                            sub_attr = "_".join(parts[2:])
                            actual_dom_rec = next((k for k in self.records.keys() if k.lower() == dom_key.lower()), dom_key)
                            flat_t = self.get_flattened_attrs(actual_dom_rec)
                            target_name = next((ad['name'] for ad in flat_t if ad['name'] == sub_attr or ad['name'].startswith(sub_attr + "_")), sub_attr)
                            return f"{actual_dom_rec.lower()}_{target_name}[{val}]"
                        return val
                    indices = []
                    for r in g_dom.get('from', []):
                        val = local_iter_map.get(actual_alias, {}).get(r.lower())
                        if not val and len(from_recs_g) == 1:
                            val = local_iter_map.get(actual_alias, {}).get('BASE')
                        indices.append(val)
                    if all(indices):
                        arr_access = f"{rec_n.lower()}[{', '.join(indices)}]" if indices else rec_n.lower()
                        actual_rec_n = next((k for k in self.records.keys() if k.lower() == rec_n.lower()), rec_n)
                        attr_def = next((ad for ad in self.records.get(actual_rec_n, []) if ad['name'].lower() == attr.lower()), None)
                        is_to_attr = (attr.lower() == to_rec.lower()) or (attr_def and attr_def['type'].lower() == to_rec.lower())
                        if len(parts) == 2 and is_to_attr:
                            return arr_access
                        target_name = "_".join(parts[2:]) if len(parts) > 2 else attr
                        if len(parts) == 2:
                            target_name = next((ad['name'] for ad in flat_attrs_to if ad['name'] == attr or ad['name'].startswith(attr + "_")), attr)
                        return f"{to_rec.lower()}_{target_name}[{arr_access}]"
        it = local_iter_map.get(actual_alias, {}).get(attr)
        if it:
            if len(parts) > 2: 
                actual_rec_n = next((k for k in self.records.keys() if k.lower() == rec_n.lower()), rec_n)
                current_type = next((ad['type'] for ad in self.records.get(actual_rec_n, []) if ad['name'] == attr), None)
                if current_type:
                    sub_attrs = "_".join(parts[2:])
                    flat_t = self.get_flattened_attrs(current_type)
                    target_name = next((ad['name'] for ad in flat_t if ad['name'] == sub_attrs or ad['name'].startswith(sub_attrs + "_")), sub_attrs)
                    return f"{current_type.lower()}_{target_name}[{it}]"
            else:
                actual_rec_n = next((k for k in self.records.keys() if k.lower() == rec_n.lower()), rec_n)
                current_type = next((ad['type'] for ad in self.records.get(actual_rec_n, []) if ad['name'] == attr), None)
                if current_type in ['int', 'str', 'any']:
                    pseudo_rec = f"{actual_rec_n}_{attr}"
                    if pseudo_rec in self.records:
                        return f"{pseudo_rec.lower()}_value[{it}]"
            return it
        base_it = local_iter_map.get(actual_alias, {}).get('BASE')
        if base_it:
            flat_attrs = self.get_flattened_attrs(rec_n)
            target_name = "_".join(parts[1:])
            target_name = next((ad['name'] for ad in flat_attrs if ad['name'] == target_name or ad['name'].startswith(target_name + "_")), target_name)
            return f"{rec_n.lower()}_{target_name}[{base_it}]"
        return None

    def is_base_domain(self, r_name):
            return all(ad['type'] in ['int', 'str', 'any'] for ad in self.records[r_name])
    
    def _build_negated_blocks(self, mzn_conditions, from_iters_defs, fused_iters, negated_aliases):
        main_iters_names = []
        negated_iters_by_alias = {na: [] for na in negated_aliases}
        for i_name in from_iters_defs:
            if i_name not in fused_iters:
                alias = i_name.split('_')[0]
                if alias in negated_aliases:
                    negated_iters_by_alias[alias].append(i_name)
                else:
                    main_iters_names.append(i_name)
        main_conds = []
        negated_conds_by_alias = {na: [] for na in negated_aliases}
        for cond in mzn_conditions:
            assigned = False
            for na in negated_aliases:
                has_iter = any(re.search(rf"\b{n_iter}\b", cond) for n_iter in negated_iters_by_alias[na])
                is_presence_flag = False
                if len(negated_iters_by_alias[na]) == 0:
                    arr_prefix = self.current_alias_map.get(na, "").lower() + "["
                    if arr_prefix in cond:
                        is_presence_flag = True
                if has_iter or is_presence_flag:
                    negated_conds_by_alias[na].append(cond)
                    assigned = True
                    break
            if not assigned:
                main_conds.append(cond)
        negated_blocks = []
        for na in negated_aliases:
            n_iters = negated_iters_by_alias[na]
            n_conds = list(dict.fromkeys(negated_conds_by_alias[na])) 
            if n_iters:
                iter_defs = [from_iters_defs[i] for i in n_iters]
                cond_str = " /\\ ".join(n_conds) if n_conds else "true"
                indent = "    " if "    " in cond_str else "        " 
                negated_blocks.append(f"not exists({', '.join(iter_defs)})(\n{indent}{cond_str}\n    )")
            elif n_conds:
                cond_str = " /\\ ".join(n_conds)
                negated_blocks.append(f"not ({cond_str})")

        return main_conds, negated_blocks, main_iters_names

    def _generate_from_iterators(self, from_records, rule, target_indices=None):
        target_indices = target_indices or []
        iterators_map = {}
        from_iters_defs = {}
        mzn_conditions = []
        for r_name, r_alias in from_records:
            self.current_alias_map[r_alias] = r_name
            if r_alias not in iterators_map:
                iterators_map[r_alias] = {}
            actual_guess_key = next((k for k in getattr(self, 'guess_domains', {}).keys() if k.lower() == r_name.lower()), None)
            is_edb = self.is_base_domain(r_name) or len(self.facts.get(r_name, [])) > 0
            if actual_guess_key:
                g_dom = self.guess_domains[actual_guess_key]
                from_recs = g_dom.get('from', [])
                to_recs = g_dom.get('to_recs', [])
                to_rec = to_recs[0] if to_recs else ''
                is_bool = g_dom.get('fallback_bool', False)
                limits = g_dom.get('limits', [])
                is_exactly_1 = len(limits) == 1 and limits[0]['type'] == 'exactly' and str(limits[0]['val']).strip() == "1"
                is_at_most_1 = len(limits) == 1 and limits[0]['type'] == 'at most' and str(limits[0]['val']).strip() == "1"
                is_functional = (is_exactly_1 or is_at_most_1) and not is_bool
                all_dims = from_recs.copy()
                if is_bool:
                    all_dims.extend(to_recs)
                    
                guess_iters = []
                for dim in all_dims:
                    it_name = f"{r_alias}_{dim.lower()}_base"
                    if target_indices and it_name in target_indices: it_name = f"{it_name}_inner"
                    from_iters_defs[it_name] = f"{it_name} in 1..{dim.lower()}_len"
                    guess_iters.append(it_name)
                    iterators_map[r_alias][dim.lower()] = it_name

                arr_name = actual_guess_key.lower()
                if is_bool:
                    iterators_map[r_alias]['BASE'] = "1"
                    arr_access = f"{arr_name}[{', '.join(guess_iters)}]" if guess_iters else arr_name
                    mzn_conditions.append(arr_access)
                else:
                    if not to_rec or to_rec.lower() == actual_guess_key.lower():
                        arr_access = f"{arr_name}[{', '.join(guess_iters)}]" if guess_iters else arr_name
                        iterators_map[r_alias]['BASE'] = arr_access
                        mzn_conditions.append(f"{arr_access} > 0")
                    else:
                        arr_access = f"{arr_name}[{', '.join(guess_iters)}]" if guess_iters else arr_name
                        iterators_map[r_alias]['BASE'] = ", ".join(guess_iters) if guess_iters else "1"
                        iterators_map[r_alias][to_rec.lower()] = arr_access
                        if is_at_most_1:
                            mzn_conditions.append(f"{arr_access} > 0")
                        
                    for attr_dict in self.records.get(actual_guess_key, []):
                        attr_name = attr_dict['name'].lower()
                        from_recs_lower = [fr.lower() for fr in from_recs]
                        if attr_name in from_recs_lower:
                            idx = from_recs_lower.index(attr_name)
                            iterators_map[r_alias][attr_name] = guess_iters[idx]
                        elif is_functional and attr_name == to_rec.lower():
                            arr_access = f"{actual_guess_key.lower()}[{', '.join(guess_iters)}]" if guess_iters else actual_guess_key.lower()
                            iterators_map[r_alias][attr_name] = arr_access
                        else:
                            if not is_functional:
                                if attr_dict['type'] not in ['int', 'str', 'any']:
                                    dim_len = f"{attr_dict['type'].lower()}_len"
                                    iter_name = f"{r_alias}_{attr_name}"
                                    if iter_name in target_indices: iter_name = f"{iter_name}_inner"
                                    if iter_name not in from_iters_defs:
                                        from_iters_defs[iter_name] = f"{iter_name} in 1..{dim_len}"
                                    iterators_map[r_alias][attr_name] = iter_name
                arr_name = actual_guess_key.lower()
                if len(guess_iters) == len(from_recs) and all(guess_iters) or not from_recs:
                    arr_access = f"{arr_name}[{', '.join(guess_iters)}]" if guess_iters else arr_name
                    if not to_rec or to_rec.lower() == actual_guess_key.lower():
                        if is_bool:
                            mzn_conditions.append(arr_access)
                        else:
                            mzn_conditions.append(f"{arr_access} > 0")
                    elif is_bool:
                        pass
                    elif not is_functional:
                        val = iterators_map[r_alias].get(to_rec.lower())
                        if val: mzn_conditions.append(f"{val} in {arr_access}")
                    elif is_at_most_1:
                        mzn_conditions.append(f"{arr_access} > 0")
            elif is_edb:
                iter_name = f"{r_alias}_base"
                if iter_name in target_indices: iter_name = f"{iter_name}_inner"
                dim_len = f"{r_name.lower()}_len"
                from_iters_defs[iter_name] = f"{iter_name} in 1..{dim_len}"
                iterators_map[r_alias]['BASE'] = iter_name
            else:
                actual_r_name = next((k for k in self.records.keys() if k.lower() == r_name.lower()), r_name)
                rec_indices = []
                for attr_dict in self.records.get(actual_r_name, []):
                    attr_type = attr_dict['type']
                    attr_name = attr_dict['name'].lower()
                    if attr_type not in ['int', 'str', 'any']:
                        dim_len = f"{attr_type.lower()}_len"
                        iter_name = f"{r_alias}_{attr_name}"
                        if iter_name in target_indices: iter_name = f"{iter_name}_inner"
                        from_iters_defs[iter_name] = f"{iter_name} in 1..{dim_len}"
                        iterators_map[r_alias][attr_name] = iter_name
                        rec_indices.append(iter_name)
                    else:
                        pseudo_rec = f"{actual_r_name}_{attr_name}"
                        dim_len = f"{pseudo_rec.lower()}_len"
                        iter_name = f"{r_alias}_{attr_name}"
                        if iter_name in target_indices: iter_name = f"{iter_name}_inner"
                        from_iters_defs[iter_name] = f"{iter_name} in 1..{dim_len}"
                        iterators_map[r_alias][attr_name] = iter_name
                        rec_indices.append(iter_name)
                iterators_map[r_alias]['BASE'] = "1"
                if rec_indices:
                    mzn_conditions.append(f"{actual_r_name.lower()}[{', '.join(rec_indices)}]")
                elif not self._is_base_domain(actual_r_name) and len(self.records.get(actual_r_name, [])) == 0:
                    mzn_conditions.append(f"{actual_r_name.lower()}")
        return iterators_map, from_iters_defs, mzn_conditions
    
    def _infer_implicit_domains(self):
        implicit_facts = {}
        for rule in self.raw_rules:
            conditions = rule.get('conditions', [])
            aliases = rule.get('alias_map_snapshot', {})
            for left, op, right in conditions:
                if op == "==" and "." in str(left) and (str(right).isdigit() or str(right).startswith(('"', "'"))):
                    parts = str(left).split(".")
                    alias = parts[0]
                    rec_name = aliases.get(alias)
                    if rec_name:
                        current_rec = rec_name
                        for i in range(1, len(parts) - 1):
                            attr_name = parts[i]
                            next_type = next((ad['type'] for ad in self.records.get(current_rec, []) if ad['name'] == attr_name), None)
                            if next_type and next_type not in ['int', 'str', 'any']:
                                current_rec = next_type
                            else:
                                break
                        
                        if current_rec and current_rec != rec_name:
                            target_attr = parts[-1]
                            if current_rec not in implicit_facts:
                                implicit_facts[current_rec] = {}
                            entity_key = (id(rule), ".".join(parts[:-1]))
                            if entity_key not in implicit_facts[current_rec]:
                                implicit_facts[current_rec][entity_key] = {}
                            val = int(right) if right.isdigit() else self.get_string_id(right)
                            implicit_facts[current_rec][entity_key][target_attr] = val
        
        for rec_name, entities in implicit_facts.items():
            flat_attrs = self.get_flattened_attrs(rec_name)
            if rec_name not in self.facts:
                self.facts[rec_name] = []
            for entity_key, attrs_dict in entities.items():
                ordered_tuple = []
                for ad in flat_attrs:
                    ordered_tuple.append(attrs_dict.get(ad["name"])) 
                tup = tuple(ordered_tuple)
                if tup not in self.facts[rec_name]:
                    self.facts[rec_name].append(tup)

    def _parse_condition(self, left, op, right, iterators_map, rule):
        l_str = str(left).strip()
        r_str = str(right).strip()
        if ".." in r_str:
            res_l = self.resolve_math_expr(l_str, iterators_map, rule)
            bounds = r_str.split("..")
            res_bound_1 = self.resolve_math_expr(bounds[0].strip(), iterators_map, rule)
            res_bound_2 = self.resolve_math_expr(bounds[1].strip(), iterators_map, rule)
            res_r = f"{res_bound_1}..{res_bound_2}"
            mzn_op = "in" if op == "==" else op
            return res_l, mzn_op, res_r
        res_l = self.resolve_math_expr(l_str, iterators_map, rule)
        res_r = self.resolve_math_expr(r_str, iterators_map, rule)
        return res_l, op, res_r
    
    def _process_deny_assert(self, rule):
        self.current_alias_map = {}
        is_assert_rule = rule.get('is_assert', False)
        from_records = rule.get('targets', []) + rule.get('from_records', []) if is_assert_rule else rule.get('from_records', [])
        iterators_map, from_iters_defs, mzn_conditions = self._generate_from_iterators(from_records, rule)
        fused_iters = set()
        deny_conds = sorted(rule.get('conditions', []), key=lambda x: 0 if x[1] == "==" and not str(x[2]).isdigit() and not str(x[2]).startswith(('"', "'")) else 1)
        for left, op, right in deny_conds: 
            res_l, parsed_op, res_r = self._parse_condition(left, op, right, iterators_map, rule)
            
            if ".." in str(res_r):
                mzn_conditions.append(f"{res_l} {parsed_op} {res_r}")
                continue
           
            if res_l and res_r:
                if parsed_op == "==" and "[" in str(res_l) and "[" in str(res_r):
                    arr_l, idx_l = str(res_l).strip().replace("]", "").split("[", 1)
                    arr_r, idx_r = str(res_r).strip().replace("]", "").split("[", 1)
                    is_guess_array = any(arr_l == g.lower() for g in getattr(self, 'guess_domains', {}))
                    if arr_l == arr_r and not is_guess_array and idx_l in from_iters_defs and idx_r in from_iters_defs:
                        is_primary_key = False
                        for rec_name, attrs in getattr(self, 'records', {}).items():
                            prefix = rec_name.lower() + "_"
                            if arr_l.startswith(prefix):
                                attr_name = arr_l[len(prefix):] 
                                attr_idx = -1
                                for i, a in enumerate(attrs):
                                    if a['name'].lower() == attr_name:
                                        attr_idx = i
                                        break
                                if attr_idx != -1 and rec_name in getattr(self, 'facts', {}):
                                    values = [fact[attr_idx] for fact in self.facts[rec_name]]
                                    if len(values) > 0 and len(values) == len(set(values)):
                                        is_primary_key = True
                                break
                        if is_primary_key:
                            res_l = idx_l
                            res_r = idx_r
                            
                if parsed_op == "==" and res_l in from_iters_defs and res_r in from_iters_defs:
                    negated_al = rule.get('negated_atoms', [])
                    self._merge_mapped_iterators(res_l, res_r, iterators_map, mzn_conditions, negated_al, fused_iters)
                    continue
                if parsed_op == "==" and str(res_l).strip() == str(res_r).strip():
                    continue 
                mzn_conditions.append(f"{res_l} {parsed_op} {res_r}")
        for r_name, r_alias in from_records:
            actual_guess_key = next((k for k in getattr(self, 'guess_domains', {}).keys() if k.lower() == r_name.lower()), None)
            is_guess = actual_guess_key is not None
            if is_guess:
                g_dom = self.guess_domains[actual_guess_key]
                from_recs = g_dom.get('from', [])
                to_recs = g_dom.get('to_recs', [])
                to_rec = to_recs[0] if to_recs else ''
                is_bool = g_dom.get('fallback_bool', False)
                limits = g_dom.get('limits', [])
                is_functional = (len(limits) == 1 and limits[0]['type'] in ['exactly', 'at most'] and str(limits[0]['val']).strip() == "1") and not is_bool
                
                if is_bool:
                    pass 
                else:
                    arr_name = actual_guess_key.lower()
                    keys = [iterators_map[r_alias].get(f.lower()) for f in from_recs]
                    if len(keys) == len(from_recs) and (all(keys) or not from_recs):
                        arr_access = f"{arr_name}[{', '.join(keys)}]" if keys else arr_name
                        if not to_rec or to_rec.lower() == actual_guess_key.lower():
                            if is_bool:
                                mzn_conditions.append(arr_access)
                            else:
                                mzn_conditions.append(f"{arr_access} > 0")
                        elif is_functional:
                            if len(limits) == 1 and limits[0]['type'] == 'at most':
                                mzn_conditions.append(f"{arr_access} > 0")
                        else:
                            val = iterators_map[r_alias].get(to_rec.lower())
                            if val:
                                mzn_conditions.append(f"{val} in {arr_access}")
        functional_groups = {} 
        for rec_name, rec_alias in from_records:
            if not self.is_base_domain(rec_name) and len(self.facts.get(rec_name, [])) == 0:
                actual_guess_key = next((k for k in getattr(self, 'guess_domains', {}).keys() if k.lower() == rec_name.lower()), None)
                if actual_guess_key:
                    g_dom = self.guess_domains[actual_guess_key]
                    
                    def get_iter_for_type(t_name):
                        attr = next((ad['name'] for ad in self.records.get(actual_guess_key, []) if str(ad['type']).lower() == str(t_name).lower()), None)
                        if not attr: 
                            attr = next((ad['name'] for ad in self.records.get(actual_guess_key, []) if str(ad['name']).lower() == str(t_name).lower()), None)
                        it_v = iterators_map.get(rec_alias, {}).get(attr)
                        if not it_v:
                            for c_alias, c_rec in self.current_alias_map.items():
                                if str(c_rec).lower() == str(t_name).lower():
                                    it_v = iterators_map.get(c_alias, {}).get('BASE')
                                    if it_v: break
                        return it_v or iterators_map.get(rec_alias, {}).get('BASE') or "1"

                    to_recs = g_dom.get('to_recs', [])
                    to_rec = to_recs[0] if to_recs else ''

                    if not g_dom.get('fallback_bool'):
                        indices = [get_iter_for_type(r_type) for r_type in g_dom['from']]
                        iter_to = get_iter_for_type(to_rec)
                        limits = g_dom.get('limits', [])
                        preconds = self.rule_headers.get(actual_guess_key, {}).get('preconds', [])
                        is_exactly_1 = len(limits) == 1 and limits[0]['type'] == 'exactly' and str(limits[0]['val']).strip() == "1"
                        is_at_most_1 = len(limits) == 1 and limits[0]['type'] == 'at most' and str(limits[0]['val']).strip() == "1"
                        is_functional = (is_exactly_1 or is_at_most_1) and not preconds
                        if is_functional:
                            lhs = f"{actual_guess_key.lower()}[{', '.join(indices)}]" if indices else actual_guess_key.lower()
                            if iter_to not in functional_groups:
                                functional_groups[iter_to] = []
                            functional_groups[iter_to].append(lhs)
                        else:
                            arr_access = f"{actual_guess_key.lower()}[{', '.join(indices)}]" if indices else actual_guess_key.lower()
                            if to_rec.lower() == actual_guess_key.lower():
                                if f"{arr_access} > 0" not in mzn_conditions:
                                    mzn_conditions.append(f"{arr_access} > 0")
                            else:
                                mzn_conditions.append(f"{iter_to} in {arr_access}")
                    else:
                        all_dims = g_dom['from'] + to_recs
                        indices = [get_iter_for_type(d_type) for d_type in all_dims]
                        arr_access = f"{actual_guess_key.lower()}[{', '.join(indices)}]" if indices else actual_guess_key.lower()
                        if arr_access not in mzn_conditions:
                            mzn_conditions.append(arr_access)
                else:
                    rec_indices = [iterators_map[rec_alias].get(ad['name'].lower(), "1") for ad in self.records.get(rec_name, [])]
                    mzn_conditions.append(f"{rec_name.lower()}[{', '.join(rec_indices)}]")
        for target_val, lhs_list in functional_groups.items():
            if len(lhs_list) > 1:
                for i in range(len(lhs_list) - 1):
                    mzn_conditions.append(f"{lhs_list[i]} == {lhs_list[i+1]}")
                is_used_elsewhere = any(target_val in cond for cond in mzn_conditions if cond not in [f"{lhs_list[i]} == {lhs_list[i+1]}" for i in range(len(lhs_list)-1)])
                if not is_used_elsewhere:
                    fused_iters.add(target_val) 
                else:
                    mzn_conditions.append(f"{lhs_list[0]} == {target_val}")
            elif len(lhs_list) == 1:
                mzn_conditions.append(f"{lhs_list[0]} == {target_val}")
        mzn_aggregates = self._translate_aggregates(rule.get('aggregates', []), iterators_map, rule)
        if mzn_aggregates:
            mzn_conditions.extend(mzn_aggregates)
        forall_guards = []
        negated_aliases = rule.get('negated_atoms', []).copy()
        mzn_conditions, from_iters_defs, _ = self._fuse_equivalent_iterators(
            conditions=mzn_conditions, 
            iter_defs=from_iters_defs
        )
        clean_conditions = []
        for cond in mzn_conditions:
            normalized_cond = re.sub(r'\s+', ' ', cond).strip()
            parts = normalized_cond.split(" == ")
            if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                continue 
            if normalized_cond not in clean_conditions:
                clean_conditions.append(normalized_cond)
        mzn_conditions = clean_conditions
        dynamic_names = [d.lower() for d in getattr(self, 'guess_domains', {})] + \
                        [d.lower() for d in getattr(self, 'rule_bodies', {})]
        negated_iterators = []
        for i_name in from_iters_defs:
            if i_name.split('_')[0] in negated_aliases:
                negated_iterators.append(i_name)

        static_conds = []
        dynamic_conds = []
        for c in mzn_conditions:
            c_lower = c.lower()
            is_dynamic = False
            
            if "exists" in c_lower or "sum(" in c_lower:
                is_dynamic = True
            else:
                for d in dynamic_names:
                    if re.search(rf"\b{d}\b", c_lower):
                        is_dynamic = True
                        break
            if any(re.search(rf"\b{n_iter}\b", c) for n_iter in negated_iterators):
                is_dynamic = True

            if is_dynamic:
                dynamic_conds.append(c)
            else:
                static_conds.append(c)
        forall_guards.extend(static_conds)
        mzn_conditions = dynamic_conds
        main_conds, negated_blocks, main_iters_names = self._build_negated_blocks(mzn_conditions, from_iters_defs, fused_iters, negated_aliases)
        all_final_conds = main_conds + negated_blocks
        body = " /\\ ".join(all_final_conds) if all_final_conds else "true"
        active_from_iters = [from_iters_defs[i] for i in main_iters_names]
        unique_guards = []
        for g in forall_guards:
            if g not in unique_guards: unique_guards.append(g)
        guards_str = (" where " + " /\\ ".join(unique_guards)) if unique_guards else ""
        if rule.get('is_weak'):
            if unique_guards and not active_from_iters:
                body = " /\\ ".join(unique_guards) + " /\\ " + body
            core_expr = f"bool2int(not ({body}))" if is_assert_rule else f"bool2int({body})"
            penalty_data = rule['penalty']
            res_weight = self.resolve_math_expr(str(penalty_data['weight']), iterators_map, rule)
            res_level = self.resolve_math_expr(str(penalty_data['level']), iterators_map, rule)
            try:
                p_level = int(eval(res_level))
            except Exception:
                raise ValueError("Semantic error in weak constraint...")
            if not hasattr(self, 'weak_constraints'): self.weak_constraints = []
            p_name = f"penalty_{len(self.weak_constraints) + 1}"
            if active_from_iters:
                penalty_expr = f"sum({', '.join(active_from_iters)}{guards_str})(\n    {core_expr} * ({res_weight})\n)"
                max_cost_expr = f"sum({', '.join(active_from_iters)}{guards_str})(1 * ({res_weight}))"
            else:
                penalty_expr = f"{core_expr} * ({res_weight})"
                max_cost_expr = f"{res_weight}"
            self.weak_constraints.append({
                'name': p_name, 
                'expr': penalty_expr, 
                'max_cost_expr': max_cost_expr, 
                'level': p_level
            })
        else:
            if not active_from_iters and unique_guards:
                body = " /\\ ".join(unique_guards) + " /\\ " + body
            if is_assert_rule:
                if active_from_iters:
                    deny_str = f"constraint forall({', '.join(active_from_iters)}{guards_str})(\n    {body}\n);"
                else:
                    deny_str = f"constraint ({body});"
            else:
                if active_from_iters:
                    deny_str = f"constraint forall({', '.join(active_from_iters)}{guards_str})(\n    not ({body})\n);"
                else:
                    deny_str = f"constraint not ({body});"
            self.deny_constraints.append(deny_str)
        return
    
    def _check_negation_safety(self, rule, rule_type, target_name, target_alias):
        conditions = rule.get('conditions', [])
        if not conditions:
            return
        negative_aliases = set(rule.get('negated_atoms', []))
        positive_aliases = set()
        for alias, rec_name in rule.get('alias_map_snapshot', {}).items():
            if alias not in negative_aliases:
                positive_aliases.add(alias)
        for r_name, r_alias in rule.get('from_records', []):
            if r_alias not in negative_aliases:
                positive_aliases.add(r_alias)
        for r_name in rule.get('from_recs', []):
            if r_name not in negative_aliases:
                positive_aliases.add(r_name)
        target_identifiers = {target_name, target_alias}
        parent = {}
        
        def find(i):
            if parent[i] == i: return i
            parent[i] = find(parent[i])
            return parent[i]
        
        def union(i, j):
            root_i = find(i)
            root_j = find(j)
            if root_i != root_j:
                parent[root_i] = root_j

        terms = set()
        for left, op, right in conditions:
            if op == "==":
                terms.add(str(left).strip())
                terms.add(str(right).strip())
                
        for t in terms:
            parent[t] = t
            
        for left, op, right in conditions:
            if op == "==":
                union(str(left).strip(), str(right).strip())
        components = {}
        for t in terms:
            root = find(t)
            if root not in components:
                components[root] = []
            components[root].append(t)
        for root, group in components.items():
            has_target = False
            has_negative = False
            has_positive_or_constant = False
            for item in group:
                if item.isdigit() or item.startswith(('"', "'")) or '..' in item or (item.startswith('-') and item[1:].isdigit()):
                    has_positive_or_constant = True
                    continue
                base = item.split(".")[0]
                if base in target_identifiers:
                    has_target = True
                elif base in positive_aliases:
                    has_positive_or_constant = True
                elif base in negative_aliases:
                    has_negative = True
                    
            if has_target and has_negative and not has_positive_or_constant:
                t_attrs = [x for x in group if x.split(".")[0] in target_identifiers]
                n_attrs = [x for x in group if x.split(".")[0] in negative_aliases]
                raise ValueError(
                    f"\nSemantic Error in {rule_type} '{target_name}':\n"
                    f"Target attribute '{t_attrs[0]}' is logically bound to '{n_attrs[0]}' "
                    f"(from a negative relation), but it is NEVER anchored to a positive domain or a constant.\n"
                    f"This violates Datalog Safety Rules."
                )

    def _check_rule_safety(self, rule, target_alias, target_record, flat_t, is_guess=False):
        mapped_attrs = []
        aliases_to_check = {str(target_alias).lower(), str(target_record).lower()}
        for left, op, right in rule.get('conditions', []):
            if op == "==":
                for side in (left, right):
                    parts = str(side).strip().split('.')
                    if parts[0].lower() in aliases_to_check:
                        if len(parts) > 1:
                            mapped_attrs.append("_".join(parts[1:]).lower())
                        else:
                            
                            for ad in flat_t: mapped_attrs.append(ad['name'].lower())
        implicit_attrs = []
        if is_guess:
            g_dom = getattr(self, 'guess_domains', {}).get(target_record, {})
            implicit_attrs = [f.lower() for f in g_dom.get('from', [])]
            for tr in g_dom.get('to_recs', []):
                implicit_attrs.append(tr.lower())
        for ad in flat_t:
            t_attr = ad['name'].lower()
            is_mapped = t_attr in mapped_attrs or any(t_attr.startswith(m + "_") for m in mapped_attrs)
            is_implicit = t_attr in implicit_attrs or any(t_attr.startswith(i + "_") for i in implicit_attrs)
            if not is_mapped and not is_implicit:
                clean_attr = ad['name'].replace('_', '.')
                rule_type = "guess" if is_guess else "rule"
                msg_suffix = ", or it must be part of the guess domain" if is_guess else ""
                raise ValueError(f"Unsafe {rule_type} definition for '{target_record}'. The attribute '{clean_attr}' is unbound. You must specify how to derive it in the where clause{msg_suffix}!")
    
    def _merge_mapped_iterators(self, iter_l, iter_r, iterators_map, mzn_conditions, negated_aliases, fused_iters, target_indices=None):
        target_indices = target_indices or []
        alias_l_prefix = str(iter_l).split('_')[0]
        alias_r_prefix = str(iter_r).split('_')[0]
        if iter_l in target_indices and iter_r not in target_indices:
            pass
        elif iter_r in target_indices and iter_l not in target_indices:
            iter_l, iter_r = iter_r, iter_l
        elif alias_r_prefix in negated_aliases and alias_l_prefix not in negated_aliases:
            pass
        elif alias_l_prefix in negated_aliases and alias_r_prefix not in negated_aliases:
            iter_l, iter_r = iter_r, iter_l
        elif "_base" in iter_r and "_base" not in iter_l:
            iter_l, iter_r = iter_r, iter_l
        elif str(iter_r) < str(iter_l) and not ("_base" in iter_l and "_base" not in iter_r):
            iter_l, iter_r = iter_r, iter_l
        if iter_l != iter_r:
            fused_iters.add(iter_r)
            for a in iterators_map:
                for k, v in iterators_map[a].items():
                    if v == iter_r:
                        iterators_map[a][k] = iter_l
                    elif isinstance(v, str) and iter_r in v:
                        iterators_map[a][k] = v.replace(iter_r, iter_l)
            for i in range(len(mzn_conditions)):
                mzn_conditions[i] = re.sub(rf"\b{iter_r}\b", iter_l, mzn_conditions[i])
        return iter_l, iter_r
    
    def _translate_aggregates(self, aggregates, iterators_map, rule):
        mzn_aggregates = []
        for aggr in aggregates:
            aggr_type = aggr['aggr_type'] 
            aggr_op = aggr['operator']
            aggr_val = aggr['target_value']
            res_val = self.resolve_math_expr(aggr_val, iterators_map, rule)
            if res_val: aggr_val = res_val
            mzn_aggr_parts = []
            exists_parts = []
            for body in aggr['bodies']:
                local_iter_map = {k: v.copy() for k, v in iterators_map.items() if isinstance(v, dict)}
                local_iters_defs = []
                local_conds = []
                snapshot_alias = self.current_alias_map.copy()
                for r_name, r_alias in body['from']:
                    self.current_alias_map[r_alias] = r_name 
                    local_iter_map[r_alias] = {}
                    if self.is_base_domain(r_name) or len(self.facts.get(r_name, [])) > 0:
                        iter_name = f"{r_alias}_aggr"
                        dim_len = f"{r_name.lower()}_len"
                        local_iters_defs.append(f"{iter_name} in 1..{dim_len}")
                        local_iter_map[r_alias]['BASE'] = iter_name
                for r_name, r_alias in body['from']:
                    if self.is_base_domain(r_name) or len(self.facts.get(r_name, [])) > 0:
                        continue 
                    is_guess = r_name in getattr(self, 'guess_domains', {})
                    if is_guess:
                        g_dom = self.guess_domains[r_name]
                        from_recs = g_dom.get('from', [])
                        to_recs = g_dom.get('to_recs', [])
                        to_rec = to_recs[0] if to_recs else ''
                        is_bool = g_dom.get('fallback_bool', False)
                        limits = g_dom.get('limits', [])
                        is_exactly_1 = len(limits) == 1 and limits[0]['type'] == 'exactly' and str(limits[0]['val']).strip() == "1"
                        is_at_most_1 = len(limits) == 1 and limits[0]['type'] == 'at most' and str(limits[0]['val']).strip() == "1"
                        preconds = self.rule_headers.get(r_name, {}).get('preconds', [])
                        is_functional = (is_exactly_1 or is_at_most_1) and not is_bool
                        guess_iters = []
                        for fr in from_recs:
                            it_name = f"{r_alias}_{fr.lower()}_aggr"
                            local_iters_defs.append(f"{it_name} in 1..{fr.lower()}_len")
                            guess_iters.append(it_name)
                        if not to_rec or to_rec.lower() == r_name.lower():
                            local_iter_map[r_alias]['BASE'] = "1"
                        else:
                            local_iter_map[r_alias]['BASE'] = ", ".join(guess_iters) if guess_iters else "1"
                            
                        for attr_dict in self.records.get(r_name, []):
                            attr_name = attr_dict['name'].lower()
                            attr_type = attr_dict['type'].lower()
                            from_recs_lower = [fr.lower() for fr in from_recs]
                            if attr_name in from_recs_lower:
                                idx = from_recs_lower.index(attr_name)
                                local_iter_map[r_alias][attr_name] = guess_iters[idx]
                            elif is_functional and attr_name == to_rec.lower():
                                arr_access = f"{r_name.lower()}[{', '.join(guess_iters)}]" if guess_iters else r_name.lower()
                                local_iter_map[r_alias][attr_name] = arr_access
                            else:
                                if not is_functional:
                                    fixed_val = None
                                    for l_str, op_str, r_str in body.get('where', []):
                                        if op_str == "==":
                                            if l_str == f"{r_alias}.{attr_name}": fixed_val = self.resolve_math_expr(r_str, local_iter_map, rule) 
                                            elif r_str == f"{r_alias}.{attr_name}": fixed_val = self.resolve_math_expr(l_str, local_iter_map, rule)
                                    if isinstance(fixed_val, str) and fixed_val in local_iter_map and 'BASE' in local_iter_map[fixed_val]:
                                        fixed_val = local_iter_map[fixed_val]['BASE']
                                    if fixed_val:
                                        local_iter_map[r_alias][attr_name] = fixed_val
                                    else:
                                        dim_len = f"{attr_dict['type'].lower()}_len"
                                        iter_name = f"{r_alias}_{attr_name}_aggr"
                                        local_iters_defs.append(f"{iter_name} in 1..{dim_len}")
                                        local_iter_map[r_alias][attr_name] = iter_name

                        arr_name = r_name.lower()
                        if len(guess_iters) == len(from_recs) and (all(guess_iters) or not from_recs):
                            arr_access = f"{arr_name}[{', '.join(guess_iters)}]" if guess_iters else arr_name
                            if not to_rec or to_rec.lower() == r_name.lower():
                                if is_bool:
                                    local_conds.append(arr_access)
                                else:
                                    local_conds.append(f"{arr_access} > 0")
                            elif is_functional:
                                local_iter_map[r_alias][to_rec.lower()] = arr_access
                                if is_at_most_1:
                                    local_conds.append(f"{arr_access} > 0")
                            elif is_bool:
                                vals = []
                                for tr in to_recs:
                                    v = local_iter_map[r_alias].get(tr.lower())
                                    if v: vals.append(v)
                                if len(vals) == len(to_recs):
                                    bool_access = f"{arr_name}[{', '.join(guess_iters + vals)}]" if (guess_iters or vals) else arr_name
                                    local_conds.append(bool_access)
                            else:
                                val = local_iter_map[r_alias].get(to_rec.lower())
                                if val: local_conds.append(f"{val} in {arr_access}")
                    else:
                        is_functional = False
                        rec_indices = []
                        for attr_dict in self.records.get(r_name, []):
                            attr_name = attr_dict['name'].lower()
                            attr_type = attr_dict['type']
                            fixed_val = None
                            for l_str, op_str, r_str in body.get('where', []):
                                if op_str == "==":
                                    if l_str == f"{r_alias}.{attr_name}": fixed_val = self.resolve_math_expr(r_str, local_iter_map, rule) 
                                    elif r_str == f"{r_alias}.{attr_name}": fixed_val = self.resolve_math_expr(l_str, local_iter_map, rule)
                            if isinstance(fixed_val, str) and fixed_val in local_iter_map and 'BASE' in local_iter_map[fixed_val]:
                                fixed_val = local_iter_map[fixed_val]['BASE']
                            if fixed_val:
                                local_iter_map[r_alias][attr_name] = fixed_val
                                rec_indices.append(fixed_val)
                            else:
                                if attr_type not in ['int', 'str', 'any']:
                                    dim_len = f"{attr_type.lower()}_len"
                                    iter_name = f"{r_alias}_{attr_name}_aggr"
                                    local_iters_defs.append(f"{iter_name} in 1..{dim_len}")
                                    local_iter_map[r_alias][attr_name] = iter_name
                                    rec_indices.append(iter_name)
                                else:
                                    pseudo_rec = f"{r_name}_{attr_name}"
                                    if pseudo_rec in self.records:
                                        dim_len = f"{pseudo_rec.lower()}_len"
                                    else:
                                        dim_len = f"{r_name.lower()}_len"
                                    iter_name = f"{r_alias}_{attr_name}_aggr"
                                    local_iters_defs.append(f"{iter_name} in 1..{dim_len}")
                                    local_iter_map[r_alias][attr_name] = iter_name
                                    rec_indices.append(iter_name)
                                    
                        arr_acc = f"{r_name.lower()}[{', '.join(rec_indices)}]" if rec_indices else r_name.lower()
                        local_conds.append(arr_acc)
                
                for left, op, right in body.get('where', []):
                    self._append_normalized_condition(left, op, right, local_iter_map, rule, local_conds)
                aggr_target_expr = "1" 
                if body.get('target'):
                    t_str = str(body['target'][0]).rsplit("/", 1)[0] 
                    res_t = self.resolve_math_expr(t_str, local_iter_map, rule)
                    if res_t: aggr_target_expr = str(res_t)
                local_conds, local_iters_defs, updated_extra = self._fuse_equivalent_iterators(
                    conditions=local_conds, 
                    iter_defs=local_iters_defs, 
                    extra_exprs=[aggr_target_expr]
                )
                aggr_target_expr = updated_extra[0]
                where_clause = (" where " + " /\\ ".join(local_conds)) if local_conds else ""
                generators = ", ".join(local_iters_defs)
                exists_body = " /\\ ".join(local_conds) if local_conds else "true"
                exists_expr = f"exists({generators})(\n            {exists_body}\n        )"
                if not generators:
                    cond_str = " /\\ ".join(local_conds) if local_conds else "true"
                    if local_conds:
                        if aggr_type == "count": mzn_aggr_parts.append(f"bool2int({cond_str})")
                        elif aggr_type == "sum": mzn_aggr_parts.append(f"(if {cond_str} then {aggr_target_expr} else 0 endif)")
                        elif aggr_type in ["min", "max"]:
                            mzn_aggr_parts.append(f"({aggr_target_expr})")
                            exists_parts.append(cond_str) 
                    else:
                        mzn_aggr_parts.append("1" if aggr_type == "count" else f"({aggr_target_expr})")
                            
                else:
                    cond_str = " /\\ ".join(local_conds) if local_conds else "true"
                    if aggr_type == "count": mzn_aggr_parts.append(f"sum({generators})(1)" if cond_str == "true" else f"sum({generators})(bool2int({cond_str}))")
                    elif aggr_type == "sum": mzn_aggr_parts.append(f"sum({generators})({aggr_target_expr})" if cond_str == "true" else f"sum({generators})(if {cond_str} then {aggr_target_expr} else 0 endif)")
                    elif aggr_type == "min":
                        mzn_aggr_parts.append(f"min([ {aggr_target_expr} | {generators} {where_clause} ])")
                        exists_parts.append(exists_expr)
                    elif aggr_type == "max":
                        mzn_aggr_parts.append(f"max([ {aggr_target_expr} | {generators} {where_clause} ])")
                        exists_parts.append(exists_expr)
                self.current_alias_map = snapshot_alias
            combined_aggr_expr = " + ".join(mzn_aggr_parts)
            if combined_aggr_expr:
                base_cond = f"({combined_aggr_expr}) {aggr_op} {aggr_val}"
                if exists_parts: mzn_aggregates.append(f"((\n        {' /\\ '.join(exists_parts)}\n    ) /\\ {base_cond})")
                else: mzn_aggregates.append(base_cond)
        return mzn_aggregates
         
    def _process_guess(self, rule):
        self.current_alias_map = {}
        target_alias = rule.get('target_alias') or (rule.get('targets')[0] if rule.get('targets') else None)
        target_record = rule['target_record']
        if target_record and target_record in self.records:
            flat_t = self.get_flattened_attrs(target_record)
            self._check_rule_safety(rule, target_alias, target_record, flat_t, is_guess=True)
        self._check_negation_safety(rule, "Guess", target_record, target_alias)
        target_rec = rule['target_record']
        from_recs = rule['from_recs']
        to_recs = rule.get('to_recs', [])
        if not to_recs:
            if rule.get('to_rec'):
                to_recs = [rule['to_rec']]
            else:
                to_recs = [target_rec]
                rule['to_recs'] = to_recs
        g_conds = rule.get('conditions', [])
        for r in from_recs:
            actual_r = next((k for k in self.records.keys() if k.lower() == r.lower()), r)
            if actual_r == target_rec:
                raise ValueError(f"Domain error: Cyclic guess definition. You cannot use the target '{target_rec}' as a dimension in its own 'from' clause.")
            if len(self.facts.get(actual_r, [])) == 0:
                raise ValueError(f"Domain error: Cannot use '{actual_r}' to define the dimensions of '{target_rec}'. The search space of a decision (guess) must be built on domains with a statically known size, not on decision variables or dynamically inferred records.")
        for to_rec in to_recs:
            if to_rec and to_rec != target_rec:
                actual_to = next((k for k in self.records.keys() if k.lower() == to_rec.lower()), to_rec)
                if len(self.facts.get(actual_to, [])) == 0:
                    raise ValueError(f"Domain error: Cannot use '{actual_to}' as the target domain of '{target_rec}'.")
        target_iters, target_indices = [], []
        temp_iter_map = {}
        for r in from_recs:
            r_low = str(r).lower()
            it_name = f"{target_rec.lower()}_{r_low}"
            target_iters.append(f"{it_name} in 1..{r_low}_len")
            target_indices.append(it_name)
            alias = next((k for k, v in rule['alias_map_snapshot'].items() if v == r), r)
            self.current_alias_map[alias] = r 
            temp_iter_map[alias] = {'BASE': it_name}
        for to_rec in to_recs:
            to_low = str(to_rec).lower()
            if to_rec.lower() != target_rec.lower():
                to_it_name = f"{target_rec.lower()}_{to_low}"
                if to_it_name in target_indices:
                    to_it_name = f"{to_it_name}_to"
                target_iters.append(f"{to_it_name} in 1..{to_low}_len")
                target_indices.append(to_it_name)
                to_alias = next((k for k, v in rule.get('alias_map_snapshot', {}).items() if v == to_rec), to_rec)
                self.current_alias_map[to_alias] = to_rec
                temp_iter_map[to_alias] = {'BASE': to_it_name}
            else:
                to_alias = next((k for k, v in rule.get('alias_map_snapshot', {}).items() if v == to_rec), to_rec)
                self.current_alias_map[to_alias] = to_rec
                if to_alias not in temp_iter_map: temp_iter_map[to_alias] = {}
                if target_rec not in temp_iter_map: temp_iter_map[target_rec] = {}
                array_access = f"{target_rec.lower()}[{', '.join(target_indices)}]" if target_indices else target_rec.lower()
                temp_iter_map[to_alias]['BASE'] = array_access
                temp_iter_map[target_rec]['BASE'] = array_access
        target_alias = rule.get('target_alias') or target_rec
        self.current_alias_map[target_alias] = target_rec
        self.current_alias_map[target_rec] = target_rec
        if target_rec not in temp_iter_map: temp_iter_map[target_rec] = {}
        if target_alias not in temp_iter_map: temp_iter_map[target_alias] = temp_iter_map[target_rec]
        if target_indices:
            temp_iter_map[target_rec]['BASE'] = target_indices[-1]
            temp_iter_map[target_alias]['BASE'] = target_indices[-1]
        for idx, r in enumerate(from_recs):
            temp_iter_map[target_rec][str(r).lower()] = target_indices[idx]
            temp_iter_map[target_alias][str(r).lower()] = target_indices[idx]
            if str(r) not in temp_iter_map: temp_iter_map[str(r)] = {}
            if 'BASE' not in temp_iter_map[str(r)]:
                temp_iter_map[str(r)]['BASE'] = target_indices[idx]
                self.current_alias_map[str(r)] = r
        for to_rec in to_recs:
            temp_iter_map[target_rec][str(to_rec).lower()] = target_indices[-1]
            temp_iter_map[target_alias][str(to_rec).lower()] = target_indices[-1]
            if str(to_rec) not in temp_iter_map: temp_iter_map[str(to_rec)] = {}
            if 'BASE' not in temp_iter_map[str(to_rec)]:
                temp_iter_map[str(to_rec)]['BASE'] = target_indices[-1]
                self.current_alias_map[str(to_rec)] = to_rec
        aux_iters_defs = []
        aux_idb_conds = [] 
        forbidden_aux = set([target_rec.lower(), target_alias.lower()])
        for tr in to_recs: 
            forbidden_aux.add(tr.lower())
        for k, v in rule.get('alias_map_snapshot', {}).items():
            if v in from_recs or v in to_recs or v == target_rec:
                forbidden_aux.add(k.lower())
                forbidden_aux.add(v.lower())
        for r in from_recs: forbidden_aux.add(r.lower())
        for k_alias, v_rec in rule.get('alias_map_snapshot', {}).items():
            if v_rec.lower() not in forbidden_aux and k_alias.lower() not in forbidden_aux:
                self.current_alias_map[k_alias] = v_rec
                if k_alias not in temp_iter_map:
                    temp_iter_map[k_alias] = {}
                is_edb = self.is_base_domain(v_rec) or len(self.facts.get(v_rec, [])) > 0
                if is_edb:
                    it_name = f"{k_alias}_base"
                    aux_iters_defs.append(f"{it_name} in 1..{v_rec.lower()}_len")
                    temp_iter_map[k_alias]['BASE'] = it_name
                else:
                    rec_indices = []
                    for ad in self.records.get(v_rec, []):
                        attr_type = ad['type']
                        attr_name = ad['name'].lower()
                        if attr_type not in ['int', 'str', 'any']:
                            dim_len = f"{attr_type.lower()}_len"
                        else:
                            pseudo_rec = f"{v_rec}_{attr_name}"
                            if pseudo_rec in self.records:
                                dim_len = f"{pseudo_rec.lower()}_len"
                            else:
                                dim_len = f"{v_rec.lower()}_len"
                        it_name = f"{k_alias}_{attr_name}"
                        aux_iters_defs.append(f"{it_name} in 1..{dim_len}")
                        temp_iter_map[k_alias][attr_name] = it_name
                        rec_indices.append(it_name)
                    temp_iter_map[k_alias]['BASE'] = "1"
                    if rec_indices:
                        aux_idb_conds.append(f"{v_rec.lower()}[{', '.join(rec_indices)}]")
        mapped_recs = set()
        is_perfect_functional = True
        structural_failure = False 
        to_rec = to_recs[0] if to_recs else ''
        forbidden_bases = {target_rec, target_alias}
        for tr in to_recs:
            to_alias = next((k for k, v in rule.get('alias_map_snapshot', {}).items() if v == tr), tr)
            forbidden_bases.update([tr, to_alias])
        g_dom = self.guess_domains[target_rec]
        limits = g_dom.get('limits', [])
        if len(limits) != 1 or limits[0]['type'] not in ['exactly', 'at most'] or str(limits[0]['val']).strip() != "1":
            is_perfect_functional = False
        is_inclusion_guess = False
        if to_recs and to_recs[0].lower() == target_rec.lower():
            is_perfect_functional = False
            is_inclusion_guess = True
        elif len(to_recs) > 1:
            is_perfect_functional = False
        for left, op, right in g_conds:
            l_str, r_str = str(left), str(right)
            op_str = str(op).strip()
            l_base = l_str.split(".")[0] if "." in l_str else l_str
            r_base = r_str.split(".")[0] if "." in r_str else r_str
            if l_base not in forbidden_bases and r_base not in forbidden_bases:
                is_perfect_functional = False 
                continue
            if any(c in l_str + r_str for c in ['+', '-', '*', '/', '(', ')']):
                structural_failure = True
                continue  
            if l_base == target_rec or l_base == target_alias or r_base == target_rec or r_base == target_alias:
                if op_str != "==":
                    structural_failure = True
                else:
                    for r in from_recs + [to_rec]:
                        r_alias = next((k for k, v in rule['alias_map_snapshot'].items() if v == r), r)
                        if r == l_base or r == r_base or r_alias == l_base or r_alias == r_base:
                            mapped_recs.add(r)
        if set(from_recs + [to_rec]) - mapped_recs:
            if to_rec.lower() != target_rec.lower():
                structural_failure = True
        g_dom = self.guess_domains[target_rec]
        limits = g_dom.get('limits', [])
        if len(limits) == 1 and limits[0]['type'] in ['exactly', 'at most'] and str(limits[0]['val']).strip() == "1":
            structural_failure = False 
        if structural_failure:
            g_dom['fallback_bool'] = True
            is_perfect_functional = False
        if not is_perfect_functional:
            g_dom['fallback_bool'] = True
        if is_inclusion_guess:
            g_dom['to_recs'] = []
            to_recs = []
            to_rec = ''
        if is_perfect_functional:
            target_iters.pop()   
            target_indices.pop() 
            to_rec = to_recs[0] if to_recs else ''
            array_access = f"{target_rec.lower()}[{', '.join(target_indices)}]" if target_indices else target_rec.lower()
            temp_iter_map[target_rec][str(to_rec).lower()] = array_access
            if target_alias != target_rec:
                temp_iter_map[target_alias][str(to_rec).lower()] = array_access
            if to_alias not in temp_iter_map: temp_iter_map[to_alias] = {}
            temp_iter_map[to_alias]['BASE'] = array_access
            if str(to_rec) not in temp_iter_map: temp_iter_map[str(to_rec)] = {}
            if to_alias == str(to_rec) or str(to_rec) not in from_recs:
                temp_iter_map[str(to_rec)]['BASE'] = array_access
            for k, v in rule['alias_map_snapshot'].items():
                if v == to_rec and k != to_alias and k not in from_recs:
                    if k not in temp_iter_map: temp_iter_map[k] = {}
                    temp_iter_map[k]['BASE'] = array_access
        mzn_preconds = []
        mzn_postconds = []
        mzn_preconds.extend(aux_idb_conds)
        for left, op, right in g_conds:
            l_str, r_str = str(left), str(right)
            l_base = l_str.split(".")[0] if "." in l_str else l_str
            r_base = r_str.split(".")[0] if "." in r_str else r_str
            is_precond = False 
            if not is_precond:
                if op == "==" and not any(c in l_str+r_str for c in ['+', '-', '*', '/']):
                    target_names = [t.lower() for t in [target_rec, target_alias] if t]
                    domain_names = [d.lower() for d in from_recs if d]
                    to_rec_alias = next((k for k, v in rule.get('alias_map_snapshot', {}).items() if v == to_rec), to_rec)
                    if to_rec and to_rec.lower() in domain_names:
                        codomain_names = []
                    else:
                        codomain_names = [t.lower() for t in [to_rec, to_rec_alias] if t]
                    if (l_base.lower() in target_names and (r_base.lower() in codomain_names or r_base.lower() in domain_names)) or \
                       (r_base.lower() in target_names and (l_base.lower() in codomain_names or l_base.lower() in domain_names)):
                        continue
            target_list = mzn_preconds if is_precond else mzn_postconds
            self._append_normalized_condition(left, op, right, temp_iter_map, rule, target_list)
        mzn_aggregates = self._translate_aggregates(rule.get('aggregates', []), temp_iter_map, rule)
        if mzn_aggregates:
            mzn_postconds.extend(mzn_aggregates) 
        if aux_iters_defs:
            active_aux_pre = [aux for aux in aux_iters_defs if any(aux.split(' in ')[0] in p for p in mzn_preconds)]
            if active_aux_pre and mzn_preconds:
                pre_str = " /\\ ".join(mzn_preconds)
                mzn_preconds = [f"exists({', '.join(active_aux_pre)})(\n        {pre_str}\n    )"]
            active_aux_post = [aux for aux in aux_iters_defs if any(aux.split(' in ')[0] in p for p in mzn_postconds)]
            if active_aux_post and mzn_postconds:
                post_str = " /\\ ".join(mzn_postconds)
                mzn_postconds = [f"exists({', '.join(active_aux_post)})(\n        {post_str}\n    )"]
        self.rule_headers[target_rec] = {
            'dims': [f"1..{r.lower()}_len" for r in from_recs] + ([f"1..{to_low}_len"] if not is_perfect_functional and to_rec.lower() != target_rec.lower() else []),
            'iters': target_iters, 
            'indices': target_indices,
            'preconds': mzn_preconds
        }
        if mzn_postconds:
            if target_rec not in self.rule_bodies:
                self.rule_bodies[target_rec] = []
            combined_post = " /\\ ".join(mzn_postconds)
            array_access = f"{target_rec.lower()}[{', '.join(target_indices)}]" if target_indices else target_rec.lower()
            if not is_perfect_functional and to_rec.lower() == target_rec.lower():
                self.rule_bodies[target_rec].append(f"{array_access} -> ({combined_post})")
            else:
                self.rule_bodies[target_rec].append(combined_post)
        return
        
    def _resolve_path_to_iterator(self, path, iterators_map):
        parts = str(path).split('.')
        if not parts:
            return None
        current = iterators_map.get(parts[0])
        if current is None:
            return None
        if len(parts) == 1:
            return current.get('BASE')
        for i in range(1, len(parts)):
            attr = parts[i]
            if isinstance(current, dict) and attr in current:
                current = current[attr]
            else:
                if i == len(parts) - 1 and attr == "id" and isinstance(current, str):
                    return current
                return None
        return current if isinstance(current, str) else None

    def _fuse_equivalent_iterators(self, conditions, iter_defs, extra_exprs=None):
        if extra_exprs is None:
            extra_exprs = []
        is_dict = isinstance(iter_defs, dict)
        working_defs = iter_defs.copy() if is_dict else {d.split(" in ")[0].strip(): d for d in iter_defs}
        working_conds = list(conditions)
        working_extra = list(extra_exprs)
        changed = True
        while changed:
            changed = False
            for cond in list(working_conds):
                parts = cond.split(" == ")
                if len(parts) == 2:
                    left_p, right_p = parts[0].strip(), parts[1].strip()
                    for gen_name in list(working_defs.keys()):
                        if gen_name in left_p and gen_name in right_p:
                            continue
                        replacement = None
                        if left_p == gen_name: 
                            replacement = right_p
                        elif right_p == gen_name: 
                            replacement = left_p
                        if replacement:
                            del working_defs[gen_name]
                            if cond in working_conds:
                                working_conds.remove(cond)
                            working_conds = [re.sub(rf'\b{gen_name}\b', lambda m: replacement, c) for c in working_conds]
                            working_extra = [re.sub(rf'\b{gen_name}\b', lambda m: replacement, e) for e in working_extra]
                            changed = True
                            break
                if changed:
                    break
        clean_conds = []
        for c in working_conds:
            parts = c.split(" == ")
            if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                continue
            clean_conds.append(c)
        final_defs = working_defs if is_dict else list(working_defs.values())
        return clean_conds, final_defs, working_extra
    
    def _append_normalized_condition(self, left, op, right, iterators_map, rule, target_list):
        res_l, parsed_op, res_r = self._parse_condition(left, op, right, iterators_map, rule)
        if ".." in str(res_r):
            target_list.append(f"{res_l} {parsed_op} {res_r}")
            return
        if isinstance(res_l, str) and res_l in iterators_map and 'BASE' in iterators_map[res_l]: 
            res_l = iterators_map[res_l]['BASE']
        if isinstance(res_r, str) and res_r in iterators_map and 'BASE' in iterators_map[res_r]: 
            res_r = iterators_map[res_r]['BASE']
        if res_l and res_r:
            if res_l == res_r and op == "==": 
                return
            target_list.append(f"{res_l} {op} {res_r}")
            
    def _process_define(self, rule):        
        self.current_alias_map = {}
        from_records = rule.get('from_records', []) 
        conditions = rule.get('conditions', [])
        aggregates = rule.get('aggregates', [])
        target_alias = rule.get('targets') or rule.get('target_alias')
        if isinstance(target_alias, list): 
            target_alias = target_alias[0]
        target_record = rule.get('target_record') or rule.get('alias_map_snapshot', {}).get(target_alias) or target_alias
        self.current_alias_map[target_alias] = target_record
        if getattr(self, 'is_recursive_active', False) and target_record in self.recursive_records:
            if aggregates:
                raise ValueError(
                    f"Semantic error: Aggregates within recursive rules (like '{target_record}') "
                    f"are currently unsupported. Cycles involving aggregates break classical bounds propagation."
                )
        self._check_negation_safety(rule, "Rule", target_record, target_alias)
        target_static_facts = {}
        for left, op, right in conditions:
            if op == "==" and "." in left:
                parts = left.split(".")
                if parts[0] == target_alias:
                    attr_key = "_".join(parts[1:]) 
                    if right.isdigit():
                        target_static_facts[attr_key] = int(right)
                    elif right.startswith(('"', "'")):
                        target_static_facts[attr_key] = self.get_string_id(right)
        if not self.is_base_domain(target_record) and target_record in self.records:
            flat_t = self.get_flattened_attrs(target_record)
            self._check_rule_safety(rule, target_alias, target_record, flat_t, is_guess=False)
        for rec_name, rec_alias in from_records:
            self.current_alias_map[rec_alias] = rec_name
        iterators_map = { target_alias: {} }
        target_dims, target_iters, target_indices = [], [], []
        if self.is_base_domain(target_record):
            dim_len = f"{target_record.lower()}_len"
            iter_name = f"{target_record.lower()}_base" 
            target_dims.append(f"1..{dim_len}")
            target_iters.append(f"{iter_name} in 1..{dim_len}")
            target_indices.append(iter_name)
            iterators_map[target_alias]['BASE'] = iter_name
        else:
            for attr_dict in self.records.get(target_record, []):
                attr_type = attr_dict['type']
                attr_name = attr_dict['name'].lower()
                if attr_type not in ['int', 'str', 'any']:
                    dim_len = f"{attr_type.lower()}_len"
                    iter_name = f"{target_record.lower()}_{attr_name}" 
                    target_dims.append(f"1..{dim_len}")
                    target_iters.append(f"{iter_name} in 1..{dim_len}")
                    target_indices.append(iter_name)
                    iterators_map[target_alias][attr_name] = iter_name
                else:
                    val = target_static_facts.get(attr_name)
                    if val is not None:
                        pseudo_rec = f"{target_record}_{attr_name}"
                        if pseudo_rec not in self.records:
                            self.records[pseudo_rec] = [{'name': 'value', 'type': attr_type}]
                            self.facts[pseudo_rec] = []
                        if tuple([val]) not in self.facts[pseudo_rec]:
                            self.facts[pseudo_rec].append(tuple([val]))
                            
                        dim_len = f"{pseudo_rec.lower()}_len"
                        iter_name = f"{target_record.lower()}_{attr_name}"
                        target_dims.append(f"1..{dim_len}")
                        target_iters.append(f"{iter_name} in 1..{dim_len}")
                        target_indices.append(iter_name)
                        iterators_map[target_alias][attr_name] = iter_name
                    else:
                        is_calculated = any(aggr['target_value'] == f"{target_alias}.{attr_name}" for aggr in aggregates)
                        if is_calculated:
                            target_static_facts[attr_name] = None
                            pseudo_rec = f"{target_record}_{attr_name}"
                            if pseudo_rec not in self.records:
                                self.records[pseudo_rec] = [{'name': 'value', 'type': attr_type}]
                                self.facts[pseudo_rec] = []
                            self.facts[pseudo_rec].append(tuple([None]))
                            dim_len = f"{pseudo_rec.lower()}_len"
                            iter_name = f"{target_record.lower()}_{attr_name}"
                            target_dims.append(f"1..{dim_len}")
                            target_iters.append(f"{iter_name} in 1..{dim_len}")
                            target_indices.append(iter_name)
                            iterators_map[target_alias][attr_name] = iter_name
                        else:
                            raise ValueError(f"Inference error: Primitive attribute '{attr_name}'...")
        new_iters_map, from_iters_defs, mzn_conditions = self._generate_from_iterators(from_records, rule, target_indices)
        iterators_map.update(new_iters_map)
        fused_iters = set() 
        negated_aliases = rule.get('negated_atoms', [])
        all_valid_iters = list(from_iters_defs.keys()) + target_indices
        conditions = sorted(conditions, key=lambda x: 0 if x[1] == "==" and not str(x[2]).isdigit() and not str(x[2]).startswith(('"', "'")) else 1)
        for left, op, right in conditions:
            l_str, r_str = str(left), str(right)
            res_l, parsed_op, res_r = self._parse_condition(left, op, right, iterators_map, rule)
            if ".." in str(res_r):
                mzn_conditions.append(f"{res_l} {parsed_op} {res_r}")
                continue
            has_math = any(c in l_str + r_str for c in ['+', '-', '*', '/', '(', ')'])
            if parsed_op == "==" and not r_str.isdigit() and not r_str.startswith(('"', "'")) and not has_math:
                parts_l = left.split(".") if "." in left else [left]
                parts_right = right.split(".") if "." in right else [right]
                alias_l, alias_r = parts_l[0], parts_right[0]
                if alias_l in iterators_map and alias_r in iterators_map:
                    attr_l = parts_l[1] if len(parts_l) > 1 else 'BASE'
                    attr_r = parts_right[1] if len(parts_right) > 1 else 'BASE'
                    if (alias_l == target_alias or alias_r == target_alias) and self.is_base_domain(target_record):
                        t_alias, t_parts = (alias_l, parts_l) if alias_l == target_alias else (alias_r, parts_right)
                        f_alias, f_parts = (alias_r, parts_right) if alias_l == target_alias else (alias_l, parts_l)
                        source_rec_name = self.current_alias_map.get(f_alias)
                        iter_f = None
                        is_edb = self.is_base_domain(source_rec_name) or len(self.facts.get(source_rec_name, [])) > 0
                        if len(f_parts) == 3: 
                            rel_attr, sub_attr = f_parts[1], f_parts[2]
                            if is_edb:
                                source_attr = f"{rel_attr}_{sub_attr}"
                                iter_f = iterators_map[f_alias].get('BASE')
                            else:
                                source_attr = sub_attr
                                for ad in self.records.get(source_rec_name, []):
                                    if ad['name'] == rel_attr and ad['type'] not in ['int', 'str', 'any']:
                                        source_rec_name = ad['type'] 
                                        break
                                iter_f = iterators_map[f_alias].get(rel_attr) 
                        elif len(f_parts) == 2: 
                            source_attr = f_parts[1]
                            iter_f = iterators_map[f_alias].get('BASE') or iterators_map[f_alias].get(f_parts[1])
                        else:
                            source_attr = self.records[source_rec_name][0]['name']
                            iter_f = iterators_map[f_alias].get('BASE')
                            
                        if len(t_parts) == 1:
                            t_attr = self.records[target_record][0]['name']
                        else:
                            t_attr = "_".join(t_parts[1:])
                            
                        flat_f = self.get_flattened_attrs(source_rec_name)
                        col_idx_f = next((i for i, ad in enumerate(flat_f) if ad['name'] == source_attr or ad['name'].startswith(source_attr + "_")), -1)
                        
                        flat_t = self.get_flattened_attrs(target_record)
                        col_idx_t = next((i for i, ad in enumerate(flat_t) if ad['name'] == t_attr or ad['name'].startswith(t_attr + "_")), -1)
                        
                        if col_idx_f != -1 and col_idx_t != -1:
                            dict_f = f"{source_rec_name.lower()}_{flat_f[col_idx_f]['name']}"
                            dict_t = f"{target_record.lower()}_{flat_t[col_idx_t]['name']}"
                            filters = []
                            target_to_from_map = {flat_t[col_idx_t]['name']: flat_f[col_idx_f]['name']}
                            if len(f_parts) == 2 or is_edb:
                                for left_f, op_f, right_f in conditions:
                                    if op_f == "==":
                                        if right_f.isdigit() or right_f.startswith(('"', "'")):
                                            parts_f_filter = left_f.split(".")
                                            if parts_f_filter[0] == f_alias:
                                                attr_to_check = "_".join(parts_f_filter[1:])
                                                idx_to_check = next((i for i, ad in enumerate(flat_f) if ad['name'] == attr_to_check or ad['name'].startswith(attr_to_check + "_")), -1)
                                                
                                                val_to_check = int(right_f) if right_f.isdigit() else self.get_string_id(right_f)
                                                
                                                if idx_to_check != -1:
                                                    filters.append((idx_to_check, val_to_check))
                                                    
                            for tup in self.facts.get(source_rec_name, []):
                                if all(tup[idx] == val for idx, val in filters):
                                    new_tup = []
                                    for ad in flat_t:
                                        t_attr_name = ad['name']
                                        if t_attr_name in target_to_from_map:
                                            f_attr_name = target_to_from_map[t_attr_name]
                                            idx_in_f = next((i for i, f_ad in enumerate(flat_f) if f_ad['name'] == f_attr_name), -1)
                                            if idx_in_f != -1:
                                                new_tup.append(tup[idx_in_f])
                                                continue
                                        val = target_static_facts.get(t_attr_name)
                                        if val is not None:
                                            new_tup.append(val)
                                            continue
                                        idx_in_f = next((i for i, f_ad in enumerate(flat_f) if f_ad['name'] == t_attr_name), -1)
                                        if idx_in_f != -1:
                                            new_tup.append(tup[idx_in_f])
                                            continue
                                        new_tup.append(None)
                                    tup_to_add = tuple(new_tup)
                                    if tup_to_add not in self.facts[target_record]:
                                        self.facts[target_record].append(tup_to_add)
                            iter_t = iterators_map[t_alias].get(t_attr) or iterators_map[t_alias].get('BASE')
                            if iter_f and iter_t:
                                is_edb = self.is_base_domain(source_rec_name) or len(self.facts.get(source_rec_name, [])) > 0
                                if is_edb:
                                    mzn_conditions.append(f"{dict_t}[{iter_t}] == {dict_f}[{iter_f}]")
                                else:
                                    iterators_map[t_alias][t_attr] = iter_f
                                    iterators_map[t_alias]['BASE'] = iter_f
                            continue
                    if len(parts_l) <= 2 and len(parts_right) <= 2:
                        iter_l = iterators_map[alias_l].get(attr_l)
                        iter_r = iterators_map[alias_r].get(attr_r)
                        if iter_l and iter_r:
                            self._merge_mapped_iterators(iter_l, iter_r, iterators_map, mzn_conditions, negated_aliases, fused_iters, target_indices)
                            continue
                    if len(parts_l) == 3 and len(parts_right) == 3:
                        sub_attr_l = parts_l[2]
                        sub_attr_r = parts_right[2]
                        iter_l_name = iterators_map[alias_l].get(attr_l)
                        iter_r_name = iterators_map[alias_r].get(attr_r)
                        rec_name_l = self.current_alias_map.get(alias_l)
                        rec_name_r = self.current_alias_map.get(alias_r)
                        type_l = next((ad['type'] for ad in self.records.get(rec_name_l, []) if ad['name'] == attr_l), None)
                        type_r = next((ad['type'] for ad in self.records.get(rec_name_r, []) if ad['name'] == attr_r), None)
                        
                        if iter_l_name and iter_r_name and type_l and type_r:
                            dict_l = f"{type_l.lower()}_{sub_attr_l}"
                            dict_r = f"{type_r.lower()}_{sub_attr_r}"
                            mzn_conditions.append(f"{dict_l}[{iter_l_name}] == {dict_r}[{iter_r_name}]")
                            continue
            if res_l and res_r:
                if parsed_op == "==" and res_l in all_valid_iters and res_r in all_valid_iters:
                    self._merge_mapped_iterators(res_l, res_r, iterators_map, mzn_conditions, negated_aliases, fused_iters, target_indices)
                    continue
                if parsed_op == "==" and str(res_l).strip() == str(res_r).strip():
                    continue 
                mzn_conditions.append(f"{res_l} {parsed_op} {res_r}")
        recursive_replacements = {}
        for r_name, r_alias in from_records:
            actual_guess_key = next((k for k in getattr(self, 'guess_domains', {}).keys() if k.lower() == r_name.lower()), None)
            is_guess = actual_guess_key is not None
            if is_guess:
                g_dom = self.guess_domains[actual_guess_key]
                from_recs = g_dom.get('from', [])
                to_recs = g_dom.get('to_recs', [])
                to_rec = to_recs[0] if to_recs else ''
                is_bool = g_dom.get('fallback_bool', False)
                limits = g_dom.get('limits', [])
                is_exactly_1 = len(limits) == 1 and limits[0]['type'] == 'exactly' and str(limits[0]['val']).strip() == "1"
                is_at_most_1 = len(limits) == 1 and limits[0]['type'] == 'at most' and str(limits[0]['val']).strip() == "1"
                preconds = self.rule_headers.get(actual_guess_key, {}).get('preconds', [])
                is_functional = (is_exactly_1 or is_at_most_1) and not is_bool
                arr_name = actual_guess_key.lower()
                keys = []
                for r in from_recs:
                    val = iterators_map[r_alias].get(r.lower())
                    if not val and len(from_recs) == 1:
                        val = iterators_map[r_alias].get('BASE')
                    keys.append(val)
                if len(keys) == len(from_recs) and (all(keys) or not from_recs):
                    arr_access = f"{arr_name}[{', '.join(keys)}]" if keys else arr_name
                    if not to_rec or to_rec.lower() == actual_guess_key.lower():
                        if is_bool:
                            mzn_conditions.append(arr_access)
                        else:
                            mzn_conditions.append(f"{arr_access} > 0")
                    elif is_functional:
                        iterators_map[r_alias][to_rec.lower()] = arr_access
                        if is_at_most_1:
                            mzn_conditions.append(f"{arr_access} > 0")
                    elif is_bool:
                        vals = []
                        for tr in to_recs:
                            v = iterators_map[r_alias].get(tr.lower())
                            if v: vals.append(v)
                        if len(vals) == len(to_recs):
                            bool_access = f"{arr_name}[{', '.join(keys + vals)}]" if (keys or vals) else arr_name
                            mzn_conditions.append(bool_access)
                    else:
                        val = iterators_map[r_alias].get(to_rec.lower())
                        if val:
                            mzn_conditions.append(f"{val} in {arr_access}")
            elif not self.is_base_domain(r_name) and len(self.facts.get(r_name, [])) == 0:
                rec_indices = [iterators_map[r_alias].get(ad['name'].lower(), "1") for ad in self.records.get(r_name, [])]
                arr_acc = f"{r_name.lower()}[{', '.join(rec_indices)}]" if rec_indices else r_name.lower()
                mzn_conditions.append(arr_acc)
                if getattr(self, 'is_recursive_active', False) and target_record in self.recursive_records and r_name in self.recursive_records:
                    t_idx = f"[{', '.join(target_indices)}]" if target_indices else ""
                    d_idx = f"[{', '.join(rec_indices)}]" if rec_indices else ""
                    rank_check = f"rank_{target_record.lower()}{t_idx} > rank_{r_name.lower()}{d_idx}"
                    arr_acc_acyclic = f"({arr_acc} /\\ {rank_check})"
                    recursive_replacements[arr_acc] = arr_acc_acyclic
        mzn_aggregates = self._translate_aggregates(rule.get('aggregates', []), iterators_map, rule)
        if mzn_aggregates:
            mzn_conditions.extend(mzn_aggregates)
        main_conds, negated_blocks, main_iters_names = self._build_negated_blocks(mzn_conditions, from_iters_defs, fused_iters, negated_aliases)
        all_final_conds = main_conds + negated_blocks
        all_final_conds = list(dict.fromkeys(all_final_conds))
        final_body = " /\\ ".join(all_final_conds) if all_final_conds else "true"
        final_body_acyclic = final_body
        for orig, new_val in recursive_replacements.items():
            pattern = rf"(?<!\w){re.escape(orig)}(?!\w|\[)"
            final_body_acyclic = re.sub(pattern, new_val, final_body_acyclic)
        active_from_iters = [from_iters_defs[i] for i in main_iters_names]
        if active_from_iters:
            final_body = f"exists({', '.join(active_from_iters)})(\n        {final_body}\n    )"
            final_body_acyclic = f"exists({', '.join(active_from_iters)})(\n        {final_body_acyclic}\n    )"
        if target_record not in self.rule_bodies:
            self.rule_bodies[target_record] = []
            self.rule_bodies_acyclic[target_record] = []
        self.rule_bodies[target_record].append(final_body)
        self.rule_bodies_acyclic[target_record].append(final_body_acyclic)
        self.rule_headers[target_record] = {
            'dims': target_dims,
            'iters': target_iters,
            'indices': target_indices
        }
        return

    def process_rules(self):
        global recursive
        if not recursive:
            self.extract_scc()
            self.is_recursive_active = len(self.recursive_records) > 0
        else:
            self.is_recursive_active = False
        self._process_static_facts()
        self._infer_implicit_domains()
        sorted_rules = sorted(self.raw_rules, key=lambda r: 1 if r.get('is_deny') else 0)
        for rule in sorted_rules:
            self._clean_rule_aliases(rule)
            if rule.get('is_deny') or rule.get('is_assert'):
                self._process_deny_assert(rule)
                continue
            if rule.get('type') == 'guess' or rule.get('is_guess'):
                self._process_guess(rule)
                continue
            # RIMOSSI I CONTROLLI from_records E aggregates PER PROCESSARE ANCHE I FATTI STATICI
            if rule.get('is_define'):
                self._process_define(rule)
                
    def def_1(self, args):
        clean_args = [arg for arg in args if str(arg) != ";"]
        targets = clean_args[0]
        context_records = []
        conditions = []
        aggregates = []
        for arg in clean_args:
            if isinstance(arg, list) and len(arg) > 0 and isinstance(arg[0], dict) and 'aggr_type' in arg[0]:
                aggregates.extend(arg)
            elif isinstance(arg, dict) and 'aggr_type' in arg:
                aggregates.append(arg)
        core_args = [a for a in clean_args if not (isinstance(a, dict) and 'aggr_type' in a) and not (isinstance(a, list) and len(a)>0 and isinstance(a[0], dict) and 'aggr_type' in a[0])]

        if len(core_args) == 3:
            context_records = core_args[1]
            conditions = core_args[2]
        elif len(core_args) == 2:
            conditions = core_args[1]
        self.raw_rules.append({
            'is_define': True,
            'targets': targets,
            'from_records': context_records,
            'conditions': conditions,
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy() if hasattr(self, 'current_alias_map') else {},
            'negated_atoms': self.negated_atoms.copy()
        })
        self.init_define_variables()
        return ""
    
    def def_2(self, args):
        clean_args = [arg for arg in args if str(arg) != ";"]
        targets = clean_args[0]
        aggregates = clean_args[-1] 
        conditions = clean_args[-2] 
        context_records = []
        if len(clean_args) == 4:
            context_records = clean_args[1]
        self.raw_rules.append({
            'is_define': True,
            'targets': targets,
            'from_records': context_records,
            'conditions': conditions,
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy() if hasattr(self, 'current_alias_map') else {},
            'negated_atoms': self.negated_atoms.copy()
        })
        self.init_define_variables()
        return ""

    def def_3(self, args):
        clean_args = [arg for arg in args if str(arg) != ";"]
        targets = clean_args[0]
        aggregates = clean_args[-1] 
        conditions = []             
        context_records = []
        if len(clean_args) == 3:
            context_records = clean_args[1]
        self.raw_rules.append({
            'is_define': True,
            'targets': targets,
            'from_records': context_records,
            'conditions': conditions,
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy() if hasattr(self, 'current_alias_map') else {},
            'negated_atoms': self.negated_atoms.copy()
        })
        self.init_define_variables()
        return ""
    
    def define_expression(self, args):
        res_parts = []
        final_type = "any"
        operators = ["*", "+", "-", "/"]
        integer_operation = any(str(arg) in operators for arg in args)
        for i, arg in enumerate(args):
            arg_str = str(arg)
            if arg_str == "/":
                if i + 1 < len(args):
                    denom_str = str(args[i+1])
                    denom_val = denom_str.rsplit("/", 1)[0] if "/" in denom_str and denom_str not in operators else denom_str
                    if denom_val == "0":
                        raise ValueError("Division by zero detected! You cannot divide by a literal 0.")
        for arg in args:
            arg_str = str(arg)
            if arg_str in operators:
                res_parts.append(arg_str)
                continue
            if "/" in arg_str:
                parts = arg_str.rsplit("/", 1)
                val = parts[0]
                typ = parts[1] if len(parts) > 1 else "any"
                res_parts.append(val)
                if typ != "any":
                    final_type = typ
                if integer_operation and typ != "int" and typ != "any":
                    raise ValueError(error_messages.UNSUPPORTED_ARITHMETIC_OPERATION)
            else:
                res_parts.append(arg_str)
        expr_str = "".join(res_parts)
        self.define_expressions.append(expr_str)
        if integer_operation:
            final_type = "int"
        return f"{expr_str}/{final_type}"

    def exp_aggr_define(self, args):
        return self.define_expression(args)
    
    def var_define(self, args):
        if isinstance(args[0], Token):
            type_value = args[0].type.lower()
            if type_value == "str":
                return f"'{args[0]}'/str"
            elif type_value == "minus":
                return f"-{args[1]}/int"
            else:
                return f"{args[0]}/{type_value}"
        return args[0]
    
    def attributes_check(self, args):
        attribute_type = ""
        if isinstance(args[0], Token):
            if args[0].type == "RECORD_NAME":
                attribute_type = args[0]
            if args[0].type == "NAME":
                if args[0] in self.declared_alias:
                    attribute_type = self.declared_alias[args[0]]
                else:
                    attribute_type = self.redefined_record[args[0]]
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    if attribute_type in ["str", "int"]:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                    found = False
                    for t in records_global[attribute_type]:
                        if t.value == args[i]:
                            attribute_type = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                else:
                    break
        return attribute_type 

    def value_def(self, args):
        
        attribute_type = self.attributes_check(args)
        return {
            "node_type": "value_access",
            "path": "".join(args),
            "final_type": attribute_type
        }
    
    def value_define(self, args):
        if not (args[0] in self.redefined_record.keys() or args[0] in self.defined_record):
            if not args[0] in self.declared_alias.keys() and not args[0] in self.defined_records:
                raise ValueError(error_messages.undefined_element(args[0]))
        res = self.value_def(args)
        return f"{res['path']}/{res['final_type']}"
    
    def operator(self, args):
        return args[0]
    
    def verify_int(self, arg):
        splitted = arg.split("/")
        if len(splitted) > 1:
            if splitted[1] != "int":
                raise ValueError(f"Expected int, received: {splitted[1]}")
            return splitted[0]
        return arg
    
    def range_define(self, args):
        
        def get_val(v):
            return v.split("/")[0] if isinstance(v, str) and "/" in v else str(v)
        if args[0] in ["-", "+"]:
            low = f"{args[0]}{get_val(self.verify_int(args[1]))}"
            high_idx = 3 if args[3] not in ["-", "+"] else 4
            high = f"{args[3]}{get_val(self.verify_int(args[4]))}" if args[3] in ["-", "+"] else get_val(self.verify_int(args[3]))
        else:
            low = get_val(self.verify_int(args[0]))
            high = f"{args[2]}{get_val(self.verify_int(args[3]))}" if args[2] in ["-", "+"] else get_val(self.verify_int(args[2]))
        return f"{low}..{high}/int"
    
    def op(self, args):
        return args[0]
    def deny(self, args):
        return args
    
    def deny_1(self, args):
        from_records = args[0]
        conditions = args[1]
        aggregates = args[2] if len(args) > 2 else []
        self.raw_rules.append({
            'is_deny': True,
            'from_records': from_records,
            'conditions': conditions,
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy(),
            'negated_atoms': self.negated_atoms.copy()
        })
        self.init_define_variables()
        return ""

    def deny_2(self, args):
        from_records = args[0]
        aggregates = args[1]
        
        self.raw_rules.append({
            'is_deny': True,
            'from_records': from_records,
            'conditions': [], 
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy(),
            'negated_atoms': self.negated_atoms.copy()
        })
        self.init_define_variables()
        return ""
    
    def guess(self, args):
        self.count_guess += 1
        self.guess_count = guess_alias[self.count_guess]["number"]
        self.new_guess_alias = {}
        self.guess_alias = {}
        self.guess_check = []
        self.guess_records = set()
        self.aggregate_records = set()
        self.aggregate_with = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.negated_atoms = []
        return args
    
    def _extract_guess_middle_args(self, middle_args, current_alias_map):
        found_aggregates = []
        found_limits = []
        found_conditions = []
        def recursive_walk(item):
            nonlocal found_limits
            if isinstance(item, dict) and 'aggr_type' in item:
                found_aggregates.append(item)
                return
            if isinstance(item, dict) and item.get('is_times'):
                found_limits = item['limits']
                return
            if isinstance(item, list) and len(item) >= 2 and str(item[0]).lower() in ['exactly', 'at most', 'at least']:
                parsed = self.guess_times(item)
                found_limits = parsed['limits']
                return
            if isinstance(item, tuple) and len(item) == 3 and isinstance(item[0], str):
                found_conditions.append(item)
                return
            if hasattr(item, 'children'):
                for child in item.children:
                    recursive_walk(child)
            elif isinstance(item, list):
                for sub in item:
                    recursive_walk(sub)
        for arg in middle_args:
            recursive_walk(arg)
        return found_aggregates, found_limits, found_conditions
    
    def _extract_guess_targets(self, targets_ast):
        group_id = str(uuid.uuid4())
        parsed_targets = []
        group_target_names = []
        for t_ast in targets_ast:
            t_rec = str(t_ast[0])
            if len(t_ast) > 1 and getattr(t_ast[1], 'type', '') == 'NAME':
                t_alias = str(t_ast[1])
                body_start_idx = 2  
            else:
                t_alias = t_rec.lower()
                body_start_idx = 1  
            
            t_to_recs = []
            t_conditions = []
            
            def extract_target_details(item):
                if hasattr(item, 'type') and item.type == 'RECORD_NAME':
                    t_to_recs.append(str(item))
                elif isinstance(item, tuple) and len(item) == 3 and isinstance(item[0], str):
                    t_conditions.append(item)
                elif hasattr(item, 'children'):
                    for child in item.children:
                        extract_target_details(child)
                elif isinstance(item, list):
                    for sub in item:
                        extract_target_details(sub)
                        
            if len(t_ast) > body_start_idx:
                extract_target_details(t_ast[body_start_idx:])
            group_target_names.append(t_rec)
            parsed_targets.append({
                'rec': t_rec,
                'alias': t_alias,
                'to_recs': t_to_recs if t_to_recs else [t_rec],
                'conditions': t_conditions
            })
        is_multi_target = len(parsed_targets) > 1
        return parsed_targets, group_id, is_multi_target, group_target_names
    
    def _extract_ast_aliases(self, item):
        if isinstance(item, list):
            if len(item) == 2 and isinstance(item[0], str) and isinstance(item[1], str) and item[0][0].isupper():
                self.current_alias_map[item[1]] = item[0]
            elif len(item) == 1 and isinstance(item[0], str) and item[0][0].isupper():
                self.current_alias_map[item[0]] = item[0]
            for sub in item:
                self._extract_ast_aliases(sub)

    def guess_def_1(self, args):
        clean_args = [arg for arg in args if str(arg) != ";"]
        from_recs = []
        times_limits=[]
        target_rec = None
        target_alias = None
        to_rec = None
        guess_conditions = []
        aggregates = [] 
        from_block = clean_args[0]
        if isinstance(from_block, list):
            for item in from_block:
                if isinstance(item, list) and len(item) >= 1:
                    rec_name = str(item[0])
                    from_recs.append(rec_name)
                    if len(item) == 2:
                        alias = str(item[1])
                        self.current_alias_map[alias] = rec_name
        def_block_wrapper = clean_args[-1]
        if isinstance(def_block_wrapper, list) and len(def_block_wrapper) > 0 and isinstance(def_block_wrapper[0], list):
            definition_block = def_block_wrapper[0] 
            target_rec = str(definition_block[0])
            if len(definition_block) > 2: 
                target_alias = str(definition_block[1])
                self.current_alias_map[target_alias] = target_rec
            declaration_block = definition_block[-1]
            if len(declaration_block) > 0:
                self._extract_ast_aliases(declaration_block[0])
            try:
                to_rec_info = declaration_block[0]
                while isinstance(to_rec_info, list) and len(to_rec_info) > 0:
                    to_rec_info = to_rec_info[0]
                if isinstance(to_rec_info, str) and "." not in to_rec_info and "==" not in to_rec_info:
                    to_rec = str(to_rec_info)
                else:
                    to_rec = None
            except (IndexError, TypeError): 
                to_rec = None
            if len(declaration_block) > 0:
                if isinstance(declaration_block[-1], list):
                    inner_conds = [c for c in declaration_block[-1] if isinstance(c, tuple)]
                    guess_conditions.extend(inner_conds)
                elif isinstance(declaration_block[0], tuple): 
                    inner_conds = [c for c in declaration_block if isinstance(c, tuple)]
                    guess_conditions.extend(inner_conds)
        middle_args = clean_args[:-1] 
        aggregates, times_limits, extra_conds = self._extract_guess_middle_args(
            middle_args, 
            self.current_alias_map
        )
        guess_conditions.extend(extra_conds)
        targets_ast = clean_args[-1]
        parsed_targets, group_id, is_multi_target, group_target_names = self._extract_guess_targets(targets_ast)
        for pt in parsed_targets:
            combined_conds = extra_conds.copy() + pt['conditions']
            self.guess_domains[pt['rec']] = {
                'from': from_recs,  
                'to_recs': pt['to_recs'],
                'limits': times_limits,
                'conditions': combined_conds,
                'fallback_bool': True if (is_multi_target or len(pt['to_recs']) > 1) else self.guess_domains.get(pt['rec'], {}).get('fallback_bool', False),
                'group_id': group_id if is_multi_target else None,
                'group_targets': group_target_names if is_multi_target else None
            }
            self.raw_rules.append({
                'type': 'guess',
                'target_record': pt['rec'],
                'target_alias': pt['alias'],
                'from_recs': from_recs,
                'to_recs': pt['to_recs'], 
                'conditions': combined_conds,
                'aggregates': aggregates,
                'alias_map_snapshot': getattr(self, 'current_alias_map', {}).copy()
            })
        self.current_alias_map = {}
    
    def guess_def_2(self, args):
        return self.guess_def_1(args)
    
    def record_guess(self, args):
        return self.guess_record(args)
    
    def where_guess(self, args):
        self.guess_check = []
        return args
    
    def from_guess(self, args):
        recs = [arg for arg in args if isinstance(arg, dict)]
        global g, recursive
        temp = []
        if self.count_guess in guess_alias:
            for alias in guess_alias[self.count_guess].keys():
                if alias != "number":
                    en = guess_records[self.count_guess][alias]
                    self.increment_num(en)
                    temp.append(en)
        for arg in recs:
            if isinstance(arg, list) and len(arg) > 0:
                rec_name = str(arg[0]) if arg[0] != "not" else str(arg[1])
                self.increment_num(rec_name)
                for t in temp:
                    if recursive and rec_name == t:
                        raise ValueError(error_messages.CYCLIC_DEPENDENCY)
                    g.add_edge(num_pred[rec_name], num_pred[t])
        return args
    
    def guess_from(self, args):
        return args

    def guess_declaration(self, args):
        return args
    
    def add_edge_guess(self, args, pred_guess):
        global g, recursive
        self.increment_num(pred_guess)
        en = str(args)
        if recursive and en == pred_guess:
            raise ValueError(error_messages.CYCLIC_DEPENDENCY)
        self.increment_num(en)
        g.add_edge(num_pred[en], num_pred[pred_guess])

    def guess_definition(self, args):
        target_rec = str(args[0])
        decl = args[-1]
        try:
            to_rec_info = decl[0]
            while isinstance(to_rec_info, list) and len(to_rec_info) > 0:
                to_rec_info = to_rec_info[0]
            from_guess = str(to_rec_info)
            
            if len(from_guess) > 0:
                self.add_edge_guess(from_guess, target_rec)
        except (IndexError, TypeError):
            pass
        if not target_rec in records_global.keys():
            raise ValueError(error_messages.undefined_alias(target_rec))
        if len(args) > 2:
            target_alias = str(args[1])
            if target_alias in self.guess_alias:
                raise ValueError(error_messages.alias_defined(target_alias))
            for en in self.guess_check:
                if str(en) != target_alias:
                    raise ValueError(error_messages.undefined_alias(en))
                    
        else:
            if target_rec in self.guess_records:
                raise ValueError(error_messages.record_defined(target_rec))
            for en in self.guess_check:
                if str(en) != target_rec:
                    raise ValueError(error_messages.undefined_record(en))
        self.guess_check = []
        self.guess_alias = {}
        self.guess_records = set()
        
        return args

    def access_nested_dict(self, dictionary, keys):
        if not keys:
            return
        curr_keys = keys[0]
        if curr_keys in dictionary:
            nested_dictionary = dictionary[curr_keys]
            if len(keys) == 1:
                dictionary[curr_keys] = True
            else:
                return self.access_nested_dict(nested_dictionary, keys[1:])
        else:
            pass

    def build_nested_dictionary(self, alias, args, current_dict=None):
        if current_dict is None:
            current_dict = {}
        for attr in records_global[args[0]]:
            if attr.type in ("int", "str", "any"):
                current_dict[attr.value] = False
            else:
                current_dict[attr.value] = {}
                self.build_nested_dictionary(alias, [attr.type], current_dict[attr.value])
        return current_dict
    
    def guess_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
        rec_name = args[0]
        if not rec_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
        alias = args[1] if len(args) > 1 else rec_name
        if len(args) > 1:
            if alias in self.guess_alias:
                raise ValueError(error_messages.alias_defined(alias))
            self.guess_alias[alias] = rec_name
        else:
            if rec_name in self.guess_records:
                raise ValueError(error_messages.record_defined(rec_name))
            self.guess_records.add(rec_name)
        if negated:
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
        return args
    
    def guess_times(self, args):
        limits = []
        current_type = None
        for arg in args:
            if isinstance(arg, dict) and arg.get('is_times'):
                limits.extend(arg['limits'])
                continue
            arg_str = str(arg)
            if ".." in arg_str:
                raise ValueError("the use of ranges (e.g., '1..5') is not allowed in guess cardinalities.")
            arg_lower = arg_str.lower()
            if arg_lower in ['exactly', 'at most', 'at least']:
                current_type = arg_lower
            elif current_type and arg_lower != 'and':
                limits.append({'type': current_type, 'val': arg_str})
                current_type = None 
        types = [l['type'] for l in limits]
        if 'exactly' in types and len(limits) > 1:
            raise ValueError("'exactly' is an absolute constraint and cannot be combined with 'at least' or 'at most'.")
        if types.count('at least') > 1:
            raise ValueError("you cannot specify more than one 'at least' constraint in the same guess.")
        if types.count('at most') > 1:
            raise ValueError("you cannot specify more than one 'at most' constraint in the same guess.")
        return {'is_times': True, 'limits': limits}
    
    def guess_definitions(self, args):
        return args
    def guess_where(self, args):
        return args

    def where_guess_statement(self, args):
        return self.guess_where_check_(args)

    def guess_where_statement(self, args):
        return self.guess_where_check_(args)
    
    def var_guess(self, args):
        return self.var_define(args)
    
    def var_guess_2(self, args):
        return self.var_define(args)
    
    def attributes_guess_check(self, args):
        attribute = ""
        if args[0] in self.guess_alias:
            attribute = self.guess_alias[args[0]]
        if args[0] in self.guess_records:
            attribute = args[0]
        if args[0] in guess_records[self.count_guess]:
            attribute = guess_records[self.count_guess][args[0]]
            if not args[0] in guess[self.count_guess]:
                self.guess_check.append(args[0])
        if args[0] in records_global.keys():
            attribute = args[0]
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    if attribute == "str" or attribute == "int":
                        raise ValueError(error_messages.no_attribute(attribute, args[i]))
                    found = False
                    for t in records_global[attribute]:
                        if t.value == args[i]:
                            attribute = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(error_messages.no_attribute(attribute, args[i]))
                else:
                    break
        return attribute
    
    def value_guess_check(self, args):
        statement = ""
        attribute = self.attributes_guess_check(args)
        if args[0] in guess_alias[self.count_guess].keys():
            args[0] = guess_alias[self.count_guess][args[0]]
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement + "/" + attribute
    
    def value_guess(self, args):
        if not args[0] in guess_records[self.count_guess].keys():
            raise ValueError(error_messages.undefined_element(args[0]))
        return self.value_guess_check(args)
    
    def value_guess_2(self, args):
        if not (args[0] in self.guess_alias.keys() or args[0] in self.guess_records or args[0] in guess_records[self.count_guess].keys()):
            raise ValueError(error_messages.undefined_element(args[0]))
        elif args[0] in self.aggr_alias:
            raise ValueError(error_messages.undefined_element(args[0]))
        return self.value_guess_check(args)
    
    def var_aggr_define(self, args):
        return self.var_define(args)

    def times_value(self, args):
        statement = ""
        if not (args[0] in guess_records[self.count_guess].keys()):
            raise ValueError(error_messages.undefined_record(args[0]))
        attribute = self.attributes_guess_check(args)
        if attribute != "int" and attribute != "any":
            raise ValueError(f"Expected int, received: {attribute}")
        if args[0] in guess_alias[self.count_guess].keys():
            args[0] = guess_alias[self.count_guess][args[0]]
            
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement
    
    def var_guess_exp(self, args):
        return self.exp_aggr_define(args)

    def var_guess_exp_2(self, args):
        return self.exp_aggr_define(args)

    def aggr_guess_exp(self, args):
        return self.exp_aggr_define(args)
    
    def times_exp(self, args):
        stat = ""
        for i in range(len(args)):
            if args[i] == ")" or args[i] == "(":
                stat += args[i]
                continue
            
            if "/" in str(args[i]) and "int" in str(args[i]):
                args[i] = str(args[i]).split("/")[0]
                
            stat += str(args[i])
        return stat
    
    def times(self, args):
        return args[0]

    def where_deny_statement(self, args):
        return self.where_stat_check(args)
    
    def where_deny(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    def deny_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
        rec_name = str(args[0])
        if not rec_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
        alias = str(args[1][0]) if len(args) > 1 and isinstance(args[1], list) else str(args[1]) if len(args) > 1 else rec_name
        if len(args) > 1:
            if alias in self.declared_alias or alias in self.redefined_record.keys():
                raise ValueError(error_messages.alias_defined(alias))
            self.declared_alias[alias] = rec_name
        else:
            if rec_name in self.defined_records or rec_name in self.defined_record:
                raise ValueError(error_messages.record_defined(rec_name))
            self.defined_records.add(rec_name)
            
        self.attributes[alias] = list(records_global[rec_name])
        
        if negated:
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
            
        return (rec_name, alias)
    
    def deny_from(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    def var(self, args):
        return self.var_define(args)

    def var_expression(self, args):
        return self.define_expression(args)

    def range_var(self, args):
        return self.range_define(args)

    def value(self, args):
        base_name = str(args[0])
        if not (base_name in self.defined_record or base_name in self.redefined_record.keys()):
            if not base_name in self.declared_alias.keys() and not base_name in self.defined_records:
                raise ValueError(error_messages.undefined_element(base_name))
        
        res = self.value_def(args)
        
        return f"{res['path']}/{res['final_type']}"
    
    def isNum(self, args):
        try:
            int(args)
            return True
        except ValueError:
            return False
        
    def get_string_id(self, s):
        clean_s = str(s).strip("\"'")
        if clean_s not in self.string_to_id:
            self.string_to_id[clean_s] = self.string_counter
            self.id_to_string[self.string_counter] = clean_s
            self.string_counter += 1
        return self.string_to_id[clean_s]

    def get_flattened_attrs(self, record_name, prefix=""):
        attrs = []
        if record_name not in self.records:
            return [{"name": prefix.strip("_"), "type": "any"}]
        for attr_dict in self.records[record_name]:
            attr_name = attr_dict["name"]
            attr_type = attr_dict["type"]
            new_prefix = f"{prefix}{attr_name}_"
            if attr_type in self.records:
                attrs.extend(self.get_flattened_attrs(attr_type, new_prefix))
            else:
                attrs.append({"name": new_prefix.strip("_"), "type": attr_type})
        return attrs
    

    def record_declaration(self, args):
        record_name = str(args[0])
        self.records[record_name] = []
        self.dependencies[record_name] = self.records_attributes.copy()
        declarations = args[2]
        for i in range(0, len(declarations), 2):
            attr_name = str(declarations[i][0])
            attr_type = str(declarations[i][2]) 
            self.records[record_name].append({
                "name": attr_name, 
                "type": attr_type
            })
            
        return args
    
    def declarations(self, args):
        return args
    
    def recursive_declaration_checking(self, args, verify_list, attr_list):
        for attr in attr_list:
            if attr.type != "int" and attr.type != "any" and attr.type != "str":
                if attr.type == args:
                    raise ValueError(error_messages.RECURSIVE_DEPENDENCY_BETWEEN_RECORDS)
                verify_list.append(attr.type)
        return verify_list
    
    def declaration(self, args):
        attr_type = args[2]
        if attr_type in records_global.keys():
            self.records_attributes.append(attr_type)
        
        if not (attr_type == "int" or attr_type == "any" or attr_type == "str"):
            if attr_type not in records_global.keys():
                raise ValueError(error_messages.undefined_record(attr_type))
            verify_list = self.recursive_declaration_checking(attr_type, [], records_global[attr_type])
            while verify_list:
                verify = records_global[verify_list.pop()]
                verify_list = self.recursive_declaration_checking(attr_type, verify_list, verify)
        return args
    def attr_type(self, args):
        return args[0]
    
    def define(self, args):
        return ""
    
    def init_define_variables(self):
        self.redefined_record = {}
        self.defined_record = set()
        self.declared_alias = {}
        self.defined_records = set()
        self.attributes = {}
        self.aggregate_records = set()
        self.aggregate_with = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.otherwise_en = []
        self.count = 0
        self.define_expressions = []
        self.negated = {}
        self.negated_atoms = []
        self.current_alias_map = {}

    def define_definition(self, args):
        self.declared_alias = {}
        self.defined_records = set()
        record_name = str(args[0])
        alias = record_name
        
        if not record_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(args[0]))

        self.attributes = {}
        attr = records_global[args[0]]
        self.attributes[args[0]] = list(attr)
        
        alias = args[1] if len(args) > 1 else args[0]
        
        
        if len(args) > 1:
            self.redefined_record[args[1]] = args[0]
        else:
            self.defined_record.add(args[0])
            
        self.current_alias_map[alias] = record_name
        self.current_record = record_name
        self.current_alias = alias
        self.current_fact_attrs = {}
        
        return alias
    
    def as_statement(self, args):
        return str(args[0])
    
    def define_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
            
        rec_name = str(args[0])
        if not rec_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(args[0]))
        alias = args[1] if len(args) > 1 else args[0]
        var = alias
        if len(args) > 1:
            if alias in self.declared_alias or alias in self.redefined_record.keys():
                raise ValueError(error_messages.alias_defined(alias))
            
            self.declared_alias[alias] = args[0]
        else:
            if args[0] in self.defined_records or args[0] in self.defined_record:
                raise ValueError(error_messages.record_defined(args[0]))
            self.defined_records.add(args[0])
            
        self.attributes[var] = list(records_global[args[0]])
        if negated:
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)

        return (rec_name, alias)

    def define_from(self, args):
        record_names = []
        for arg in args:
            if isinstance(arg, tuple):
                record_name, alias = arg
                if alias not in getattr(self, 'negated_atoms', []):
                    record_names.append(record_name)
        self.add_edge(record_names)
        return [arg for arg in args if isinstance(arg, tuple)]

    def increment_num(self, en):
        global num
        if not en in num_pred.keys():
            num_pred[en] = num
            num += 1

    def add_edge(self, args):
        pred_define = ""
        for alias in self.redefined_record.values():
            pred_define = alias
        for en in self.defined_record:
            pred_define = en
        global g, recursive
        self.increment_num(pred_define)
        for arg in args:
            pred=str(arg)
            if recursive and pred == pred_define:
                raise ValueError(error_messages.CYCLIC_DEPENDENCY)
            self.increment_num(pred)
            g.add_edge(num_pred[pred], num_pred[pred_define])

    def check_negated_atoms(self, args):
        for neg in self.negated_atoms:
            arg = ""
            val_0 = args[0].split("/")[0] if isinstance(args[0], str) and "/" in args[0] else str(args[0])
            val_1 = args[-1].split("/")[0] if isinstance(args[-1], str) and "/" in args[-1] else str(args[-1])
            
            if neg in val_0:
                arg = val_0
            elif neg in val_1:
                arg = val_1
                
            if arg != "":
                pattern = re.compile(r'{}((?:\.[a-zA-Z0-9_]+)+)'.format(re.escape(neg)))
                match = pattern.search(arg)
                if match:
                    terms = match.group(1).split('.')
                    self.access_nested_dict(self.negated[neg], terms[1:])


    def where_stat_check(self, args):
        if args[-2] == "=":
            raise TypeError("Unexpected operator \"=\". Did you mean to use \"==\" instead?")
        
        
        splitted_l = str(args[0]).rsplit("/", 1)
        val_l = splitted_l[0]
        type_l = splitted_l[1] if len(splitted_l) > 1 else "any"
        
        operator = args[-2]
        if hasattr(operator, 'value'): operator = operator.value
        
        splitted_r = str(args[-1]).rsplit("/", 1)
        val_r = splitted_r[0]
        type_r = splitted_r[1] if len(splitted_r) > 1 else "any"

        
        def is_literal(v):
            return v.isdigit() or v.startswith(('"', "'")) or (v.startswith('-') and v[1:].isdigit())
        
        
        if is_literal(val_l) and not is_literal(val_r):
            val_l, val_r = val_r, val_l
            type_l, type_r = type_r, type_l
            
            
            swap_ops = {">": "<", "<": ">", ">=": "<=", "<=": ">=", "==": "==", "!=": "!="}
            if operator in swap_ops:
                operator = swap_ops[operator]
        

        if self.isNum(val_r) and self.isNum(val_l):
            raise ValueError(f"Unexpected boolean condition: {val_l}{operator}{val_r}")
        
        if not type_r == type_l and type_l != "any":
            if operator != "==":
                raise ValueError(f"{type_r} cannot be compared with type: {type_l}")
            raise ValueError(f"{type_r} cannot be assigned to type {type_l}")

        if self.negated_atoms:
            self.check_negated_atoms(args)
            
        return (str(val_l), str(operator), str(val_r))

    def guess_where_check_(self, args):
        return self.where_stat_check(args)

    def where_define_statement(self, args):
        for exp in self.define_expressions:
            rec = exp.split(".")[0] if "." in exp else exp.split("/")[0]
            if rec in self.aggr_new_alias.keys():
                raise ValueError(error_messages.undefined_element(self.aggr_new_alias[rec]))
        self.define_expressions = []
        return self.where_stat_check(args)

    def define_where(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]

        
    def assert_(self, args):
        return ""

    def assert_1(self, args):
        targets = args[0] 
        
        
        context_records = []
        conditions = []
        
        if len(args) == 3: 
            context_records = args[1]
            conditions = args[2]
        elif len(args) == 2: 
            conditions = args[1]
            
        self.raw_rules.append({
            'is_assert': True,
            'targets': targets, 
            'from_records': context_records,
            'conditions': conditions,
            'aggregates': [],
            'alias_map_snapshot': self.current_alias_map.copy()
        })
        self.init_define_variables()
        return ""

    def assert_2(self, args):
        targets = args[0]
        context_records = []
        conditions = []
        aggregates = args[-1] 
        
        if len(args) == 4:
            context_records = args[1]
            conditions = args[2]
        elif len(args) == 3:
            conditions = args[1]
            
        self.raw_rules.append({
            'is_assert': True,
            'targets': targets,
            'from_records': context_records,
            'conditions': conditions,
            'aggregates': aggregates,
            'alias_map_snapshot': self.current_alias_map.copy()
        })
        self.init_define_variables()
        return ""
    
    def assert_records(self, args):
        rec_name = str(args[0])
        
        if not rec_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
            
        alias = str(args[1]) if len(args) > 1 else rec_name
        
        if len(args) > 1:
            if alias in self.declared_alias or alias in self.redefined_record.keys():
                raise ValueError(error_messages.alias_defined(alias))
            self.redefined_record[alias] = rec_name
        else:
            if rec_name in self.defined_records or rec_name in self.defined_record:
                raise ValueError(error_messages.record_defined(rec_name))
            self.defined_record.add(rec_name)
            
        self.attributes[alias] = list(records_global[rec_name])
        return (rec_name, alias)

    def assert_definition(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    

    def assert_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
            
        rec_name = str(args[0])
        if not rec_name in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
            
        alias = str(args[1][0]) if len(args) > 1 and isinstance(args[1], list) else str(args[1]) if len(args) > 1 else rec_name
        
        if len(args) > 1:
            if alias in self.declared_alias or alias in self.redefined_record.keys():
                raise ValueError(error_messages.alias_defined(alias))
            self.declared_alias[alias] = rec_name
        else:
            if rec_name in self.defined_records or rec_name in self.defined_record:
                raise ValueError(error_messages.record_defined(rec_name))
            self.defined_records.add(rec_name)
            
        self.attributes[alias] = list(records_global[rec_name])
        
        if negated:
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
            
        return (rec_name, alias)

    def assert_from(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    
    def where_assert(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]

    def where_assert_statement(self, args):
        return self.where_stat_check(args)

    def var_assert(self, args):
        return self.var_define(args)

    def var_aggr_guess(self, args):
        return self.var_define(args)
    
    def range_assert(self, args):
        return self.range_define(args)

    def value_assert(self, args):
        return self.value(args)
    
    def assert_otherwise_1(self, args):
        targets = args[0]
        context = args[1] if len(args) == 3 else []
        conditions = args[-1]
        return {'targets': targets, 'from_records': context, 'conditions': conditions, 'aggregates': []}

    def assert_otherwise_2(self, args):
        targets = args[0]
        context = args[1] if len(args) == 4 else []
        conditions = args[-2]
        aggregates = args[-1]
        return {'targets': targets, 'from_records': context, 'conditions': conditions, 'aggregates': aggregates}


    def try_assert(self, args):
        rule_data = args[0]
        penalty = args[-2] 
        
        self.raw_rules.append({
            'is_assert': True,
            'is_weak': True,
            'targets': rule_data.get('targets', []),
            'from_records': rule_data.get('from_records', []),
            'conditions': rule_data.get('conditions', []),
            'aggregates': rule_data.get('aggregates', []),
            'penalty': penalty,
            'alias_map_snapshot': self.current_alias_map.copy(),
            'negated_atoms': self.negated_atoms.copy()
        })
        
        self.init_define_variables() 
        return ""

    def assert_otherwise_3(self, args):
        targets = args[0]
        context = args[1] if len(args) == 3 else []
        conditions = []  
        aggregates = args[-1]
        return {'targets': targets, 'from_records': context, 'conditions': conditions, 'aggregates': aggregates}

    def assert_otherwise_4(self, args):
        targets = args[0]
        context = []     
        conditions = []  
        aggregates = []  
        return {'targets': targets, 'from_records': context, 'conditions': conditions, 'aggregates': aggregates}

    def try_deny(self, args):
        rule_data = args[0]
        penalty = args[-2] 
        
        self.raw_rules.append({
            'is_deny': True,
            'is_weak': True,
            'from_records': rule_data.get('from_records', []),
            'conditions': rule_data.get('conditions', []),
            'aggregates': rule_data.get('aggregates', []),
            'penalty': penalty,
            'alias_map_snapshot': self.current_alias_map.copy(),
            'negated_atoms': self.negated_atoms.copy(), 
        })
        self.init_define_variables() 
        return ""

    def pay_statement(self, args):
        raw_values = [arg for arg in args if str(arg).lower() not in ["pay", "at", "or"]]

        weight_str = str(raw_values[0])
        if "/" in weight_str:
            parts = weight_str.rsplit("/", 1)
            w_val = parts[0]
            w_type = parts[1] if len(parts) > 1 else "any"
            if w_type != "int" and w_type != "any":
                raise ValueError(f"Penalty weight must be an integer, got: {w_type}")
            weight = w_val
        else:
            weight = weight_str

        if len(raw_values) > 1:
            level_str = str(raw_values[1])
            if "/" in level_str:
                parts = level_str.rsplit("/", 1)
                l_val = parts[0]
                l_type = parts[1] if len(parts) > 1 else "any"
                if l_type != "int" and l_type != "any":
                    raise ValueError(f"Penalty level must be an integer, got: {l_type}")
                level = l_val
            else:
                level = level_str
        else:
            level = "0"

        return {
            'weight': weight,
            'level': level
        }
    
    def pay(self, args):
        base_name = str(args[0])

        if not (base_name in self.defined_record or base_name in self.redefined_record.keys()):
            if not base_name in self.declared_alias.keys() and not base_name in self.defined_records:
                raise ValueError(error_messages.undefined_element(base_name))

        res = self.value_def(args)

        return f"{res['path']}/{res['final_type']}"
    
    def deny_otherwise(self, args):
        return args[0]

    def assert_otherwise(self, args):
        return args[0]
    
    def deny_otherwise_1(self, args):
        from_records = args[0]
        conditions = args[1]
        aggregates = args[2] if len(args) > 2 else []
        
        return {
            'from_records': from_records,
            'conditions': conditions,
            'aggregates': aggregates
        }

    def deny_otherwise_2(self, args):
        from_records = args[0]
        aggregates = args[1] if len(args) > 1 else []
        return {
            'from_records': from_records,
            'conditions': [],
            'aggregates': aggregates
        }
        
    def deny_otherwise_3(self, args):
        from_records = args[0]
        return {
            'from_records': from_records,
            'conditions': [],
            'aggregates': []
        }
    
    def abs2(self, args):
        expr = None
        for arg in args:
            if str(arg) != "|" and str(arg).lower() != "abs":
                expr = str(arg)
                break
                
        if expr is None:
            raise ValueError("Empty absolute value expression")
            
        
        if "/" in expr:
            parts = expr.rsplit("/", 1)
            val = parts[0]
            typ = parts[1] if len(parts) > 1 else "any"
            if typ != "int" and typ != "any":
                raise ValueError(f"Absolute value can only be applied to integers, got: {typ}")
        else:
            val = expr
            
        return f"abs({val})/int"

    def abs_aggr_define(self, args):
        return self.abs2(args)
        
    def abs_aggr_guess(self, args):
        return self.abs2(args)

    def range2(self, args):
        start_val = str(args[0])
        end_val = str(args[-1])
        if "/" in start_val:
            start_val = start_val.split("/")[0]
        if "/" in end_val:
            end_val = end_val.split("/")[0]
            
        return f"{start_val}..{end_val}/int"

    def range_aggr_define(self, args):
        return self.range2(args)
        
    def range_aggr_guess(self, args):
        return self.range2(args)
    
    def arithmetic_operation(self, args):
        return self.exp_aggr_define(args)

    def _format_aggr_targets(self, targets, local_alias_map):
        
        formatted = []
        for target in targets:
            if "/" in str(target): 
                formatted.append(str(target))
                continue
            en = str(target).split(".")[0]
            
            if en in self.aggr_new_alias: attribute = self.aggr_new_alias[en]
            elif en in local_alias_map: attribute = local_alias_map[en]
            elif en in self.redefined_record: attribute = self.redefined_record[en]
            else: attribute = en
            
            if "." in target:
                for p in target.split(".")[1:]:
                    for t in records_global.get(attribute, []):
                        if t.value == p:
                            attribute = t.type
                            break
                            
            formatted_path = target.replace(".", "_")
            formatted.append(f"{formatted_path}/{attribute}")
        return formatted

    
    def aggr_body(self, args):
        return args[0]
        
    def aggr_body_guess(self, args):
        return args[0]

    def _build_aggr_body(self, args, alias_dict, record_set, has_where):
        self.aggregate_check(alias_dict, record_set)
        target_exprs = self._format_aggr_targets(args[0], alias_dict)
        context = args[1] if len(args) > (2 if has_where else 1) else []
        conditions = args[-1] if has_where else []
        
        aggr_record_names = []
        for c in context:
            if isinstance(c, tuple):
                record_name, alias = c
                if alias not in getattr(self, 'negated_atoms', []):
                    aggr_record_names.append(record_name)
                    
        self.add_edge(aggr_record_names)
        self.aggr_new_alias = {}
        self.aggr_alias = []
        self.aggregate_records = set()
        
        return {'target': target_exprs, 'from': context, 'where': conditions}

    def aggr_body_1(self, args):
        return self._build_aggr_body(args, self.declared_alias, self.defined_records, True)

    def aggr_body_2(self, args):
        return self._build_aggr_body(args, self.declared_alias, self.defined_records, False)

    def aggr_body_guess_1(self, args):
        return self._build_aggr_body(args, self.guess_alias, self.guess_records, True)

    def aggr_body_guess_2(self, args):
        return self._build_aggr_body(args, self.guess_alias, self.guess_records, False)
    
    def aggr_records(self, args):
        return [arg for arg in args if str(arg) != ","]

    def aggr_records_guess(self, args):
        return [arg for arg in args if str(arg) != ","]
    
    def aggr_where(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]

    def aggr_where_guess(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    def where_aggr_statement(self, args):
        return self.where_stat_check(args)
    
    def where_aggr_guess(self, args):
        return self.guess_where_check_(args)
    
    def aggr_record_guess(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
        rec_name = str(args[0])
        if rec_name not in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
        alias = str(args[1][0]) if len(args) > 1 and isinstance(args[1], list) else str(args[1]) if len(args) > 1 else rec_name
        if len(args) > 1:
            if alias in self.aggr_new_alias or alias in self.current_alias_map:
                raise ValueError(error_messages.alias_defined(alias))
            self.aggr_new_alias[alias] = rec_name
            self.aggr_alias.append(alias)
        else:
            self.aggregate_records.add(rec_name)
        self.attributes[alias] = list(records_global[rec_name])
        return (rec_name, alias)
    
    def aggr_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
        rec_name = str(args[0])
        if rec_name not in records_global.keys():
            raise ValueError(error_messages.undefined_record(rec_name))
        alias = str(args[1][0]) if len(args) > 1 and isinstance(args[1], list) else str(args[1]) if len(args) > 1 else rec_name
        if len(args) > 1:
            if alias in self.aggr_new_alias or alias in self.declared_alias or alias in self.redefined_record:
                raise ValueError(error_messages.alias_defined(alias))
            self.aggr_new_alias[alias] = rec_name
            self.aggr_alias.append(alias)
        else:
            self.aggregate_records.add(rec_name)
        self.attributes[alias] = list(records_global[rec_name])
        return (rec_name, alias)

    def _validate_aggr_target(self, aggr_type, target_raw, local_from, current_alias_map):
        t_str = str(target_raw).rsplit("/", 1)[0] if "/" in str(target_raw) else str(target_raw)
        has_math = any(op in t_str for op in ['+', '-', '*', '/'])
        if aggr_type == "count" and not has_math:
            return 
        tokens = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z0-9_]+)*\b', t_str)
        for token in tokens:
            if token in ["div", "mod", "sum", "max", "min", "count"]:
                continue
            parts = token.split(".")
            alias = parts[0]
            rec_name = next((r_name for r_name, r_alias in local_from if r_alias == alias), None)
            if not rec_name:
                rec_name = current_alias_map.get(alias)
            if len(parts) == 1:
                if rec_name:
                    raise ValueError(f"Semantic error in '{aggr_type}': '{token}' is an entire record. In a mathematical expression, you must specify a numeric field.")
            else:
                if rec_name and rec_name in getattr(self, 'records', {}):
                    current_rec = rec_name
                    attr_type = "any"
                    for i in range(1, len(parts)):
                        attr = parts[i]
                        ad = next((item for item in self.records.get(current_rec, []) if item['name'] == attr), None)
                        if ad:
                            attr_type = ad['type'].strip().lower()
                            if attr_type not in ["int", "string", "true", "any"]:
                                current_rec = next((k for k in self.records.keys() if k.lower() == attr_type), ad['type'])
                        else:
                            attr_type = "any"
                            break 
                    if attr_type not in ["int", "true", "any"]:
                        raise ValueError(f"Semantic error in '{aggr_type}': The expression contains '{token}' which resolves to type '{attr_type}'. Mathematical expressions require numeric fields.")
                    
    def aggr_def(self, args):
        aggr_type = str(args[0]).lower() 
        bodies = [arg for arg in args if isinstance(arg, dict)]
        
        for body in bodies:
            target_list = body.get('target', [])
            if target_list:
                local_from = body.get('from', [])
                self._validate_aggr_target(aggr_type, target_list[0], local_from, getattr(self, 'current_alias_map', {}))
        op = str(args[-2])
        if hasattr(op, 'value'): op = op.value
        target_val_str = str(args[-1])
        if "/" in target_val_str:
            parts = target_val_str.rsplit("/", 1)
            target_val = parts[0]
            target_type = parts[1] if len(parts) > 1 else "any"
            if target_type != "int" and target_type != "any":
                raise ValueError(f"The right side of an aggregate must be an integer, got: {target_type}")
        else:
            target_val = target_val_str
        return {
            'aggr_type': aggr_type, 
            'bodies': bodies, 
            'operator': op, 
            'target_value': target_val
        }
    
    def aggr_def_guess(self, args):
        aggr_type = str(args[0]).lower() 
        bodies = []
        for arg in args:
            if isinstance(arg, dict):
                bodies.append(arg)
            elif hasattr(arg, 'data'): 
                rule_name = str(arg.data)
                if 'aggr_body' in rule_name:
                    children = arg.children
                    target = children[0] if len(children) > 0 else []
                    ctx = children[1] if len(children) > 1 else []
                    conds = children[2] if len(children) > 2 else []
                    bodies.append({
                        'target': target,
                        'from': ctx,
                        'where': conds
                    })
                else:
                    for child in arg.children:
                        if isinstance(child, dict):
                            bodies.append(child)
                        elif hasattr(child, 'data') and 'aggr_body' in str(child.data):
                            c_children = child.children
                            target = c_children[0] if len(c_children) > 0 else []
                            ctx = c_children[1] if len(c_children) > 1 else []
                            conds = c_children[2] if len(c_children) > 2 else []
                            bodies.append({'target': target, 'from': ctx, 'where': conds})
        for body in bodies:
            target_list = body.get('target', [])
            if target_list:
                local_from = body.get('from', [])
                self._validate_aggr_target(aggr_type, target_list[0], local_from, getattr(self, 'current_alias_map', {}))
        op = str(args[-2])
        if hasattr(op, 'value'): op = op.value
        target_val_str = str(args[-1])
        if "/" in target_val_str:
            parts = target_val_str.rsplit("/", 1)
            target_val = parts[0]
            target_type = parts[1] if len(parts) > 1 else "any"
            if target_type != "int" and target_type != "any":
                raise ValueError(f"The right side of an aggregate must be an integer, got: {target_type}")
        else:
            target_val = target_val_str
        return {
            'aggr_type': aggr_type, 
            'bodies': bodies, 
            'operator': op, 
            'target_value': target_val
        }

    def aggregate_record(self, args):
        stat = "".join(str(a) for a in args)
        self.aggregate_records.add(stat)
        return stat
    
    def aggregate_check(self, declared_alias, defined_records):
        for en in self.aggregate_records:
            all_en = ""
            if "." in en:
                all_en = en
                en = en.split(".")[0]
            if not (en in self.aggr_new_alias.keys() or en in self.aggregate_records):
                if not (en in declared_alias.keys() or en in defined_records or en in self.redefined_record.keys()):
                    raise ValueError(error_messages.undefined_record(en))
            if all_en != "":
                if en in self.aggr_new_alias.keys():
                    attribute = self.aggr_new_alias[en]
                elif en in declared_alias.keys():
                    attribute = declared_alias[en]
                elif en in self.redefined_record.keys():
                    attribute = self.redefined_record[en]
                else:
                    attribute = en
                
                temp_array = all_en.split(".")[1:]
                for i in range(len(temp_array)):
                    found = False
                    for t in records_global[attribute]:
                        if t.value == temp_array[i]:
                            attribute = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(f"{attribute} object has no attribute {temp_array[i]}")
                    
    def aggregate_term(self, args):
        if isinstance(args[0], Token) and args[0].type == 'INT':
            if len(args) == 2 and args[0] in ["-", "+"]:
                return f"{args[0]}{args[1]}/int"
            return f"{args[0]}/int"
        return self.value_aggr_define(args)

    def aggregate_term_guess(self, args):
        if isinstance(args[0], Token) and args[0].type == 'INT':
            if len(args) == 2 and args[0] in ["-", "+"]:
                return f"{args[0]}{args[1]}/int"
            return f"{args[0]}/int"
            
        return self.value_aggr_guess(args)
    
    def abs_aggregate_term(self, args):
        return self.abs2(args)

    def abs_term_guess(self, args):
        return self.abs2(args)

    def aggregate_terms(self, args):
        if len(args) == 3 and args[1] == "..":
            start_val = str(args[0]).rsplit("/", 1)[0] if "/" in str(args[0]) else str(args[0])
            end_val = str(args[2]).rsplit("/", 1)[0] if "/" in str(args[2]) else str(args[2])
            return f"{start_val}..{end_val}/int"
        return args[0]

    def aggregate_terms_guess(self, args):
        return self.aggregate_terms(args)
    
    def aggregate_expression(self, args):
        return self.exp_aggr_define(args)

    def aggregate_term_exp(self, args):
        return self.exp_aggr_define(args)

    def aggregate_term_guess_exp(self, args):
        return self.exp_aggr_define(args)
    
    def aggregate(self, args):
        return [arg for arg in args if isinstance(arg, dict)]

    def guess_aggregate(self, args):
        return self.aggregate(args)
    
    def aggregate_from_guess(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    def aggregate_from(self, args):
        return [arg for arg in args if isinstance(arg, tuple)]
    
    def value_aggr_guess(self, args):
        base_name = str(args[0])
        attribute_type = ""
        if base_name in self.aggr_new_alias:
            attribute_type = self.aggr_new_alias[base_name]
        elif base_name in self.guess_alias:
            attribute_type = self.guess_alias[base_name]
        elif base_name in self.guess_records:
            attribute_type = base_name
        else:
            raise ValueError(error_messages.undefined_element(base_name))
            
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    if attribute_type in ["str", "int", "any"]:
                        raise ValueError(error_messages.no_attribute(attribute_type, args[i]))
                    
                    found = False
                    for t in records_global.get(attribute_type, []):
                        if t.value == args[i]:
                            attribute_type = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(error_messages.no_attribute(attribute_type, args[i]))
                else:
                    break
        
        path = "".join(str(a) for a in args)
        return f"{path}/{attribute_type}"

    def value_aggr_define(self, args):
        base_name = str(args[0])
        attribute_type = ""
        if base_name in self.aggr_new_alias:
            attribute_type = self.aggr_new_alias[base_name]
        elif base_name in self.declared_alias:
            attribute_type = self.declared_alias[base_name]
        elif base_name in self.redefined_record:
            attribute_type = self.redefined_record[base_name]
        elif base_name in self.defined_records or base_name in self.defined_record:
            attribute_type = base_name
        else:
            raise ValueError(error_messages.undefined_element(base_name))
            
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    if attribute_type in ["str", "int", "any"]:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                    
                    found = False
                    for t in records_global.get(attribute_type, []):
                        if t.value == args[i]:
                            attribute_type = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                else:
                    break
                    
        path = "".join(str(a) for a in args)
        return f"{path}/{attribute_type}"
    
    def value_aggr_define(self, args):
        base_name = str(args[0])
        attribute_type = ""
        if base_name in self.aggr_new_alias:
            attribute_type = self.aggr_new_alias[base_name]
        elif base_name in self.declared_alias:
            attribute_type = self.declared_alias[base_name]
        elif base_name in getattr(self, 'aggregate_records', []):
            attribute_type = base_name
        elif base_name in self.redefined_record:
            attribute_type = self.redefined_record[base_name]
        elif base_name in self.defined_records or base_name in self.defined_record:
            attribute_type = base_name
        else:
            raise ValueError(error_messages.undefined_element(base_name))
            
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    if attribute_type in ["str", "int", "any"]:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                    
                    found = False
                    for t in records_global.get(attribute_type, []):
                        if t.value == args[i]:
                            attribute_type = t.type
                            found = True
                            break
                    if not found:
                        raise ValueError(f"{attribute_type} object has no attribute {args[i]}")
                else:
                    break
                    
        path = "".join(str(a) for a in args)
        return f"{path}/{attribute_type}"
    
    def show(self, args):
        global list_show
        for i in range(len(args)):
            if args[i] != "," and args[i] != ";":
                
                val = args[i].value if hasattr(args[i], 'value') else str(args[i])
                list_show.append(val)
        return ""

def build_tree(code: str, target: str):
    global number, list_show, asp_block
    with open(os.path.join(os.path.dirname(__file__), "grammar.lark"), "r") as grammar:
        grammar_ = grammar.read()
        base_parser = Lark(grammar_, parser='lalr')
        raw_ast = base_parser.parse(code)
        DeclarationTransformer().transform(raw_ast)
        validator = SDLValidator()
        validator_state = validator.transform(raw_ast) 
        if target == "minizinc":
            
            generator = MinizincGenerator(validator_state, list_show)
            return generator.generate()
        else:
            shared_state = {
                "number": number,
                "list_show": list_show,
                "asp_block": asp_block,
                "records_global": records_global,
                "pyspel_guess_alias": pyspel_guess_alias,
                "guess_alias": guess_alias,
                "guess_records": guess_records,
                "guess": guess,
            }
            
            pyspel_transformer = PyspelTransformer(shared_state)
            result = pyspel_transformer.transform(raw_ast)
            number = shared_state["number"]
            list_show = shared_state["list_show"]
            asp_block = shared_state["asp_block"]
            return result
    
def check_graph():
    global g
    g.scc()

def print_program_pyspel(asp):
    global number
    asp += f"\nprint(problem{number})\n"
    return asp

def execute_pyspel(solver_path, asp):
    global number
    global list_show
    execution_string = asp + f"""
solver = SolverWrapper(solver_path="{solver_path}")
res = solver.solve(problem=problem{number}, timeout=100)
if res.status == Result.HAS_SOLUTION:"""
    if list_show:
        execution_string += """
    num = 0
    for answer in res.answers:
        num += 1
        print("Solution #"+str(num)+": ", end="")"""
        for atom in list_show:
            execution_string += f"""
        result = answer.get_atom_occurrences({atom}())
        result_str = [str(x) for x in result]
        print(" ".join(result_str))"""
    else:
        execution_string += """\n    print("SAT")"""
    execution_string += """
elif res.status == Result.NO_SOLUTION:
    print("UNSAT")
else:
    print("Unknown")
    """
    return execution_string


def main():
    destination_file = "outputMzn.mzn"
    parser = OptionParser(usage="Usage: %prog [options] [input_files]")
    parser.add_option("-f", "--file", dest="destination_file", help="write output to FILE", metavar="FILE")
    parser.add_option("-v", "--verbose", action="store_true", default=False, dest="verbose", help="print parse tree")
    parser.add_option("-e", "--execute", dest="execute", help="execute the generated code")
    parser.add_option("-r", "--disable-recursive-check", dest="recursive", default=False,
                      help="disable recursive checking", action="store_true")
    parser.add_option("-p", "--print-program", dest="print_program", default=False, help="print ASP program",
                      action="store_true")
    parser.add_option("-t", "--target", dest="target", default="pyspel", 
                      help="Target language: 'pyspel' (default) or 'minizinc'")
    (options, args) = parser.parse_args()

    if options.execute is not None and not args:
        args.append(options.execute)
        options.execute = "default"
        
    code = ''.join(fileinput.input(args))
    try:
        global recursive, target
        if options.recursive:
            recursive = True
        target = options.target
        final_code = build_tree(code, options.target)
        if recursive:
            check_graph()
        if options.verbose:
            print(final_code)
        if options.destination_file is not None:
            destination_file = options.destination_file
        else:
            destination_file = "o.py" if options.target == "pyspel" else "outputMzn.mzn"
        if options.target == "pyspel":
            asp = final_code
            if asp_block != "":
                asp += f"""\nproblem{number}.add(\"\"\"{asp_block}\"\"\")"""
            f = open(destination_file, "w")
            if options.print_program and options.execute is None:
                f.write(print_program_pyspel(asp))
                f.close()
                subprocess.run(["python", destination_file])
            elif options.execute is not None:
                if options.print_program:
                    asp = ""
                execution_string = execute_pyspel(str(options.execute), asp)
                f.write(execution_string)
                f.close()
                subprocess.run(["python", destination_file])
            else:
                f.write(asp)
                f.close()

        elif options.target == "minizinc":
            f = open(destination_file, "w")
            f.write(final_code)
            f.close()
            if options.print_program:
                print(f"MiniZinc file in {destination_file}:\n")
                print(final_code)
            if options.execute is not None:
                solver = "Gecode" if options.execute == "default" else options.execute
                subprocess.run(["minizinc", "--solver", solver, destination_file])

    except exceptions.LarkError as e:
        print(f"Parsing error: {e}")
    except Exception as e:
        print(f"Unexpected error: {e}")
        print(traceback.format_exc())

if __name__ == '__main__':
    main()