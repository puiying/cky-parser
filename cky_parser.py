import sys
import re
import copy
import itertools
from nltk.tree import *


# define function that takes in grammar file name, read the file, and return a dictionary of grammar rules
def read_grammar_file(filename):
    # read grammar file
    lines = []
    with open(filename) as f:
        lines = f.readlines()
    lines = [re.sub('\\n', '', l) for l in lines if not re.match('^#', l)]

    # create a dictionary of grammar rules with LHS as key and RHS as value
    grammar = {}
    for l in lines:
        # get left hand side of the rule
        lhs = l.split('->')[0].strip()
        # get right hand side of the rule
        rhs = l.split('->')[1].strip()
        # if LHS already existed, append the rule list
        if lhs in grammar.keys():
            grammar[lhs].append(rhs)
        # if not existed, add rule as a list
        else:
            grammar[lhs] = [rhs]

    return grammar


# define function that takes in a grammar dictionary and convert to Chowsky Normal Form rules in a dictionary
def convert_to_cnf(grammar_dict):
    # placeholder for cnf rules
    cnf = grammar_dict.copy()
    # keep a counter for new rules
    counter = 0
    # get any first cnf violation key (lhs)
    violation_key = cnf_violation(cnf)
    # repeat until we achieve cnf form
    while violation_key is not None:
        # get the cnf violation items
        lhs = violation_key
        rhs = cnf[violation_key]
        for i in rhs:
            symbols = i.split(' ')
            num_symbols = len(symbols)

            # apply rule 2: all terminal symbols should be replaced by non-terminals if more than 1
            if num_symbols > 1:
                for j in range(num_symbols):
                    # check if any first character is lowercase
                    if symbols[j][0].islower():
                        to_be_replaced = symbols[j]
                        # check if rule already exists for terminals (assume only one key is returned)
                        replaced_key = get_key(cnf, to_be_replaced)
                        # if not add new rule
                        if len(replaced_key) == 0:
                            cnf[f'X{counter}'] = [to_be_replaced]
                            replaced_key = [f'X{counter}']
                            counter += 1
                        # replace the symbols in original rule (assume only one key is returned)
                        symbols[j] = replaced_key[0]
                        cnf = replace_values(grammar_dict=cnf, to_be_replaced=i, replaced_with=" ".join(symbols))

            # apply rule 4: if more than 2 symbols, replace left to right
            if num_symbols > 2:
                to_be_replaced = " ".join(symbols[:-1])
                # check if the rule already exist for the first 2 symbols
                replaced_key = get_key(cnf, to_be_replaced)
                # if not add new rule
                if len(replaced_key) == 0:
                    cnf[f'X{counter}'] = [to_be_replaced]
                    replaced_key = [f'X{counter}']
                    counter += 1
                # replace with existing rule (assume only one key is returned)
                cnf = replace_values(grammar_dict=cnf, to_be_replaced=i,
                                     replaced_with=replaced_key[0] + ' ' + symbols[-1])
        # check if there is any violation of cnf for while loop
        violation_key = cnf_violation(cnf)
    return cnf


# create function that takes in grammar dictionary and lookup RHS to find LHS, return a list of keys
def get_key(grammar_dict, lookup_val):
    # placeholder for key
    key = []
    for lhs, rhs in grammar_dict.items():
        for i in rhs:
            if i == lookup_val:
                key.append(lhs)
    return key


# create function to replace the rhs of rules in a grammar dictionary and return the full grammar dictionary
def replace_values(grammar_dict, to_be_replaced, replaced_with):
    for lhs, rhs in grammar_dict.items():
        for i in range(len(rhs)):
            if rhs[i] == to_be_replaced:
                rhs[i] = replaced_with
    return grammar_dict


# create function to check if cnf rules are satisfied except unit production rule, input as dictionary and return violation key
def cnf_violation(grammar_dict):
    violation_key = None
    for lhs, rhs in grammar_dict.items():
        for i in rhs:
            symbols = i.split(' ')
            num_symbols = len(symbols)
            # check if more than two symbols then no
            if num_symbols > 2:
                violation_key = lhs
                break
            # check if 2 symbols but one of them is terminal then no
            elif num_symbols == 2 and (symbols[0][0].islower() or symbols[1][0].islower()):
                violation_key = lhs
                break
    return violation_key


# create function that break sentence into items in list and add start symbol
def sentence_processor(sentence):
    sentence = ('<s> ' + sentence).split(' ')
    return sentence


# create function to perform cky parser given sentence and grammar dictionary
def cky_parser(sent_list, grammar_dict):
    # placeholder for cky_table and back pointer
    cky_table = {}
    back_pointer = {}
    for j in range(1, len(sent_list)):
        cky_table[j - 1] = {}
        cky_table[j - 1][j] = {}
        back_pointer[j - 1] = {}
        back_pointer[j - 1][j] = {}
        # get all non-terminals to terminals: A -> terminal symbols
        cky_table[j - 1][j] = add_rules_recursively(grammar_dict=grammar_dict, lookup=sent_list[j],
                                                    rules_dict=cky_table[j - 1][j])
        # keep track of location for tracing purposes
        back_pointer[j - 1][j][sent_list[j]] = j
        for lhs, rhs in cky_table[j - 1][j].items():
            for val in rhs:
                if val[0].isupper():
                    back_pointer[j - 1][j][val] = (j - 1, j)

        # moving up to non-terminals to non-terminals
        for i in range(j - 2, -1, -1):
            cky_table[i][j] = {}
            back_pointer[i][j] = {}
            for k in range(i + 1, j):
                # define B and C in A->BC
                B = list(cky_table[i][k].keys())
                C = list(cky_table[k][j].keys())
                # look for all combination of BC
                for r in itertools.product(B, C):
                    BC = r[0] + ' ' + r[1]
                    if len(get_key(grammar_dict, BC)) > 0:
                        # keep track of all the location of B, C to trace back later
                        back_pointer[i][j][r[0]] = (i, k)
                        back_pointer[i][j][r[1]] = (k, j)
                    # check if A->BC grammar rule exists, if yes, append rule
                    cky_table[i][j] = add_rules_recursively(grammar_dict=grammar_dict, lookup=BC,
                                                            rules_dict=cky_table[i][j])
    # add back pointer for the "end-goal" cell
    lhs = list(cky_table[0][len(sent_list)-1].keys())
    rhs = [j for i in cky_table[0][len(sent_list)-1].values() for j in i]
    point_lhs = list(back_pointer[0][len(sent_list)-1].keys())
    # if end point is a unit production, there is no back pointer, add back pointer back to end-goal cell
    for r in set(rhs).intersection(set(lhs))-set(point_lhs):
        back_pointer[0][len(sent_list)-1][r] = (0, len(sent_list)-1)

    return cky_table, back_pointer


# create function that update current rule dictionary to loop up keys (lhs) and unit production rules in grammar dictionary
def add_rules_recursively(grammar_dict, lookup, rules_dict):
    lhs = get_key(grammar_dict, lookup)
    rhs = [lookup] * len(lhs)
    while len(lhs) > 0:
        # placeholder to look for all unit production rules
        lhs_next = []
        rhs_next = []
        for key, val in zip(lhs, rhs):
            # append rules that match the lookup value
            if key in rules_dict.keys() and val not in rules_dict[key]:
                rules_dict[key].extend([val])
            elif key not in rules_dict.keys():
                rules_dict[key] = [val]
            # add #3 unit production rules recursively
            unit_rules = get_key(grammar_dict, key)
            lhs_next.extend(unit_rules)
            rhs_next.extend([key] * len(unit_rules))
        # redirect to look for all unit production rules
        lhs = lhs_next
        rhs = rhs_next
    return rules_dict


# build tree based on cky table
def build_tree(cky_table, back_pointer, tree, tree_index_string, lookup_val, index, dup_count):
    # get first and second indices
    i, j = index
    # loop through the lhs and rhs of the cky parser
    for parents, children in cky_table[i][j].items():
        # if lhs is the lookup value
        if parents == lookup_val:
            # loop through the possible rhs
            for c_count in range(len(children)):
                # if multiple tree exists
                if c_count > 0:
                    # for each tree that currently exists in the list, we need a copy
                    for t_count in range(len(tree)):
                        dup_count += 1
                        # make a copy
                        diverge_copy = [copy.deepcopy(tree[t_count])]
                        exec(f"diverge_copy{tree_index_string} = dict()")
                        # add to tree dictionary list
                        tree.extend(diverge_copy)
                        # change the index of dictionary
                        tree_index_string = re.sub("\[[0-9]\]", f"[{dup_count}]", tree_index_string)
                # get all symbols for each rhs items
                c_list = children[c_count].split(' ')
                for c in c_list:
                    # if the symbol is not terminal
                    if (c[0].isupper() and len(back_pointer[i][j][c]) == 2):
                        val_c = c
                        index_c = back_pointer[i][j][c]
                        # if unit production rule happened at end-goal cell, refer back to itself
                        if lookup_val == 'S' and len(c_list) == 1:
                            index_c = (i, j)
                        tree_index_c = f"{tree_index_string}['{c}']"
                        c_counter = dup_count
                        # create a branch for each symbol
                        exec(f"tree{tree_index_c} = dict()")
                        # regenerate branches of tree
                        tree = build_tree(cky_table, back_pointer, tree=tree, tree_index_string=tree_index_c,
                                          lookup_val=val_c, index=index_c, dup_count=c_counter)
                    # if the symbol is terminal
                    else:
                        exec(f"tree{tree_index_string} = c")
    return tree


# create function that takes in the dictionary of tree then print out tree and output nltk tree class
def print_tree(tree):
    # generate tree from dictionary -> string
    t = Tree.fromstring(str(tree).replace("\'", "").replace(":", "").replace(", ", "} {"), brackets="{}")
    # print out tree
    t.pretty_print()
    return t


def main():
    # collect user input
    grammar_file = sys.argv[1]
    sentence = sys.argv[2]
    # grammar_file = '/Users/py/Documents/GitHub/homework7/l1.cfg'
    # sentence = 'i prefer book'

    print('Input sentence is:', sentence)
    # make sentence to list and add 's'
    sent_list = sentence_processor(sentence.lower())

    # read grammar rules as text files
    g = read_grammar_file(grammar_file)
    # convert grammar rules to chowsky normal form except unit production rule
    g = convert_to_cnf(g)
    # perform cky parsing to build tree
    cky_table, back_pointer = cky_parser(sent_list, g)

    # if tree is not found, print error
    if 'S' not in cky_table[0][len(sent_list) - 1]:
        print('The given sentence is not derivable.')

    else:
        # build tree using cky parser
        tree = build_tree(cky_table, back_pointer, tree=[{'S': {}}], tree_index_string="[0]['S']", lookup_val='S',
                          index=(0, len(sent_list) - 1), dup_count=0)

        t = []
        num_tree = len(tree)
        print(f'The given sentence is derivable. A total of {num_tree} tree(s) is(are) found.')
        # print tree
        for i in range(len(tree)):
            print(f'\nParsing Tree {i + 1}\n{"-"*15}')
            t.append(print_tree(tree[i]))
            print(t[i])


if __name__ == '__main__':
    main()
