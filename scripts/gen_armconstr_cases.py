# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

# Helper script to generate theorems for the experimental method to
# aggregate state effects using reflection.

import random

global val_count

def generate_nested_writes(depth, start_reg, state):
    global val_count
    
    if depth == 0:
        return state, ""
    
    reg = start_reg
    inner_write, inner_expr = generate_nested_writes(depth - 1, start_reg + 1, state)

    h_step =  f"(w (.GPR {reg}#5) val{val_count} {inner_write})"
    expr   = f"w_gpr {reg}#5 (.var {val_count}), {inner_expr}"

    val_count = val_count + 1    
    
    return h_step, expr

def generate_expression(n):
    depth = random.randint(1, 5)
    start_reg = random.randint(1, 32 - depth)  # 32 registers
    nested_writes, writes = generate_nested_writes(depth, start_reg, f"s{n-1}")

    h_step = f"(h_step_{n} : s{n} = {nested_writes})"
    exprs = f"{{ curr_state := {n}, prev_state := {n-1}, writes := [{writes}] }}"
    
    return h_step, exprs

def generate_theorem_statement(nsteps):
    global val_count
    ans = [generate_expression(i) for i in range(1, nsteps+1)]
    step_hyps = ""
    refl_exprs = ""
    
    for h_step, expr in ans:
        step_hyps = f"{step_hyps}  {h_step}\n"
        refl_exprs = f"{refl_exprs}  {expr},\n"

    state_vars = "[" + ", ".join(["s" + str(suffix) for suffix in list(range(0, nsteps+1))]) + "]"
    gpr_vars = "[" + ", ".join(["val" + str(suffix) for suffix in list(range(0, val_count))]) + "]"
    h_step_vars = " ".join(["h_step_" + str(suffix) for suffix in list(range(1, nsteps+1))]) + "]"
    
    return f"open Expr Update in \
             \ntheorem test_{nsteps}_steps (s0 : ArmState)\n{step_hyps}  :\
             \n  s{nsteps} = <xxxx> := by\
             \n    have := (Expr.eq_true_of_denote \
             \n            -- Context \
             \n            {{ state := {state_vars}, \
             \n               gpr := {gpr_vars} }} \
             \n            -- init \
             \n            {{ curr_state := 0, prev_state := 0, writes := [] }} \
             \n            -- final: run `Exprs.aggregate init updates` to get the following. \
             \n            <xxxx_reflected> \
             \n            -- updates \
             \n            [{refl_exprs}] \
             \n            (by native_decide)) \
             \n    simp only [Exprs.denote, and_true, and_imp] at this \
             \n    exact this (Eq.refl s0) {h_step_vars} \
             \n    done"


# # Generate 30 expressions
# val_count = 0
# ans = [generate_expression(i) for i in range(1, 31)]
# 
# # Print the h_steps
# for h_step, _ in ans:
#     print(h_step)
# 
# # Print the exprs
# for _, expr in ans:
#     print(expr)    
#     

val_count = 0
print (generate_theorem_statement(40)) 
