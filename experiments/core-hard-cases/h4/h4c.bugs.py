src = open(__file__.replace("h4c.bugs.py", "h4c-borrowing-bodies.bc")).read()
BUGS = [
 ("MEMORY", "free-while-lent", "          let () = forget_imm['d, 1] ud;\n", "          let () = forget_imm['d, 1] ud;\n          x9 <- return (free[i32] c1);\n", "the lent cell c1 freed while the tasks hold its borrow"),
 ("MEMORY", "task-escapes-queue-scope", "          let (uc, w3) = r3;", "          let (uc, w3) = r3;\n          s9 : imm 'b i32 <- return v2;", "the counter's borrow used after the queue's scope handed it to the task (v2 used twice)"),
 ("SEMANTIC", "reader-sum-wrong", "return boxed['d] plus (i32[10], y)", "return boxed['d] plus (i32[11], y)", "a wrong value"),
]
