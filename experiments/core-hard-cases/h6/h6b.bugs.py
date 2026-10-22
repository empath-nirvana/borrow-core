BUGS = [
 ("SEMANTIC", "state-not-threaded", "  let (calls, n) = attempt_work(calls);\n  let () = note_work(n);\n  (calls, 200 + n)", "  let (c2, n) = attempt_work(calls);\n  let () = note_work(n);\n  (calls, 200 + n)", "the outer handler's state not threaded past the clause (no resource: only a wrong value)"),
]
