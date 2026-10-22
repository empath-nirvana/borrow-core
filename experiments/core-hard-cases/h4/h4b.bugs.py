BUGS = [
 ("MEMORY", "cancel-twice", "inl v -> x <- return (unbang cancel_t) b; return (inl (inl v : RR) : RR + 1)", "inl v -> x <- return (unbang cancel_t) b; x2 <- return (unbang cancel_t) b; return (inl (inl v : RR) : RR + 1)", "the losing task cancelled twice"),
 ("MEMORY", "loser-dropped", "inl v -> x <- return (unbang cancel_t) b; return (inl (inl v : RR) : RR + 1)", "inl v -> return (inl (inl v : RR) : RR + 1)", "the losing task neither cancelled nor resumed (the implicit destructor cancels it)"),
 ("MEMORY", "loser-dropped-linear", ["      let (b, turns) = q;\n", "inl v -> x <- return (unbang cancel_t) b; return (inl (inl v : RR) : RR + 1)"], ["      let (b0, turns) = q;\n        linear b : TV <- return b0;\n", "inl v -> return (inl (inl v : RR) : RR + 1)"], "the losing task bound `linear`, then neither cancelled nor resumed"),
 ("MEMORY", "close-keeps-buf-linear", "inl ls -> let (buf, left) = ls; w <- return (free[i32] buf); return ()", "inl ls -> let (buf0, left) = ls; linear buf : ref i32 <- return buf0; return ()", "lookup's cancel does not free its buffer (bound `linear`)"),
 ("MEMORY", "close-keeps-buf", "inl ls -> let (buf, left) = ls; w <- return (free[i32] buf); return ()", "inl ls -> let (buf, left) = ls; return ()", "lookup's cancel does not free its buffer (the implicit destructor frees it)"),
 ("MEMORY", "use-after-free", "      | inr lt -> return (inr (inl (buf, minus (left, i32[1])) : St) : i32 + St)", "      | inr lt -> w <- return (free[i32] buf); return (inr (inl (buf, minus (left, i32[1])) : St) : i32 + St)", "the buffer freed, then kept in the next state"),
 ("MEMORY", "task-duplicated", "  ab <- return (a, (b, i32[10]));", "  ab <- return (a, (a, i32[10]));", "one task raced against itself (an affine task used twice)"),
 ("SEMANTIC", "wrong-winner", "inl w -> x <- return (unbang cancel_t) a2; return (inl (inr (inl w : i32 + 1) : RR) : RR + 1)", "inl w -> x <- return (unbang cancel_t) a2; return (inl (inl w : RR) : RR + 1)", "b's win reported as a's"),
]

