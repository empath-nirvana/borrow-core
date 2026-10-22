BUGS = [
 ("MEMORY", "double-free", "w <- return (free[i32] c);", "w <- return (free[i32] c);\n  w2 <- return (free[i32] c);", "the owner's finaliser run twice"),
 ("MEMORY", "write-after-lend", "let () = forget_mut['x, i32] m;\n          return boxed['x] (inl x : i32 + i32)",
  "let () = forget_mut['x, i32] m;\n          q2 <- return (withswap['x, i32, 1] m (thunkv fun (v : i32) -> return (i32[98], ())));\n          let (m2, z2) = q2;\n          return boxed['x] (inl x : i32 + i32)", "a write through the borrow after the borrower's finaliser ended it"),
 ("MEMORY", "borrow-escapes", "r <- return withbor2['x, top, i32, i32 + i32] c", "r <- return withbor2['x, top, i32, mut 'x i32] c", "the borrow returned out of its lend (answer type mentions 'x)"),
 ("MEMORY", "borrow-escapes-boxed", "let () = forget_mut['x, i32] m;\n          return boxed['x] (inl x : i32 + i32)", "return boxed['x] m", "the borrow answered from the lend: B = mut 'x i32"),
 ("MEMORY", "owner-used-in-lend", "let () = forget_mut['x, i32] m;\n          return boxed['x] (inl x : i32 + i32)", "let () = forget_mut['x, i32] m;\n          w0 <- return (free[i32] c);\n          return boxed['x] (inl x : i32 + i32)", "the owner freed while it is lent (inside the callback)"),
 ("MEMORY", "free-skipped", "w <- return (free[i32] c);\n  return s", "return s", "the owner's finaliser skipped on the only path (the checker's implicit destructor, SPEC 12, frees c)"),
 ("MEMORY", "owner-dup", "let (c, s) = r;", "let (c, s) = r;\n  w9 <- return (free[i32] c);", "the owner freed, then freed again by the original free (affine resource used twice)"),
 ("SEMANTIC", "write-skipped", "q <- return (withswap['x, i32, 1] m (thunkv fun (v : i32) -> return (i32[99], ())));\n          let (m, z) = q;\n          let () = z;\n", "", "the borrower's write of 99 skipped: observable output only"),
 ("SEMANTIC", "wrong-summand", "return boxed['x] (inl x : i32 + i32)", "return boxed['x] (inr x : i32 + i32)", "the wrong summand answered"),
]
BUGS += [
 ("MEMORY", "finaliser-thunk-dropped", "w <- return (free[i32] c);\n  return s", "fin : U (F i32) <- return (thunk free[i32] c);\n  return s", "the owner's finaliser packaged as a linear thunk (class 3, no destructor) and never run"),
 ("MEMORY", "linear-free-skipped", "let (c, s) = r;\n  w <- return (free[i32] c);", "let (c0, s) = r;\n  linear c : ref i32 <- return c0;\n", "the owner bound `linear` (opted out of implicit destructors) and its free skipped"),
]
