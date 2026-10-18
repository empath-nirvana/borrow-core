; The loop of bench/sum two ways: addressed as the native target addresses (`inttoptr` of integer
; arithmetic, Backend/Native/Lower.lean, `ptrAt`) and from a pointer base (`getelementptr`).
; `xcrun clang -O2 -S vectorize.ll -o -`: @sum_int stays scalar, @sum_gep is `add.2d` ×4.
define i64 @sum_int(i64 %base, i64 %n) {
entry:
  br label %loop
loop:
  %i = phi i64 [0, %entry], [%i1, %loop]
  %s = phi i64 [0, %entry], [%s1, %loop]
  %off = shl i64 %i, 3
  %a = add i64 %off, %base
  %p = inttoptr i64 %a to ptr
  %v = load i64, ptr %p, align 8
  %s1 = add i64 %v, %s
  %i1 = add nuw nsw i64 %i, 1
  %c = icmp eq i64 %i1, %n
  br i1 %c, label %exit, label %loop
exit:
  ret i64 %s1
}
define i64 @sum_gep(ptr %base, i64 %n) {
entry:
  br label %loop
loop:
  %i = phi i64 [0, %entry], [%i1, %loop]
  %s = phi i64 [0, %entry], [%s1, %loop]
  %p = getelementptr i64, ptr %base, i64 %i
  %v = load i64, ptr %p, align 8
  %s1 = add i64 %v, %s
  %i1 = add nuw nsw i64 %i, 1
  %c = icmp eq i64 %i1, %n
  br i1 %c, label %exit, label %loop
exit:
  ret i64 %s1
}
