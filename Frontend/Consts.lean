import Frontend.Syntax
/-!
# Frontend — Constants

The bracket signatures of the constants of syntax-core §8 and §8a and the derived forms of §9,
and the names of the host operations. The parser reads a constant as its keyword and the
arguments its signature lists; the printer writes it back from `Const.toArgs`. The two are
inverse (`Const.ofArgs_toArgs`).
-/

namespace Frontend

open BoCa (Width IntLit HostOp BinOp DivOp UnOp RelOp FWidth IWidth Sx FBinOp FUnOp FRelOp)

/-- The kind of one bracket argument. -/
inductive ArgKind where
  | ty | cty | life | binder | shape | nat | op | row
  deriving DecidableEq, Repr

/-- The keywords of constants. -/
inductive CKw where
  | alloc | free | swap | copy | copyBang | forgetImm | forgetMut | forgetUnk | forgetBang
  | withbor1 | withbor2 | withbor3 | withload | withswap
  | foldImm | foldOwn | foldReuse | fixd | unfoldS | unfold
  | i32 | i64 | u8 | f32 | f64 | host
  | allocS | freeS | withborSMut | withborSImm | withborF2Mut | withborF2Imm
  | arrayNew | arrayEmpty | arrayFree | arraySize | arrayReplace | arrayLen | arrayGet | arrayCopy
  | arrayForget | sliceBorrowMut | sliceBorrowImm | sliceGetMut | sliceLenMut
  | sliceSplitImm | sliceSplitMut | sliceEmptyImm | sliceEmptyMut | sliceReplaceMut | sliceSwapMut
  | countFold | countTry | boundedFix
  | withbor1U | withbor2U | withbor3U | withloadU | sliceBorrowMutU | sliceBorrowImmU
  deriving DecidableEq, Repr

/-- A constant keyword's spelling. -/
def CKw.str : CKw → String
  | .alloc => "alloc" | .free => "free" | .swap => "swap" | .copy => "copy"
  | .copyBang => "copy_bang" | .forgetImm => "forget_imm" | .forgetMut => "forget_mut"
  | .forgetUnk => "forget_unk" | .forgetBang => "forget_bang"
  | .withbor1 => "withbor1" | .withbor2 => "withbor2" | .withbor3 => "withbor3"
  | .withload => "withload" | .withswap => "withswap"
  | .foldImm => "fold_imm" | .foldOwn => "fold_own" | .foldReuse => "fold_reuse"
  | .fixd => "fixd" | .unfoldS => "unfold_s" | .unfold => "unfold"
  | .i32 => "i32" | .i64 => "i64" | .u8 => "u8" | .f32 => "f32" | .f64 => "f64"
  | .host => "host"
  | .allocS => "alloc_s" | .freeS => "free_s"
  | .withborSMut => "withbor_s_mut" | .withborSImm => "withbor_s_imm"
  | .withborF2Mut => "withbor_f2_mut" | .withborF2Imm => "withbor_f2_imm"
  | .arrayNew => "array_new" | .arrayEmpty => "array_empty" | .arrayFree => "array_free" | .arraySize => "array_size"
  | .arrayReplace => "array_replace" | .arrayLen => "array_len" | .arrayGet => "array_get"
  | .arrayCopy => "array_copy" | .arrayForget => "array_forget"
  | .sliceBorrowMut => "slice_borrow_mut" | .sliceBorrowImm => "slice_borrow_imm"
  | .sliceGetMut => "slice_get_mut" | .sliceLenMut => "slice_len_mut"
  | .sliceSplitImm => "slice_split_imm" | .sliceSplitMut => "slice_split_mut"
  | .sliceEmptyImm => "slice_empty_imm" | .sliceEmptyMut => "slice_empty_mut"
  | .sliceReplaceMut => "slice_replace_mut" | .sliceSwapMut => "slice_swap_mut"
  | .countFold => "count_fold" | .countTry => "count_try"
  | .boundedFix => "bounded_fix"
  | .withbor1U => "withbor1u" | .withbor2U => "withbor2u" | .withbor3U => "withbor3u"
  | .withloadU => "withloadu" | .sliceBorrowMutU => "slice_borrow_mut_u"
  | .sliceBorrowImmU => "slice_borrow_imm_u"

def CKw.all : List CKw :=
  [.alloc, .free, .swap, .copy, .copyBang, .forgetImm, .forgetMut, .forgetUnk, .forgetBang,
   .withbor1, .withbor2, .withbor3, .withload, .withswap,
   .foldImm, .foldOwn, .foldReuse, .fixd, .unfoldS, .unfold, .i32, .i64, .u8, .f32, .f64, .host,
   .allocS, .freeS, .withborSMut, .withborSImm, .withborF2Mut, .withborF2Imm,
   .arrayNew, .arrayEmpty, .arrayFree, .arraySize, .arrayReplace, .arrayLen, .arrayGet, .arrayCopy,
   .arrayForget, .sliceBorrowMut, .sliceBorrowImm, .sliceGetMut, .sliceLenMut,
   .sliceSplitImm, .sliceSplitMut, .sliceEmptyImm, .sliceEmptyMut, .sliceReplaceMut,
   .sliceSwapMut,
   .countFold, .countTry, .boundedFix,
   .withbor1U, .withbor2U, .withbor3U, .withloadU, .sliceBorrowMutU, .sliceBorrowImmU]

def CKw.ofString? (s : String) : Option CKw := CKw.all.find? (·.str == s)

open ArgKind in
/-- The kinds of a constant's bracket arguments, in order. A constant with none is written
    without brackets. -/
def CKw.sig : CKw → List ArgKind
  | .alloc | .free | .copyBang | .forgetBang => [ty]
  | .arrayNew | .arrayEmpty | .arrayFree | .arraySize | .arrayReplace | .countFold => [ty]
  | .arrayLen | .arrayGet | .arrayCopy | .arrayForget => [life, ty]
  | .sliceGetMut | .sliceLenMut => [life, ty]
  | .sliceSplitImm | .sliceSplitMut | .sliceEmptyImm | .sliceEmptyMut | .sliceReplaceMut
  | .sliceSwapMut => [life, ty]
  | .sliceBorrowMut | .sliceBorrowImm => [binder, life, ty, ty]
  | .swap | .foldOwn | .foldReuse | .fixd | .unfoldS | .countTry => [ty, ty]
  | .unfold => [cty, ty]
  | .boundedFix => [ty, cty]
  | .copy | .forgetImm | .forgetMut => [life, ty]
  | .forgetUnk => []
  | .withbor1 => [binder, ty, ty]
  | .withbor2 => [binder, life, ty, ty]
  | .withbor3 | .withload => [life, binder, ty, ty]
  | .withswap => [life, ty, ty]
  | .foldImm => [ty, binder, life, ty]
  | .i32 | .i64 | .u8 | .f32 | .f64 => [nat]
  | .host => [op]
  | .allocS | .freeS => [shape]
  | .withborSMut | .withborSImm => [shape, binder, ty]
  | .withborF2Mut => [binder, binder, binder, life, ty, ty, ty]
  | .withborF2Imm => [binder, binder, binder, ty, ty, ty]
  | .withbor1U => [binder, ty, ty, row]
  | .withbor2U | .sliceBorrowMutU | .sliceBorrowImmU => [binder, life, ty, ty, row]
  | .withbor3U | .withloadU => [life, binder, ty, ty, row]

/-- A constant from its keyword and arguments; `none` when they do not fit its signature. -/
def Const.ofArgs : CKw → List Arg → Option Const
  | .alloc, [.ty A] => some (.alloc A)
  | .free, [.ty A] => some (.free A)
  | .swap, [.ty A, .ty B] => some (.swap A B)
  | .copy, [.life a, .ty A] => some (.copy a A)
  | .copyBang, [.ty A] => some (.copyBang A)
  | .forgetImm, [.life a, .ty A] => some (.forgetImm a A)
  | .forgetMut, [.life a, .ty A] => some (.forgetMut a A)
  | .forgetUnk, [] => some .forgetUnk
  | .forgetBang, [.ty A] => some (.forgetBang A)
  | .withbor1, [.binder x, .ty A, .ty B] => some (.withbor1 x A B)
  | .withbor2, [.binder x, .life b, .ty A, .ty B] => some (.withbor2 x b A B)
  | .withbor3, [.life a, .binder x, .ty A, .ty B] => some (.withbor3 a x A B)
  | .withload, [.life a, .binder x, .ty A, .ty B] => some (.withload a x A B)
  | .withswap, [.life a, .ty A, .ty B] => some (.withswap a A B)
  | .foldImm, [.ty F, .binder y, .life c, .ty R] => some (.foldImm F y c R)
  | .foldOwn, [.ty F, .ty R] => some (.foldOwn F R)
  | .foldReuse, [.ty F, .ty R] => some (.foldReuse F R)
  | .fixd, [.ty A, .ty S] => some (.fixd A S)
  | .unfoldS, [.ty A, .ty S] => some (.unfoldS A S)
  | .unfold, [.cty C, .ty S] => some (.unfold C S)
  | .i32, [.nat n] => some (.lit (.i32 (UInt32.ofNat n)))
  | .i64, [.nat n] => some (.lit (.i64 (UInt64.ofNat n)))
  | .u8, [.nat n] => some (.lit (.u8 (UInt8.ofNat n)))
  | .f32, [.nat n] => some (.lit (.f32 (UInt32.ofNat n)))
  | .f64, [.nat n] => some (.lit (.f64 (UInt64.ofNat n)))
  | .host, [.op o] => some (.host o)
  | .allocS, [.shape σ] => some (.allocS σ)
  | .freeS, [.shape σ] => some (.freeS σ)
  | .withborSMut, [.shape σ, .binder c, .ty T] => some (.withborS .mut σ c T)
  | .withborSImm, [.shape σ, .binder c, .ty T] => some (.withborS .imm σ c T)
  | .withborF2Mut, [.binder c, .binder a, .binder b, .life w, .ty A, .ty B, .ty T] =>
      some (.withborF2Mut c a b w A B T)
  | .withborF2Imm, [.binder c, .binder a, .binder b, .ty A, .ty B, .ty T] =>
      some (.withborF2Imm c a b A B T)
  | .arrayNew, [.ty A] => some (.arrayNew A)
  | .arrayEmpty, [.ty A] => some (.arrayEmpty A)
  | .arrayFree, [.ty A] => some (.arrayFree A)
  | .arraySize, [.ty A] => some (.arraySize A)
  | .arrayReplace, [.ty A] => some (.arrayReplace A)
  | .arrayLen, [.life a, .ty A] => some (.arrayLen a A)
  | .arrayGet, [.life a, .ty A] => some (.arrayGet a A)
  | .arrayCopy, [.life a, .ty A] => some (.arrayCopy a A)
  | .arrayForget, [.life a, .ty A] => some (.arrayForget a A)
  | .sliceBorrowMut, [.binder x, .life b, .ty A, .ty B] => some (.sliceBorrowMut x b A B)
  | .sliceBorrowImm, [.binder x, .life b, .ty A, .ty B] => some (.sliceBorrowImm x b A B)
  | .sliceGetMut, [.life a, .ty A] => some (.sliceGetMut a A)
  | .sliceLenMut, [.life a, .ty A] => some (.sliceLenMut a A)
  | .sliceSplitImm, [.life a, .ty A] => some (.sliceSplitImm a A)
  | .sliceSplitMut, [.life a, .ty A] => some (.sliceSplitMut a A)
  | .sliceEmptyImm, [.life a, .ty A] => some (.sliceEmptyImm a A)
  | .sliceEmptyMut, [.life a, .ty A] => some (.sliceEmptyMut a A)
  | .sliceReplaceMut, [.life a, .ty A] => some (.sliceReplaceMut a A)
  | .sliceSwapMut, [.life a, .ty A] => some (.sliceSwapMut a A)
  | .countFold, [.ty S] => some (.countFold S)
  | .countTry, [.ty S, .ty E] => some (.countTry S E)
  | .boundedFix, [.ty A, .cty C] => some (.boundedFix A C)
  | .withbor1U, [.binder x, .ty A, .ty B, .row r] => some (.withbor1U x A B r)
  | .withbor2U, [.binder x, .life b, .ty A, .ty B, .row r] => some (.withbor2U x b A B r)
  | .withbor3U, [.life a, .binder x, .ty A, .ty B, .row r] => some (.withbor3U a x A B r)
  | .withloadU, [.life a, .binder x, .ty A, .ty B, .row r] => some (.withloadU a x A B r)
  | .sliceBorrowMutU, [.binder x, .life b, .ty A, .ty B, .row r] =>
      some (.sliceBorrowMutU x b A B r)
  | .sliceBorrowImmU, [.binder x, .life b, .ty A, .ty B, .row r] =>
      some (.sliceBorrowImmU x b A B r)
  | _, _ => none

/-- A constant's keyword and bracket arguments. -/
def Const.toArgs : Const → CKw × List Arg
  | .alloc A => (.alloc, [.ty A])
  | .free A => (.free, [.ty A])
  | .swap A B => (.swap, [.ty A, .ty B])
  | .copy a A => (.copy, [.life a, .ty A])
  | .copyBang A => (.copyBang, [.ty A])
  | .forgetImm a A => (.forgetImm, [.life a, .ty A])
  | .forgetMut a A => (.forgetMut, [.life a, .ty A])
  | .forgetUnk => (.forgetUnk, [])
  | .forgetBang A => (.forgetBang, [.ty A])
  | .withbor1 x A B => (.withbor1, [.binder x, .ty A, .ty B])
  | .withbor2 x b A B => (.withbor2, [.binder x, .life b, .ty A, .ty B])
  | .withbor3 a x A B => (.withbor3, [.life a, .binder x, .ty A, .ty B])
  | .withload a x A B => (.withload, [.life a, .binder x, .ty A, .ty B])
  | .withswap a A B => (.withswap, [.life a, .ty A, .ty B])
  | .foldImm F y c R => (.foldImm, [.ty F, .binder y, .life c, .ty R])
  | .foldOwn F R => (.foldOwn, [.ty F, .ty R])
  | .foldReuse F R => (.foldReuse, [.ty F, .ty R])
  | .fixd A S => (.fixd, [.ty A, .ty S])
  | .unfoldS A S => (.unfoldS, [.ty A, .ty S])
  | .unfold C S => (.unfold, [.cty C, .ty S])
  | .lit (.i32 n) => (.i32, [.nat n.toNat])
  | .lit (.i64 n) => (.i64, [.nat n.toNat])
  | .lit (.u8 n) => (.u8, [.nat n.toNat])
  | .lit (.f32 n) => (.f32, [.nat n.toNat])
  | .lit (.f64 n) => (.f64, [.nat n.toNat])
  | .host o => (.host, [.op o])
  | .allocS σ => (.allocS, [.shape σ])
  | .freeS σ => (.freeS, [.shape σ])
  | .withborS .mut σ c T => (.withborSMut, [.shape σ, .binder c, .ty T])
  | .withborS .imm σ c T => (.withborSImm, [.shape σ, .binder c, .ty T])
  | .withborF2Mut c a b w A B T =>
      (.withborF2Mut, [.binder c, .binder a, .binder b, .life w, .ty A, .ty B, .ty T])
  | .withborF2Imm c a b A B T =>
      (.withborF2Imm, [.binder c, .binder a, .binder b, .ty A, .ty B, .ty T])
  | .arrayNew A => (.arrayNew, [.ty A])
  | .arrayEmpty A => (.arrayEmpty, [.ty A])
  | .arrayFree A => (.arrayFree, [.ty A])
  | .arraySize A => (.arraySize, [.ty A])
  | .arrayReplace A => (.arrayReplace, [.ty A])
  | .arrayLen a A => (.arrayLen, [.life a, .ty A])
  | .arrayGet a A => (.arrayGet, [.life a, .ty A])
  | .arrayCopy a A => (.arrayCopy, [.life a, .ty A])
  | .arrayForget a A => (.arrayForget, [.life a, .ty A])
  | .sliceBorrowMut x b A B => (.sliceBorrowMut, [.binder x, .life b, .ty A, .ty B])
  | .sliceBorrowImm x b A B => (.sliceBorrowImm, [.binder x, .life b, .ty A, .ty B])
  | .sliceGetMut a A => (.sliceGetMut, [.life a, .ty A])
  | .sliceLenMut a A => (.sliceLenMut, [.life a, .ty A])
  | .sliceSplitImm a A => (.sliceSplitImm, [.life a, .ty A])
  | .sliceSplitMut a A => (.sliceSplitMut, [.life a, .ty A])
  | .sliceEmptyImm a A => (.sliceEmptyImm, [.life a, .ty A])
  | .sliceEmptyMut a A => (.sliceEmptyMut, [.life a, .ty A])
  | .sliceReplaceMut a A => (.sliceReplaceMut, [.life a, .ty A])
  | .sliceSwapMut a A => (.sliceSwapMut, [.life a, .ty A])
  | .countFold S => (.countFold, [.ty S])
  | .countTry S E => (.countTry, [.ty S, .ty E])
  | .boundedFix A C => (.boundedFix, [.ty A, .cty C])
  | .withbor1U x A B r => (.withbor1U, [.binder x, .ty A, .ty B, .row r])
  | .withbor2U x b A B r => (.withbor2U, [.binder x, .life b, .ty A, .ty B, .row r])
  | .withbor3U a x A B r => (.withbor3U, [.life a, .binder x, .ty A, .ty B, .row r])
  | .withloadU a x A B r => (.withloadU, [.life a, .binder x, .ty A, .ty B, .row r])
  | .sliceBorrowMutU x b A B r => (.sliceBorrowMutU, [.binder x, .life b, .ty A, .ty B, .row r])
  | .sliceBorrowImmU x b A B r => (.sliceBorrowImmU, [.binder x, .life b, .ty A, .ty B, .row r])

theorem Const.ofArgs_toArgs (c : Const) : Const.ofArgs c.toArgs.1 c.toArgs.2 = some c := by
  cases c with
  | lit l => cases l with
    | i32 n => show some (Const.lit (.i32 (UInt32.ofNat n.toNat))) = _; simp
    | i64 n => show some (Const.lit (.i64 (UInt64.ofNat n.toNat))) = _; simp
    | u8 n => show some (Const.lit (.u8 (UInt8.ofNat n.toNat))) = _; simp
    | f32 n => show some (Const.lit (.f32 (UInt32.ofNat n.toNat))) = _; simp
    | f64 n => show some (Const.lit (.f64 (UInt64.ofNat n.toNat))) = _; simp
  | withborS m => cases m <;> rfl
  | _ => rfl

theorem CKw.ofString_str (k : CKw) : CKw.ofString? k.str = some k := by
  cases k <;> decide

/-! ### Host operation names

`host[op]` names an operation as its Wasm instruction name with the width as a suffix
(`add32`, `div_s32`, `lt_u64`, `eqz64`, `extend8_s32`), and the conversions by their bare
names (`wrap`, `extend_s`, `extend_u`, `extend32_s`, and the byte's `wrap8`, `extend8_u`). The
grouped names at `8` (`add8`, …) exist and take `0`: a byte has no arithmetic (SPEC §8), and so
do those at the float widths (`addf32`, …). The float operations are named as Wasm's instructions
with `_` for `.` (`f64_add`, `f32_sqrt`, `f64_lt`, `f64_convert_i32_s`, `i32_trunc_f64_s`,
`i64_trunc_sat_f32_u`, `f32_demote_f64`, `f64_promote_f32`, `i64_reinterpret_f64`,
`f32_reinterpret_i32`; SPEC §37). -/

def widthSuffix : Width → String
  | .w32 => "32"
  | .w64 => "64"
  | .w8 => "8"
  | .f32 => "f32"
  | .f64 => "f64"

def fwName : FWidth → String
  | .f32 => "f32"
  | .f64 => "f64"

def iwName : IWidth → String
  | .i32 => "i32"
  | .i64 => "i64"

def sxName : Sx → String
  | .s => "s"
  | .u => "u"

def fbinName : FBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .min => "min"
  | .max => "max" | .copysign => "copysign"

def funName : FUnOp → String
  | .abs => "abs" | .neg => "neg" | .sqrt => "sqrt" | .ceil => "ceil" | .floor => "floor"
  | .trunc => "trunc" | .nearest => "nearest"

def frelName : FRelOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .gt => "gt" | .le => "le" | .ge => "ge"

def binOpName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shr_s => "shr_s" | .shr_u => "shr_u"
  | .rotl => "rotl" | .rotr => "rotr"

def divOpName : DivOp → String
  | .div_s => "div_s" | .div_u => "div_u" | .rem_s => "rem_s" | .rem_u => "rem_u"

def unOpName : UnOp → String
  | .clz => "clz" | .ctz => "ctz" | .popcnt => "popcnt" | .extend8_s => "extend8_s"
  | .extend16_s => "extend16_s"

def relOpName : RelOp → String
  | .eq => "eq" | .ne => "ne" | .lt_s => "lt_s" | .lt_u => "lt_u" | .le_s => "le_s"
  | .le_u => "le_u" | .gt_s => "gt_s" | .gt_u => "gt_u" | .ge_s => "ge_s" | .ge_u => "ge_u"

def hostOpName : HostOp → String
  | .bin w o => binOpName o ++ widthSuffix w
  | .div w o => divOpName o ++ widthSuffix w
  | .un w o => unOpName o ++ widthSuffix w
  | .eqz w => "eqz" ++ widthSuffix w
  | .rel w o => relOpName o ++ widthSuffix w
  | .wrap => "wrap"
  | .extend_s => "extend_s"
  | .extend_u => "extend_u"
  | .extend32_s => "extend32_s"
  | .wrap8 => "wrap8"
  | .extend8_u => "extend8_u"
  | .fbin f o => fwName f ++ "_" ++ fbinName o
  | .fun1 f o => fwName f ++ "_" ++ funName o
  | .frel f o => fwName f ++ "_" ++ frelName o
  | .convert f i sx => fwName f ++ "_convert_" ++ iwName i ++ "_" ++ sxName sx
  | .trunc i f sx => iwName i ++ "_trunc_" ++ fwName f ++ "_" ++ sxName sx
  | .trunc_sat i f sx => iwName i ++ "_trunc_sat_" ++ fwName f ++ "_" ++ sxName sx
  | .demote => "f32_demote_f64"
  | .promote => "f64_promote_f32"
  | .reinterpret_i f => iwName f.int ++ "_reinterpret_" ++ fwName f
  | .reinterpret_f f => fwName f ++ "_reinterpret_" ++ iwName f.int

/-- Every host operation. -/
def allHostOps : List HostOp :=
  let ws := [Width.w32, .w64, .w8, .f32, .f64]
  let fs := [FWidth.f32, .f64]
  let is := [IWidth.i32, .i64]
  let sxs := [Sx.s, .u]
  (ws.flatMap fun w =>
    ([.add, .sub, .mul, .and, .or, .xor, .shl, .shr_s, .shr_u, .rotl, .rotr] : List BinOp).map
        (.bin w) ++
      ([.div_s, .div_u, .rem_s, .rem_u] : List DivOp).map (.div w) ++
      ([.clz, .ctz, .popcnt, .extend8_s, .extend16_s] : List UnOp).map (.un w) ++
      [.eqz w] ++
      ([.eq, .ne, .lt_s, .lt_u, .le_s, .le_u, .gt_s, .gt_u, .ge_s, .ge_u] : List RelOp).map
        (.rel w)) ++
  [.wrap, .extend_s, .extend_u, .extend32_s, .wrap8, .extend8_u, .demote, .promote] ++
  (fs.flatMap fun f =>
    ([.add, .sub, .mul, .div, .min, .max, .copysign] : List FBinOp).map (.fbin f) ++
      ([.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest] : List FUnOp).map (.fun1 f) ++
      ([.eq, .ne, .lt, .gt, .le, .ge] : List FRelOp).map (.frel f) ++
      [.reinterpret_i f, .reinterpret_f f] ++
      (is.flatMap fun i => sxs.flatMap fun sx =>
        [.convert f i sx, .trunc i f sx, .trunc_sat i f sx]))

def hostOpOfName (s : String) : Option HostOp := allHostOps.find? (hostOpName · == s)

/-- Every host operation is listed, and the names are distinct, so `hostOpOfName` inverts `hostOpName`. -/
theorem hostOpOfName_name (o : HostOp) : hostOpOfName (hostOpName o) = some o := by
  rcases o with ⟨w, o⟩ | ⟨w, o⟩ | ⟨w, o⟩ | w | ⟨w, o⟩ | _ | _ | _ | _ | _ | _ | ⟨f, o⟩ |
      ⟨f, o⟩ | ⟨f, o⟩ | ⟨f, i, sx⟩ | ⟨i, f, sx⟩ | ⟨i, f, sx⟩ | _ | _ | f | f <;>
    (try cases w) <;> (try cases f) <;> (try cases i) <;> (try cases sx) <;> (try cases o) <;>
    decide

end Frontend
