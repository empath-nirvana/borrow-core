import Frontend.Syntax
/-!
# Frontend — Constants

The bracket signatures of the constants of syntax-core §8 and §8a and the derived forms of §9,
and the names of the host operations. The parser reads a constant as its keyword and the
arguments its signature lists; the printer writes it back from `Const.toArgs`. The two are
inverse (`Const.ofArgs_toArgs`).
-/

namespace Frontend

open BoCa (Width IntLit HostOp BinOp DivOp UnOp RelOp)

/-- The kind of one bracket argument. -/
inductive ArgKind where
  | ty | life | binder | shape | nat | op
  deriving DecidableEq, Repr

/-- The keywords of constants. -/
inductive CKw where
  | alloc | free | swap | copy | copyBang | forgetImm | forgetMut | forgetUnk | forgetBang
  | withbor1 | withbor2 | withbor3 | withload | withswap
  | foldImm | foldOwn | foldReuse | fixd | unfoldS
  | i32 | i64 | host
  | allocS | freeS | withborSMut | withborSImm | withborF2Mut | withborF2Imm
  deriving DecidableEq, Repr

/-- A constant keyword's spelling. -/
def CKw.str : CKw → String
  | .alloc => "alloc" | .free => "free" | .swap => "swap" | .copy => "copy"
  | .copyBang => "copy_bang" | .forgetImm => "forget_imm" | .forgetMut => "forget_mut"
  | .forgetUnk => "forget_unk" | .forgetBang => "forget_bang"
  | .withbor1 => "withbor1" | .withbor2 => "withbor2" | .withbor3 => "withbor3"
  | .withload => "withload" | .withswap => "withswap"
  | .foldImm => "fold_imm" | .foldOwn => "fold_own" | .foldReuse => "fold_reuse"
  | .fixd => "fixd" | .unfoldS => "unfold_s"
  | .i32 => "i32" | .i64 => "i64" | .host => "host"
  | .allocS => "alloc_s" | .freeS => "free_s"
  | .withborSMut => "withbor_s_mut" | .withborSImm => "withbor_s_imm"
  | .withborF2Mut => "withbor_f2_mut" | .withborF2Imm => "withbor_f2_imm"

def CKw.all : List CKw :=
  [.alloc, .free, .swap, .copy, .copyBang, .forgetImm, .forgetMut, .forgetUnk, .forgetBang,
   .withbor1, .withbor2, .withbor3, .withload, .withswap,
   .foldImm, .foldOwn, .foldReuse, .fixd, .unfoldS, .i32, .i64, .host,
   .allocS, .freeS, .withborSMut, .withborSImm, .withborF2Mut, .withborF2Imm]

def CKw.ofString? (s : String) : Option CKw := CKw.all.find? (·.str == s)

open ArgKind in
/-- The kinds of a constant's bracket arguments, in order. A constant with none is written
    without brackets. -/
def CKw.sig : CKw → List ArgKind
  | .alloc | .free | .copyBang | .forgetBang => [ty]
  | .swap | .foldOwn | .foldReuse | .fixd | .unfoldS => [ty, ty]
  | .copy | .forgetImm | .forgetMut => [life, ty]
  | .forgetUnk => []
  | .withbor1 => [binder, ty, ty]
  | .withbor2 => [binder, life, ty, ty]
  | .withbor3 | .withload => [life, binder, ty, ty]
  | .withswap => [life, ty, ty]
  | .foldImm => [ty, binder, life, ty]
  | .i32 | .i64 => [nat]
  | .host => [op]
  | .allocS | .freeS => [shape]
  | .withborSMut | .withborSImm => [shape, binder, ty]
  | .withborF2Mut => [binder, binder, binder, life, ty, ty, ty]
  | .withborF2Imm => [binder, binder, binder, ty, ty, ty]

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
  | .i32, [.nat n] => some (.lit (.i32 (UInt32.ofNat n)))
  | .i64, [.nat n] => some (.lit (.i64 (UInt64.ofNat n)))
  | .host, [.op o] => some (.host o)
  | .allocS, [.shape σ] => some (.allocS σ)
  | .freeS, [.shape σ] => some (.freeS σ)
  | .withborSMut, [.shape σ, .binder c, .ty T] => some (.withborS .mut σ c T)
  | .withborSImm, [.shape σ, .binder c, .ty T] => some (.withborS .imm σ c T)
  | .withborF2Mut, [.binder c, .binder a, .binder b, .life w, .ty A, .ty B, .ty T] =>
      some (.withborF2Mut c a b w A B T)
  | .withborF2Imm, [.binder c, .binder a, .binder b, .ty A, .ty B, .ty T] =>
      some (.withborF2Imm c a b A B T)
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
  | .lit (.i32 n) => (.i32, [.nat n.toNat])
  | .lit (.i64 n) => (.i64, [.nat n.toNat])
  | .host o => (.host, [.op o])
  | .allocS σ => (.allocS, [.shape σ])
  | .freeS σ => (.freeS, [.shape σ])
  | .withborS .mut σ c T => (.withborSMut, [.shape σ, .binder c, .ty T])
  | .withborS .imm σ c T => (.withborSImm, [.shape σ, .binder c, .ty T])
  | .withborF2Mut c a b w A B T =>
      (.withborF2Mut, [.binder c, .binder a, .binder b, .life w, .ty A, .ty B, .ty T])
  | .withborF2Imm c a b A B T =>
      (.withborF2Imm, [.binder c, .binder a, .binder b, .ty A, .ty B, .ty T])

theorem Const.ofArgs_toArgs (c : Const) : Const.ofArgs c.toArgs.1 c.toArgs.2 = some c := by
  cases c with
  | lit l => cases l <;> simp [toArgs, ofArgs]
  | withborS m => cases m <;> rfl
  | _ => rfl

theorem CKw.ofString_str (k : CKw) : CKw.ofString? k.str = some k := by
  cases k <;> decide

/-! ### Host operation names

`host[op]` names an operation as its Wasm instruction name with the width as a suffix
(`add32`, `div_s32`, `lt_u64`, `eqz64`, `extend8_s32`), and the four conversions by their bare
names (`wrap`, `extend_s`, `extend_u`, `extend32_s`). -/

def widthSuffix : Width → String
  | .w32 => "32"
  | .w64 => "64"

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

/-- Every host operation. -/
def allHostOps : List HostOp :=
  let ws := [Width.w32, .w64]
  (ws.flatMap fun w =>
    ([.add, .sub, .mul, .and, .or, .xor, .shl, .shr_s, .shr_u, .rotl, .rotr] : List BinOp).map
        (.bin w) ++
      ([.div_s, .div_u, .rem_s, .rem_u] : List DivOp).map (.div w) ++
      ([.clz, .ctz, .popcnt, .extend8_s, .extend16_s] : List UnOp).map (.un w) ++
      [.eqz w] ++
      ([.eq, .ne, .lt_s, .lt_u, .le_s, .le_u, .gt_s, .gt_u, .ge_s, .ge_u] : List RelOp).map
        (.rel w)) ++
  [.wrap, .extend_s, .extend_u, .extend32_s]

def hostOpOfName (s : String) : Option HostOp := allHostOps.find? (hostOpName · == s)

/-- Every host operation is listed, and the names are distinct, so `hostOpOfName` inverts `hostOpName`. -/
theorem hostOpOfName_name (o : HostOp) : hostOpOfName (hostOpName o) = some o := by
  rcases o with ⟨w, o⟩ | ⟨w, o⟩ | ⟨w, o⟩ | w | ⟨w, o⟩ | _ | _ | _ | _ <;>
    (try cases w) <;> (try cases o) <;> decide

end Frontend
