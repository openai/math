import OAI.ThreeFlat.Diagonal.CompressorNativePlacement

namespace OAI
/-! # Word-addressed parent maps and ordered child arrays

Site ordinals use the order base, tag, remaining lane. After the site
ordinal come the color-bit word and slot label of an old position.
All radices are public words. Integer fit is needed only at the outer
packed address; every proper prefix is automatically smaller.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr
open scoped Fin.NatCast
variable {A : Type*} {w k n : ℕ}

structure Radices (A : Type*) where
  tags : A
  lanes : A
  colors : A
  slots : A

def Radices.map {B : Type*} (f : A → B) (r : Radices A) : Radices B :=
  ⟨f r.tags,f r.lanes,f r.colors,f r.slots⟩

def appendDigit (o : Ops A) (v radix digit : A) : A := o.bin .add (o.bin .mul v radix) digit

def packSite (o : Ops A) (r : Radices A) (s : Site A) : A :=
  appendDigit o (appendDigit o s.base r.tags s.tag) r.lanes s.lane

def packPosition (o : Ops A) (r : Radices A) (x : Position A) : A :=
  appendDigit o (appendDigit o (packSite o r x.site) r.colors x.bits) r.slots x.slot

def unpackSite (o : Ops A) (r : Radices A) (z : A) : Site A :=
  let q := o.bin .div z r.lanes
  ⟨o.bin .div q r.tags,o.bin .mod q r.tags,o.bin .mod z r.lanes⟩

def unpackPosition (o : Ops A) (r : Radices A) (z : A) : Position A :=
  let q := o.bin .div z r.slots
  ⟨unpackSite o r (o.bin .div q r.colors),o.bin .mod q r.colors,o.bin .mod z r.slots⟩

/-- A parent map stores one word at each consecutive old position. The native
driver supplies its current absolute write address. -/
def parentRow (r : Radices (Term w k 1)) (g : Columns (Term w k 1)) (d : ℕ) (layout : Bool)
    (output : Term w k 1) : Term w k 1 :=
  let o := terms w k 1
  let z := o.bin .sub (.result 0) output
  packSite o r (owner o g d layout (unpackPosition o r z))

/-- Four words per old site form an ordinary join source record. The first
word resolves to the new owner's group word and the remaining words are
zero. The write cursor addresses that four-word array. -/
def groupSourceRow (r : Radices (Term w k 1)) (g : Columns (Term w k 1)) (d : ℕ) (layout : Bool)
    (output : Term w k 1) : Term w k 1 :=
  let o := terms w k 1
  let q := o.bin .sub (.result 0) output
  let z := o.bin .div q (o.lit 4)
  let site := packSite o r (owner o g d layout (unpackPosition o r z))
  o.choose (o.bin .mod q (o.lit 4)) (o.lit 0)
    (o.bin .add (o.lit 2) (o.bin .mul (o.lit 4) site)) (o.lit 0)

theorem eval_packSite (r : Radices (Term w k n)) (s : Site (Term w k n))
    (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) :
    ev pub m vs (packSite (terms w k n) r s) =
      packSite (words m) (r.map (ev pub m vs)) (s.map (ev pub m vs)) := by
  simp [packSite,appendDigit,terms,words,Radices.map,Site.map,ev]

theorem eval_unpackPosition (r : Radices (Term w k n)) (z : Term w k n)
    (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) :
    (unpackPosition (terms w k n) r z).map (ev pub m vs) =
      unpackPosition (words m) (r.map (ev pub m vs)) (ev pub m vs z) := by
  simp [unpackPosition,unpackSite,Position.map,Site.map,Radices.map,terms,words,ev]

theorem eval_parentRow (r : Radices (Term w k 1)) (g : Columns (Term w k 1)) (d : ℕ)
    (layout : Bool) (output : Term w k 1) (pub : Fin k → Word w) (m : Memory w) (p : Word w) :
    let ev' := ev pub m (fun _ => p)
    let rr := r.map ev'
    (parentRow r g d layout output).eval pub m (fun _ => p) =
      packSite (words m) rr (owner (words m) (g.map ev') d layout
        (unpackPosition (words m) rr (p - ev' output))) := by
  dsimp only
  unfold parentRow
  rw [show ∀ z : Term w k 1, z.eval pub m (fun _ => p) = ev pub m (fun _ => p) z from fun _ => rfl,
    eval_packSite,eval_owner,eval_unpackPosition]
  simp [ev,terms,Term.eval,BinaryOp.eval]

theorem append_val (m : Memory w) (a radix b : Word w)
    (fits : a.val * radix.val + b.val < 2^w) :
    (appendDigit (words m) a radix b).val = a.val*radix.val+b.val := by
  have prod : a.val*radix.val < 2^w := by omega
  simp [appendDigit,words,BinaryOp.eval,Fin.val_add,Fin.val_mul,Nat.mod_eq_of_lt prod,Nat.mod_eq_of_lt fits]

theorem digits (m : Memory w) (a radix b : Word w) (h : b.val < radix.val)
    (fits : a.val * radix.val + b.val < 2^w) :
    (words m).bin .div (appendDigit (words m) a radix b) radix = a ∧
      (words m).bin .mod (appendDigit (words m) a radix b) radix = b := by
  have pos : 0 < radix.val := by omega
  have hd : (a.val*radix.val+b.val)/radix.val = a.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt h,Nat.zero_add]
  have hr : (a.val*radix.val+b.val)%radix.val = b.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt h]
  constructor <;> apply Fin.ext
  · change (appendDigit (words m) a radix b).val / radix.val % 2^w = a.val
    rw [append_val m a radix b fits,hd,Nat.mod_eq_of_lt a.isLt]
  · change (appendDigit (words m) a radix b).val % radix.val % 2^w = b.val
    rw [append_val m a radix b fits,hr,Nat.mod_eq_of_lt b.isLt]

end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
