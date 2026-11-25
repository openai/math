import OAI.ThreeFlat.RAM.DescriptorExpr
import OAI.ThreeFlat.Diagonal.CompressorOrderedScan

namespace OAI
/-! # Native first-available color and tag computation

The forbidden words are runtime expressions reading neighbor descriptors.
Only the finite candidate list and the number of slots are unrolled.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr
open scoped Fin.NatCast
variable {w k n : ℕ}

def member (a : Word w) : List (Term w k n) → Term w k n
  | [] => .literal 0
  | z :: tail => .select .eq (.literal a) z (.literal 1) (member a tail)

def firstFree (banned : List (Term w k n)) (fallback : Word w) : List (Word w) → Term w k n
  | [] => .literal fallback
  | a :: tail => .select .eq (member a banned) (.literal 1) (firstFree banned fallback tail)
      (.literal a)

theorem eval_member (a : Word w) (banned : List (Term w k n)) (pub : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) :
    (member a banned).eval pub m vs =
      if a ∈ banned.map (fun z => z.eval pub m vs) then 1 else 0 := by
  induction banned with
  | nil => simp [member]
  | cons z rest ih =>
    by_cases h : a = z.eval pub m vs <;> simp [member,Comparison.test,h,ih]

theorem eval_firstFree (one : (1 : Word w) ≠ 0) (banned : List (Term w k n))
    (fallback : Word w) (choices : List (Word w)) (pub : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) :
    (firstFree banned fallback choices).eval pub m vs =
      Ordered.pick (banned.map fun z => z.eval pub m vs) fallback choices := by
  induction choices with
  | nil => simp [firstFree,Ordered.pick]
  | cons a rest ih =>
    by_cases h : a ∈ banned.map (fun z => z.eval pub m vs) <;>
      simp [firstFree,Ordered.pick,eval_member,Comparison.test,h,one.symm,ih]

private theorem binds_literal (v : Word w) : (Term.literal (k:=k) (n:=n) v).binds = 1 := rfl

private theorem binds_select (cmp : Comparison) (x y yes no : Term w k n) :
    (Term.select cmp x y yes no).binds = x.binds + y.binds + yes.binds + no.binds + 1 := by
  simp [Term.select,Term.binds,Nat.add_assoc]

def banCost (banned : List (Term w k n)) : ℕ := (banned.map fun z => z.binds + 3).sum

theorem binds_member (a : Word w) (banned : List (Term w k n)) :
    (member a banned).binds = 1 + banCost banned := by
  induction banned with
  | nil => rfl
  | cons z rest ih =>
    simp only [member,binds_select,binds_literal,ih,banCost,List.map_cons,List.sum_cons]
    omega

theorem binds_firstFree (banned : List (Term w k n)) (fallback : Word w)
    (choices : List (Word w)) :
    (firstFree banned fallback choices).binds = 1 + choices.length * (4 + banCost banned) := by
  induction choices with
  | nil => simp [firstFree,binds_literal]
  | cons a rest ih =>
    simp only [firstFree,binds_select,binds_member,binds_literal,ih,List.length_cons,Nat.succ_mul]
    omega

/-- Slot records are dense and vertex-major. Columns occupy independent arrays. -/
def slotAddr (base vertex : Term w k n) (d : ℕ) (i : Fin d) : Term w k n :=
  .binary .add (.binary .add base (.binary .mul vertex (.literal (d : Word w))))
    (.literal (i.val : Word w))

def readSlot (base vertex : Term w k n) (d : ℕ) (i : Fin d) : Term w k n :=
  (slotAddr base vertex d i).load

def readRow (base vertex : Term w k n) : Term w k n := (Term.binary .add base vertex).load

theorem eval_readSlot (base vertex : Term w k n) (d : ℕ) (i : Fin d)
    (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) :
    (readSlot base vertex d i).eval pub m vs =
      m (base.eval pub m vs + vertex.eval pub m vs * (d : Word w) + (i.val : Word w)).val := by
  simp [readSlot,slotAddr,BinaryOp.eval]

theorem eval_readRow (base vertex : Term w k n) (pub : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) :
    (readRow base vertex).eval pub m vs = m (base.eval pub m vs + vertex.eval pub m vs).val := by
  simp [readRow,BinaryOp.eval]

def colorBans (d : ℕ) (table outDst inSrc vertex : Term w k n) : List (Term w k n) :=
  (List.ofFn fun i : Fin d => readRow table (readSlot outDst vertex d i)) ++
    (List.ofFn fun i : Fin d => readRow table (readSlot inSrc vertex d i))

@[simp] theorem colorBans_length (d : ℕ) (table outDst inSrc vertex : Term w k n) :
    (colorBans d table outDst inSrc vertex).length = 2*d := by simp [colorBans]; omega

/-- The cursor presented by the native driver is an absolute address in the color array. -/
def colorRow (d : ℕ) (table outDst inSrc : Term w k 1) : Term w k 1 :=
  firstFree (colorBans d table outDst inSrc (.binary .sub (.result 0) table)) 0
    (List.ofFn fun i : Fin (2*d+1) => (i.val : Word w))

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
