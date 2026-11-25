import OAI.Hierarchy.ProtocolRAMScan
import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # Finite packet descriptor scans on actual repeated paid row IDs -/

namespace Hierarchy.ProtocolRAM.PacketScan
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing BigOperators

variable {W n d : ℕ} (mem : Memory W) (row : Word W)

def add (a b : Expr) : Expr := .op .add a b

theorem add_eval (a b : Expr) : (add a b).eval mem row=a.eval mem row+b.eval mem row := rfl

theorem word_eq {x y : ℕ} (hx : x<2^W) (hy : y<2^W) :
    ((x : Word W)=(y : Word W))↔x=y := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

theorem eq_select (a b yes no : Expr) {x y : ℕ} (ax : a.eval mem row=(x : Word W))
    (by' : b.eval mem row=(y : Word W)) (hx : x<2^W) (hy : y<2^W) :
    (.branch .eq a b yes no : Expr).eval mem row=(if x=y then yes.eval mem row else no.eval mem row) := by
  simp [Expr.eval,Comparison.test,ax,by',word_eq hx hy]

/-- Every previous occurrence is compared by the runtime paid-row ID. -/
def earlier (keys widths : Fin n→Expr) (seek : Expr) : ℕ→Expr
  | 0 => .lit 0
  | t+1 => add (earlier keys widths seek t) (if h:t<n then
      .branch .eq (keys ⟨t,h⟩) seek (widths ⟨t,h⟩) (.lit 0) else .lit 0)

theorem earlier_eval (keys widths : Fin n→Expr) (seek : Expr) (key : Fin n→Fin d) (amount : Fin n→ℕ)
    (g : Fin d) (fit : d≤2^W) (keysAt : ∀i,(keys i).eval mem row=((key i).val : Word W))
    (amountAt : ∀i,(widths i).eval mem row=(amount i : Word W)) (seekAt : seek.eval mem row=(g.val : Word W))
    (t : ℕ) : (earlier keys widths seek t).eval mem row=(TaggedShorterCommonScan.earlier key amount t g : Word W) := by
  induction t with
  | zero => simp [earlier,TaggedShorterCommonScan.earlier,Expr.eval]
  | succ t ih =>
    rw [earlier,add_eval,ih]
    unfold TaggedShorterCommonScan.earlier
    rw [Finset.sum_range_succ,Nat.cast_add]
    congr 1
    by_cases h:t<n
    · rw [dite_eq_left h,dite_eq_left h,eq_select mem row _ _ _ _ (keysAt ⟨t,h⟩) seekAt
        ((key ⟨t,h⟩).isLt.trans_le fit) (g.isLt.trans_le fit)]
      by_cases e : key ⟨t,h⟩=g
      · simp [e,amountAt]
      · simp [Fin.ext_iff.not.mp e,e,Expr.eval]
    · simp [h,Expr.eval]

/-- The first matching underlying row is its dense local port sector.
An absent row returns the dummy sector immediately after the menu. -/
def first (seek : Expr) : List Expr→Expr
  | [] => .lit 0
  | a::as => .branch .eq a seek (.lit 0) (add (.lit 1) (first seek as))

theorem first_eval (seek : Expr) {value : ℕ} (seekAt : seek.eval mem row=(value : Word W))
    (fit : value<2^W) (xs : List Expr) (ids : List ℕ)
    (data : xs.Forall₂ (fun (a : Expr) (id : ℕ)=>a.eval mem row=(id : Word W) ∧ id<2^W) ids) :
    (first seek xs).eval mem row=(ids.idxOf value : Word W) := by
  induction data with
  | nil => rfl
  | @cons a id xs ids read tail ih =>
    rw [first,eq_select mem row _ _ _ _ read.1 seekAt read.2 fit,List.idxOf_cons]
    by_cases h:id=value
    · simp [h,Expr.eval]
    · simp [h,add_eval,ih,Expr.eval,Nat.cast_add,add_comm]

end Hierarchy.ProtocolRAM.PacketScan

end OAI
