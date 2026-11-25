import OAI.Hierarchy.GridThrough
import OAI.Hierarchy.GridLensWiring

namespace OAI
/-! # Contracting the joined ports of a fully occupied grid

An idle rail whose passage is supplied by a catalyst at every cell has
one free bit per neighboring pair of cells. Its outermost ports carry
the prescribed external bits. The same bijection between settings
works for every choice of the local cell tables.
-/

namespace Hierarchy.GridThrough

open UniversalGrid
open scoped BigOperators Classical

/-- The incoming and outgoing ports of a cell read the two junctions
on its sides, or read the exterior bit when they reach a focus. -/
def junction {E : Type} {n : ℕ} (x : GridDiagonal.Pins E) (q : E × Fin n → Bool)
    (e : E) (s : Fin (n+1)) (side : Bool) : Bool :=
  if side then Fin.lastCases (x (e,true)) (fun t => q (e,t)) s
  else Fin.cases (x (e,false)) (fun t => q (e,t)) s

section
variable {E : Type} {n : ℕ} (x : GridDiagonal.Pins E) (q : E × Fin n → Bool) (e : E)

@[simp] theorem junction_left : junction x q e 0 false = x (e,false) := by simp [junction]
@[simp] theorem junction_right : junction x q e (Fin.last n) true = x (e,true) := by simp [junction]
@[simp] theorem junction_incoming (i : Fin n) : junction x q e i.succ false = q (e,i) := by
  simp [junction]
@[simp] theorem junction_outgoing (i : Fin n) : junction x q e i.castSucc true = q (e,i) := by
  simp [junction]

end

namespace Program
noncomputable section

variable {E : Type} {k n : ℕ} {width : Fin k → ℕ} (P : Program E n 0 width)

/-- Pin settings of a cell in terms of the compact, shared junctions. -/
def spliceBits (x : GridDiagonal.Pins E) (q : E × Fin n → Bool)
    (i : Fin ((n+1)^k)) : Catalyst.Port 0 width → Bool :=
  let c : Cell k n := cellOrdinal.symm i
  Sum.elim Fin.elim0 (fun ws => junction x q (P.pass c ws.1) (c (P.direction (P.pass c ws.1))) ws.2)

private def expandSplice (x : GridDiagonal.Pins E) (q : E × Fin n → Bool) : P.Hidden → Bool :=
  Sum.elim (fun z => junction x q z.1 z.2.1 z.2.2) (fun _ => false)

private def readSplice (h : P.Hidden → Bool) (v : E × Fin n) : Bool :=
  h (.inl (v.1,v.2.castSucc,true))

private theorem noTouch (idle : ∀ e, P.touch e = none) (u : Touch P.touch) : False := by
  have hu := u.property
  rw [idle u.val.1] at hu
  contradiction

private theorem expandSplice_valid (idle : ∀ e, P.touch e = none) (occupies : ∀ e t, P.Selected e t)
    (x : GridDiagonal.Pins E) (q : E × Fin n → Bool) :
    ∀ z, P.typedEdge x (P.expandSplice x q) z := by
  rintro (⟨e,s⟩ | ⟨e,t⟩ | z | ⟨u,s⟩)
  · cases s <;> simp [typedEdge,expandSplice,junction]
  · simp [typedEdge,expandSplice,junction]
  · exact (z.property.2 (occupies z.val.1 z.val.2)).elim
  · exact (P.noTouch idle u).elim

private theorem expandSplice_read (idle : ∀ e, P.touch e = none)
    (x : GridDiagonal.Pins E) (h : P.Hidden → Bool) (ok : ∀ z, P.typedEdge x h z) :
    P.expandSplice x (P.readSplice h) = h := by
  funext z
  rcases z with ⟨e,t,s⟩ | ⟨u,s⟩
  · cases s with
    | false =>
      refine Fin.cases ?_ (fun i => ?_) t
      · simpa [expandSplice,junction,typedEdge] using ok (.inl (e,false))
      · simpa [expandSplice,junction,typedEdge,readSplice] using ok (.inr (.inl (e,i)))
    | true =>
      refine Fin.lastCases ?_ (fun i => ?_) t
      · simpa [expandSplice,junction,typedEdge] using (ok (.inl (e,true))).symm
      · simp [expandSplice,junction,readSplice]
  · exact (P.noTouch idle u).elim

/-- Valid physical assignments are freely and uniquely specified by the
bits on the interior junctions, including the grid with one cell per line. -/
def spliceEquiv (idle : ∀ e, P.touch e = none) (occupies : ∀ e t, P.Selected e t)
    (x : GridDiagonal.Pins E) :
    {h : P.Hidden → Bool // ∀ z, P.typedEdge x h z} ≃ (E × Fin n → Bool) where
  toFun h := P.readSplice h.val
  invFun q := ⟨P.expandSplice x q,P.expandSplice_valid idle occupies x q⟩
  left_inv h := Subtype.ext (P.expandSplice_read idle x h.val h.property)
  right_inv q := by
    funext v
    simp [readSplice,expandSplice,junction]

private theorem typedPin_splice (x : GridDiagonal.Pins E) (q : E × Fin n → Bool) (c : Cell k n) :
    P.typedPin (P.expandSplice x q) c = P.spliceBits x q (cellOrdinal c) := by
  funext z
  rcases z with i | ⟨w,s⟩
  · exact i.elim0
  · simp [typedPin,spliceBits,expandSplice]

variable [Fintype E] {F : Type*} [Field F]

/-- Splice every collinear pair in the actual mixed contraction. The table
may differ from cell to cell, and no property of its coefficients is used. -/
theorem mixedEval_splice (idle : ∀ e, P.touch e = none) (occupies : ∀ e t, P.Selected e t)
    (A : Fin ((n+1)^k) → (Catalyst.Port 0 width → Bool) → F) (x : GridDiagonal.Pins E) :
    P.wiring.mixedEval A x = ∑ q : E × Fin n → Bool, ∏ i, A i (P.spliceBits x q i) := by
  classical
  let ok (h : P.Hidden → Bool) := ∀ z, P.typedEdge x h z
  let : Fintype (P.Hidden → Bool) := Fintype.ofFinite _
  let : DecidablePred ok := fun h => Classical.propDecidable (ok h)
  let : Fintype {h : P.Hidden → Bool // ok h} := Subtype.fintype ok
  let term (h : P.Hidden → Bool) := ∏ c, A (cellOrdinal c) (P.typedPin h c)
  calc
    P.wiring.mixedEval A x = ∑ h, if ok h then term h else 0 := by
      unfold Wiring.mixedEval
      dsimp only [ok,term]
      convert P.sum_typed A x using 1 <;>
        (apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
         intro y _
         split <;> rename_i test <;> simp only [])
    _ = ∑ h : {h // ok h}, term h.val := by
      rw [← Fintype.sum_subtype_add_sum_subtype ok (fun h => if ok h then term h else 0)]
      have valid (h : {h : P.Hidden → Bool // ok h}) : ok h.val := h.property
      have invalid (h : {h : P.Hidden → Bool // ¬ok h}) : ¬ok h.val := h.property
      simp only [valid,invalid,ite_true,ite_false,Finset.sum_const_zero,add_zero]
    _ = ∑ q : E × Fin n → Bool, term (P.expandSplice x q) :=
      ((P.spliceEquiv idle occupies x).symm.sum_comp (fun h => term h.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      unfold term
      simp_rw [P.typedPin_splice x q]
      exact cellOrdinal.prod_comp (fun i => A i (P.spliceBits x q i))


end
end Program
end Hierarchy.GridThrough

end OAI
