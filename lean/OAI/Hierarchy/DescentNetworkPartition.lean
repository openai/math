import OAI.Computability.BorderVNP.CrossingNetwork
import Mathlib.Tactic

namespace OAI
/-! # Contracting all sites in each part of a finite partition

The remaining cables are precisely the original cables between distinct parts.
The table of a part sums each internal cable once and uses each original table once.
-/

namespace Hierarchy.DescentNetworkPartition

open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {D d : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) {C : Type} [Fintype C] (loc : N.Site → C)

abbrev CrossingEdge := {e : N.Edge // loc (N.src e) ≠ loc (N.dst e)}

abbrev PrivateEdge (c : C) := {e : N.Edge // loc (N.src e) = c ∧ loc (N.dst e) = c}

abbrev PublicLabels := (e : CrossingEdge N loc) → Fin (N.width e.val) → Bool

abbrev PrivateLabels (c : C) := (e : PrivateEdge N loc c) → Fin (N.width e.val) → Bool

/-- Restriction to the surviving cables and to each part's private cables. -/
def assignmentEquiv : N.Assignment ≃ PublicLabels N loc × ((c : C) → PrivateLabels N loc c) where
  toFun a := (fun e => a e.val, fun _ e => a e.val)
  invFun z e := if h : loc (N.src e) = loc (N.dst e) then
    z.2 (loc (N.src e)) ⟨e, rfl, h.symm⟩ else z.1 ⟨e, h⟩
  left_inv a := by funext e; dsimp only; split <;> rfl
  right_inv := by
    rintro ⟨a, y⟩
    apply Prod.ext
    · funext e
      exact dite_eq_right e.property
    · funext c e
      rcases e with ⟨e, hs, ht⟩
      cases hs
      exact dite_eq_left ht.symm

variable (position : C → EuclideanSpace ℝ (Fin d)) (in_ball : ∀ c, ‖position c‖ ≤ 1)

/-- Move each part to its chosen position and retain all cables between parts. -/
abbrev quotient : Network d P bits where
  Site := C
  Edge := CrossingEdge N loc
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := loc (N.src e.val)
  dst e := loc (N.dst e.val)
  width e := N.width e.val
  attach p := loc (N.attach p)
  position := position
  in_ball := in_ball

variable {F : Type*} [CommSemiring F]

/-- Reconstruct a single original incident word from the private and crossing operands of its part. -/
def localWord {c : C} (v : {v : N.Site // loc v = c})
    (z : (e : {e : CrossingEdge N loc // loc (N.src e.val) = c ∨ loc (N.dst e.val) = c}) →
      Fin (N.width e.val.val) → Bool) (y : PrivateLabels N loc c)
    (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val}) : Fin (N.width e.val) → Bool :=
  let incident := e.property.imp (fun h => (congrArg loc h).trans v.property)
    (fun h => (congrArg loc h).trans v.property)
  if h : loc (N.src e.val) = loc (N.dst e.val) then
    y ⟨e.val, incident.elim (fun hs => ⟨hs, h.symm.trans hs⟩) (fun ht => ⟨h.trans ht, ht⟩)⟩
  else z ⟨⟨e.val, h⟩, incident⟩

/-- The table of a part reads its incident surviving cables and attached ports. -/
def tables (T : N.Tables F) : (quotient N loc position in_ball).Tables F :=
  fun c z x => ∑ y : PrivateLabels N loc c, ∏ v : {v : N.Site // loc v = c},
    T v.val (localWord N loc v z y)
      (fun p => x ⟨p.val, (congrArg loc p.property).trans v.property⟩)

private theorem split_sum (factor : PublicLabels N loc → (c : C) → PrivateLabels N loc c → F) :
    (∑ z : PublicLabels N loc, ∏ c : C, ∑ y : PrivateLabels N loc c, factor z c y) =
      ∑ a : N.Assignment, ∏ c : C, factor ((assignmentEquiv N loc a).1) c ((assignmentEquiv N loc a).2 c) := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  exact ((assignmentEquiv N loc).sum_comp (fun z => ∏ c : C, factor z.1 c (z.2 c))).symm

omit [Fintype C] in
private theorem restrictWord (a : N.Assignment) {c : C} (v : {v : N.Site // loc v = c}) :
    localWord N loc v (fun e => a e.val.val) (fun e => a e.val) =
      fun e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val} => a e.val := by
  funext e
  unfold localWord
  split <;> rfl

set_option maxHeartbeats 600000 in
/-- Contracting the partition computes the original scalar for every pin assignment. -/
theorem value_eq (T : N.Tables F) (x : Ports bits) :
    (quotient N loc position in_ball).value (tables N loc position in_ball T) x = N.value T x := by
  classical
  let factor (z : PublicLabels N loc) (c : C) (y : PrivateLabels N loc c) :=
    ∏ v : {v : N.Site // loc v = c}, T v.val (localWord N loc v (fun e => z e.val) y) (fun p => x p.val)
  have expose : (quotient N loc position in_ball).value (tables N loc position in_ball T) x =
      ∑ z : PublicLabels N loc, ∏ c : C, ∑ y : PrivateLabels N loc c, factor z c y := by
    unfold Network.value
    apply Finset.sum_congr (by ext; simp)
    intro z _
    apply Finset.prod_congr (by ext; simp)
    intro c _
    unfold Network.read tables factor
    apply Finset.sum_congr (by ext; simp)
    intro y _
    apply Finset.prod_congr (by ext; simp)
    intro v _
    rfl
  refine (expose.trans (split_sum N loc factor)).trans (Finset.sum_congr rfl ?_)
  intro a _
  calc
    _ = ∏ c : C, ∏ v : {v : N.Site // loc v = c}, N.read T a x v.val := by
      simp only [factor, assignmentEquiv, Equiv.coe_fn_mk, restrictWord, Network.read]
    _ = _ := Fintype.prod_fiberwise loc _

end
end Hierarchy.DescentNetworkPartition

end OAI
