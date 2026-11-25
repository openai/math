import OAI.Computability.BorderVNP.CrossingJunctionSites
import OAI.Computability.VPVNP.BalancedCircuit

/-!
# Local tables for the split crossing tensor

Each terminal cable copies its external word. The opposite junction reads the opposite
terminals and every bridge. The two split junctions read only their respective terminals
and bridges, and both read the same rank word. Unused rank words contribute zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open scoped BigOperators Classical
open VPVNP

/-- A fixed labeling of the possible words on one cable. -/
noncomputable def cableLabels (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Extend a rank factor to all words of the minimal integral bit width, assigning zero to
unused words. -/
noncomputable def rankEntry {K : Type*} [Zero K] {r : ℕ} (f : Fin r → K)
    (w : Fin (Nat.clog 2 r) → Bool) : K :=
  if h : (cableLabels _ w).val < r then f ⟨(cableLabels _ w).val, h⟩ else 0

/-- Summing the product of two padded rank factors preserves the original rank contraction. -/
theorem sum_rankEntry_mul {K : Type*} [CommSemiring K] {r : ℕ} (f g : Fin r → K) :
    ∑ w, rankEntry f w * rankEntry g w = ∑ i, f i * g i := by
  classical
  let e := (Fin.castLEEmb (Nat.le_pow_clog (by decide : 1 < 2) r)).trans
    (cableLabels _).symm.toEmbedding
  let t (w : Fin (Nat.clog 2 r) → Bool) := rankEntry f w * rankEntry g w
  change ∑ w, t w = _
  calc
    _ = ∑ w ∈ Finset.univ.map e, t w := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      have h : ¬ (cableLabels _ w).val < r := by
        intro hin
        apply hw
        apply Finset.mem_map.mpr
        refine ⟨⟨(cableLabels _ w).val, hin⟩, Finset.mem_univ _, ?_⟩
        apply (cableLabels _).injective
        simp [e]
      simp [t, rankEntry, h]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp [t, rankEntry, e, i.isLt]

/-- The index assigned to each terminal or bridge on a side of the crossing. -/
def sideLabels {D p q : ℕ} (x : Fin D → Fin q) (bridge : Fin p → Fin q) :
    (Fin D ⊕ Fin p) → Fin q := Sum.elim x bridge

variable {D p m r : ℕ} (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1)

local notation "N" => junctionNetwork m r negative I moveLeft z hz
local notation "Word" => Fin m → Bool
local notation "RankWord" => Fin (Nat.clog 2 r) → Bool

private abbrev Visible (side : Bool) :=
  ∀ e : {e : (N).Edge // (N).src e = .inr (.inr side) ∨ (N).dst e = .inr (.inr side)},
    Fin ((N).width e.val) → Bool

private def cutWord {side : Bool}
    (a : Visible (m := m) (r := r) negative I moveLeft z hz side) :
    (i : Fin D ⊕ Fin p) → decide (i ∈ I) = side → Word
  | .inl j, hj => a ⟨.inl (j, negative j), Or.inr (by simp [junctionNetwork, hj])⟩
  | .inr j, hj => a ⟨.inr (.inl j), Or.inr (by simp [junctionNetwork, hj])⟩

/-- All local tensors in the three-junction representation. A terminal equality table
forces a unique copy on its cable, and the cut uses zero-padded left and right factors. -/
noncomputable def junctionTables {K : Type*} [Field K]
    (F : CutFactors I (Fin r) (Fin (2 ^ m)) K)
    (opposite : ((Fin D ⊕ Fin p) → Fin (2 ^ m)) → K) : (N).Tables K
  | .inl port, a, x => if a ⟨.inl port, Or.inl rfl⟩ = x ⟨port, rfl⟩ then 1 else 0
  | .inr (.inl ()), a, _ => opposite (sideLabels
      (fun i => cableLabels _ (a ⟨.inl (i, !negative i), Or.inr (by cases h : negative i <;> simp [junctionNetwork, h])⟩))
      (fun j => cableLabels _ (a ⟨.inr (.inl j), Or.inl rfl⟩)))
  | .inr (.inr true), a, _ => rankEntry (fun k => F.left (fun i => cableLabels _
      (cutWord negative I moveLeft z hz a i.val (decide_eq_true i.property))) k)
      (a ⟨.inr (.inr ()), Or.inl rfl⟩)
  | .inr (.inr false), a, _ => rankEntry (fun k => F.right k (fun i => cableLabels _
      (cutWord negative I moveLeft z hz a i.val (decide_eq_false (Finset.mem_compl.mp i.property)))))
      (a ⟨.inr (.inr ()), Or.inr rfl⟩)

private def assembleAssignment (x : (Fin D × Bool) → Word) (j : Fin p → Word) (k : RankWord) :
    (N).Assignment
  | .inl t => x t
  | .inr (.inl b) => j b
  | .inr (.inr ()) => k

private def junctionAssignmentEquiv :
    (((Fin D × Bool) → Word) × (Fin p → Word) × RankWord) ≃ (N).Assignment where
  toFun a := assembleAssignment negative I moveLeft z hz a.1 a.2.1 a.2.2
  invFun a := (fun i => a (.inl i), fun b => a (.inr (.inl b)), a (.inr (.inr ())))
  left_inv _ := rfl
  right_inv a := by funext e; rcases e with t | ⟨b | ⟨⟩⟩ <;> rfl

private theorem cutWord_assemble {side : Bool} (x : (Fin D × Bool) → Word) (j : Fin p → Word)
    (k : RankWord) (i : Fin D ⊕ Fin p) (hi : decide (i ∈ I) = side) :
    cutWord negative I moveLeft z hz
      (fun e => assembleAssignment negative I moveLeft z hz x j k e.val) i hi =
      Sum.elim (fun t => x (t, negative t)) j i := by
  cases i <;> rfl

/-- Decode the selected terminals and a bridge assignment into the party labels of a side. -/
noncomputable def junctionLabels (m : ℕ) (negative : Fin D → Bool) (x : Ports (fun _ : Fin D × Bool => m))
    (j : Fin p → Fin (2 ^ m)) : (Fin D ⊕ Fin p) → Fin (2 ^ m) :=
  sideLabels (fun i => cableLabels m (x (i, negative i))) j

set_option backward.isDefEq.respectTransparency false in
private theorem assignment_product {K : Type*} [Field K]
    (F : CutFactors I (Fin r) (Fin (2 ^ m)) K)
    (opposite : ((Fin D ⊕ Fin p) → Fin (2 ^ m)) → K)
    (x x' : (Fin D × Bool) → Word) (j : Fin p → Word) (k : RankWord) :
    ∏ v : (N).Site, (N).read (junctionTables negative I moveLeft z hz F opposite)
      (assembleAssignment negative I moveLeft z hz x' j k) x v =
      (if x' = x then 1 else 0) * (opposite (junctionLabels m (fun i => !negative i) x' (fun b => cableLabels m (j b))) *
        (rankEntry (fun a => F.left (fun i => junctionLabels m negative x' (fun b => cableLabels m (j b)) i.val) a) k *
         rankEntry (fun a => F.right a (fun i => junctionLabels m negative x' (fun b => cableLabels m (j b)) i.val)) k)) := by
  classical
  change (∏ v : (Fin D × Bool) ⊕ (Unit ⊕ Bool), (N).read _ _ x v) = _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_bool]
  have hcut (i : Fin D ⊕ Fin p) : cableLabels m (Sum.elim (fun t => x' (t, negative t)) j i) =
      junctionLabels m negative x' (fun b => cableLabels m (j b)) i := by cases i <;> rfl
  simp only [Network.read, junctionTables, Fintype.prod_unique]
  simp_rw [cutWord_assemble, hcut]
  have hterm : (∏ t : Fin D × Bool, (if x' t = x t then (1 : K) else 0)) =
      (if x' = x then 1 else 0) := by
    rw [Fintype.prod_boole]
    congr 1
    exact propext funext_iff.symm
  rw [← hterm]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  by_cases ht : x' t = x t <;> simp [assembleAssignment, ht]

set_option backward.isDefEq.respectTransparency false in
/-- Contracting the three junctions first sums over the shared rank label and then
sums over all bridges. Each valid terminal assignment contributes exactly once. -/
theorem junctionNetwork_value {K : Type*} [Field K]
    (F : CutFactors I (Fin r) (Fin (2 ^ m)) K)
    (opposite : ((Fin D ⊕ Fin p) → Fin (2 ^ m)) → K) (x : Ports (fun _ : Fin D × Bool => m)) :
    (N).value (junctionTables negative I moveLeft z hz F opposite) x =
      ∑ j, opposite (junctionLabels m (fun i => !negative i) x j) *
        F.matrix (fun i => junctionLabels m negative x j i.val)
          (fun i => junctionLabels m negative x j i.val) := by
  classical
  unfold Network.value
  rw [← (junctionAssignmentEquiv (m := m) (r := r) negative I moveLeft z hz).sum_comp]
  change (∑ a : (((Fin D × Bool) → Word) × (Fin p → Word) × RankWord), ∏ v : (N).Site, (N).read _ (assembleAssignment negative I moveLeft z hz a.1 a.2.1 a.2.2) x v) = _
  simp only [Fintype.sum_prod_type, assignment_product,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [← Finset.mul_sum, sum_rankEntry_mul]
  let e := Equiv.piCongrRight (fun _ : Fin p => cableLabels m)
  exact e.sum_comp (fun j => opposite (junctionLabels m (fun i => !negative i) x j) *
    F.matrix (fun i => junctionLabels m negative x j i.val) (fun i => junctionLabels m negative x j i.val))

end Crossing

end BorderVNP
end Computability
end OAI
