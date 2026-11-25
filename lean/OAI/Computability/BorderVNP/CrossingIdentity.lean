import OAI.Computability.BorderVNP.CrossingShortening
import OAI.Computability.BorderVNP.CrossingRebundle
import OAI.Computability.BorderVNP.CrossingJunctionSites

/-!
# The antipodal identity supplied by border interpolation

All power slots are gathered at their original terminals into a single cable
of width `t*m`. The resulting exact finite identity already pays for a selector
sent to every terminal, as required before using the histogram wiring.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open scoped BigOperators
variable {D m t : ℕ} {K : Type*} [Field K]

/-- Equality of the antipodal words in every coordinate direction. -/
def antipodalTensor (K : Type*) [Field K] (D m : ℕ)
    (x : Ports (fun _ : Fin D × Bool => m)) : K :=
  if ∀ i : Fin D, x (i, false) = x (i, true) then 1 else 0

/-- The bundled antipodal tensor is the product of the equality tests on all its slots. -/
theorem antipodalTensor_bundle (x : Ports (fun _ : Fin D × Bool => t * m)) :
    antipodalTensor K D (t*m) x =
      ∏ j : Fin t, antipodalTensor K D m (fun p => Network.portSlices x (j,p)) := by
  classical
  have hslice : (∀ i : Fin D, x (i, false) = x (i, true)) ↔
      ∀ (j : Fin t) (i : Fin D),
        Network.portSlices x (j, (i,false)) = Network.portSlices x (j, (i,true)) := by
    constructor
    · intro h j i
      funext k
      exact congrFun (h i) _
    · intro h i
      funext k
      obtain ⟨⟨j,l⟩, rfl⟩ := finProdFinEquiv.surjective k
      exact congrFun (h j i) l
  unfold antipodalTensor
  by_cases h : ∀ i : Fin D, x (i,false) = x (i,true)
  · simp [h, hslice.mp h]
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := not_forall.mp (mt hslice.mpr h)
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).symm

/-- A one-copy antipodal identity with the rounded selector cost charged separately.
The cap is common to all terms, so every histogram has the same strict budget. -/
structure PaidIdentity (K : Type*) [Field K] (D m : ℕ) where
  /-- Exact summands, each encoded by a selector word of fixed width. -/
  count : ℕ
  /-- Actual finite cable layouts of the summands. -/
  net : Fin count → Network D (Fin D × Bool) (fun _ => m)
  /-- All field entries needed to realize the exact identity. -/
  table : ∀ a, (net a).Tables K
  placed : ∀ a, (net a).PlacedAt antipodalPosition
  identity : ∀ x, antipodalTensor K D m x = ∑ a, (net a).value (table a) x
  /-- Uniform wire-length cap for an individual exact term. -/
  cap : ℝ
  cost_le : ∀ a, (net a).cost ≤ cap
  strict : cap + 2 * D * (Nat.clog 2 count : ℝ) < 2 * D * m

/-- Lemma 3.3, including the exact rebundled identity and the full control cost:
a finite list of fixed network topologies approximating the antipodal tensor below
the strict budget yields a paid identity at some positive multiple of the width. -/
theorem paidIdentity_of_border {α : Type*} {L : ℕ} (hD : 0 < D) (hL : 0 < L)
    (N : Fin L → Network D (Fin D × Bool) (fun _ => m))
    (T : ∀ _ : α, ∀ i, (N i).Tables K) {w : ℝ}
    (hf : antipodalTensor K D m ∈ imageClosure (Set.range fun z => ∑ i, (N i).value (T z i)))
    (hp : ∀ i, (N i).PlacedAt antipodalPosition) (hw : ∀ i, (N i).cost ≤ w)
    (hsave : w + 2 * D * Real.logb 2 L < 2 * D * m) :
    ∃ t : ℕ, 0 < t ∧ Nonempty (PaidIdentity K D (t*m)) := by
  classical
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  obtain ⟨t, ht, e, hcost, hstrict⟩ := network_power_strict_saving hL N T hf hp hw hsave
  let base : Fin t := ⟨0, ht⟩
  refine ⟨t, ht, ⟨{
    count := e.count
    net := fun a => Network.rebundle (bits := fun _ : Fin D × Bool => m) (e.net a) base
    table := fun a => Network.rebundleTables (bits := fun _ : Fin D × Bool => m) (e.net a) base (e.table a)
    placed := fun a => Network.rebundle_placedAt (bits := fun _ : Fin D × Bool => m) (place := antipodalPosition) (e.net a) base (e.placed a)
    identity := ?_
    cap := t * w
    cost_le := ?_
    strict := ?_ }⟩⟩
  · intro x
    rw [antipodalTensor_bundle]
    simp_rw [Network.rebundle_value (bits := fun _ : Fin D × Bool => m)]
    exact e.exact_sum (Network.portSlices x)
  · intro a
    rw [Network.rebundle_cost (bits := fun _ : Fin D × Bool => m) (e.net a) base (e.placed a)]
    exact hcost a
  · push_cast
    linarith only [hstrict]

end Crossing

end BorderVNP
end Computability
end OAI
