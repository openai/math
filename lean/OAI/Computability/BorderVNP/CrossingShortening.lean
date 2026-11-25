import OAI.Computability.BorderVNP.CrossingParallel
import OAI.Computability.BorderVNP.CrossingSelector
import OAI.Computability.BorderVNP.CrossingSpan

/-!
# Turning a border identity into an exact network identity

The interpolation terms in Lemma 3.3 are disjoint unions of genuine networks.
A scalar is inserted at one local tensor. All external terminals retain their
positions, and the strict length comparison includes the cost of broadcasting
one copy of the integral selector to each terminal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter
open scoped BigOperators Classical
variable {D : ℕ} {P : Type} [Fintype P] [Nonempty P] {bits : P → ℕ} {K : Type*} [Field K]

/-- An exact sum of placed networks on the separate slots of a power of a tensor. -/
structure PowerNetworks (f : Ports bits → K) (place : P → EuclideanSpace ℝ (Fin D))
    (t : ℕ) where
  /-- Number of exact summands. -/
  count : ℕ
  /-- Topology, placement and widths of each summand. -/
  net : Fin count → Network D (Fin t × P) (fun ip => bits ip.2)
  /-- Field-valued local tables, including the interpolation scalars. -/
  table : ∀ a, (net a).Tables K
  placed : ∀ a, (net a).PlacedAt (fun ip => place ip.2)
  exact_sum : ∀ x : Ports (fun ip : Fin t × P => bits ip.2),
    (∏ i, f (fun p => x (i,p))) = ∑ a, (net a).value (table a) x

/-- The tensor-power expansion for fixed placed shapes can be implemented by
actual local networks. Every summand uses at most `t * w` wire length. -/
theorem network_power_interpolation {α : Type*} {L t : ℕ} (ht : 0 < t)
    (N : Fin L → Network D P bits) (T : ∀ _ : α, ∀ i, (N i).Tables K)
    {f : Ports bits → K} {place : P → EuclideanSpace ℝ (Fin D)} {w : ℝ}
    (hf : f ∈ imageClosure (Set.range fun z => ∑ i, (N i).value (T z i)))
    (hp : ∀ i, (N i).PlacedAt place) (hw : ∀ i, (N i).cost ≤ w) :
    ∃ e : PowerNetworks f place t, e.count ≤ (t+1) ^ Fintype.card (Ports bits) * L ^ t ∧
      ∀ a, (e.net a).cost ≤ t * w := by
  classical
  let term (z : α) (i : Fin L) := (N i).value (T z i)
  obtain ⟨b, hb, par, c, he⟩ := interpolate_network_sums term hf t
  let W := Fin b × (Fin t → Fin L)
  let idx := (Fintype.equivFin W).symm
  let net (a : W) := Network.parallel (fun j : Fin t => N (a.2 j))
  let T' (a : W) := Network.parallelTables (fun j : Fin t => N (a.2 j))
    (fun j => T (par a.1) (a.2 j))
  let first (a : W) : (net a).Site :=
    (net a).attach (⟨0, ht⟩, Classical.choice ‹Nonempty P›)
  let table (a : W) := (net a).scaleTable (first a) (c a.1) (T' a)
  have hterm (a : W) (x : Ports (fun ip : Fin t × P => bits ip.2)) :
      (net a).value (table a) x = c a.1 * ∏ j, term (par a.1) (a.2 j) (fun p => x (j,p)) := by
    rw [Network.value_scaleTable, Network.parallel_value]
  let e : PowerNetworks f place t := {
    count := Fintype.card W
    net := net ∘ idx
    table := fun a => table (idx a)
    placed := fun a => Network.parallel_placedAt _ (fun j => hp ((idx a).2 j))
    exact_sum := fun x => by
      change _ = ∑ a, (net (idx a)).value (table (idx a)) x
      rw [idx.sum_comp (fun a => (net a).value (table a) x)]
      simp_rw [hterm]
      rw [Fintype.sum_prod_type]
      exact he (fun j p => x (j,p)) }
  refine ⟨e, ?_, ?_⟩
  · change Fintype.card W ≤ _
    simp only [W, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    exact Nat.mul_le_mul_right _ (hb.trans (powersCount_le_polynomial _ _ Fintype.card_pos))
  · intro a
    change (Network.parallel _).cost ≤ _
    rw [Network.parallel_cost]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
      (fun j _ => hw ((idx a).2 j))

/-- If the per-copy budget (3.1) is strict, one positive power of the limiting
tensor has an exact sum whose genuine networks and rounded selector cost fit
strictly below the `2 * D * t * m` direct-wire length. -/
theorem network_power_strict_saving {α : Type*} {m L : ℕ} (hL : 0 < L)
    (N : Fin L → Network D P bits) (T : ∀ _ : α, ∀ i, (N i).Tables K)
    {f : Ports bits → K} {place : P → EuclideanSpace ℝ (Fin D)} {w : ℝ}
    (hf : f ∈ imageClosure (Set.range fun z => ∑ i, (N i).value (T z i)))
    (hp : ∀ i, (N i).PlacedAt place) (hw : ∀ i, (N i).cost ≤ w)
    (hsave : w + 2 * D * Real.logb 2 L < 2 * D * m) :
    ∃ t : ℕ, 0 < t ∧ ∃ e : PowerNetworks f place t,
      (∀ a, (e.net a).cost ≤ t * w) ∧
        (t : ℝ) * w + 2 * D * (Nat.clog 2 e.count : ℝ) < t * (2 * D * m) := by
  classical
  obtain ⟨t, ht, hbudget⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and
      (eventually_selector_strict_saving D m L (Fintype.card (Ports bits)) w hL hsave)).exists
  obtain ⟨e, hc, he⟩ := network_power_interpolation ht N T hf hp hw
  exact ⟨t, ht, e, he, hbudget e.count hc⟩

end Crossing

end BorderVNP
end Computability
end OAI
