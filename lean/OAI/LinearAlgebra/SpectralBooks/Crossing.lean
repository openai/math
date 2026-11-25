import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Expanding a restriction of a power of a direct sum of wires

A wire is given by the sum of the coordinate basis tensors indexed by its possible
bit strings. Direct sum tags those basis tensors at every site, while tensor power
takes tuples of independently chosen basis tensors. We expand arbitrary local linear
images of these tensors into an ordinary sum of networks with the same output legs.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace Crossing

noncomputable section

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]

/-- An ordered description of an unoriented wire between distinct sites. -/
structure Wire (I : Type*) where
  left : I
  right : I
  distinct : left ≠ right
  width : ℕ

/-- A local index has one bit per wire bit at an endpoint and no bits elsewhere. -/
abbrev Wire.Leg (e : Wire I) (i : I) :=
  {_t : Fin e.width // i = e.left ∨ i = e.right} → Bool

/-- The two endpoints see the same string. -/
def Wire.basisTerm (e : Wire I) (s : Fin e.width → Bool) (i : I) : e.Leg i :=
  fun t => s t.val

/-- Coefficients of a tensor presented as a finite sum of coordinate basis tensors. -/
def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0

/-- On basis terms, a tensor direct sum tags every site's input by the same summand. -/
def sumBasis {L : Type*} {S : L → Type*} {A : L → I → Type*}
    (term : ∀ l, S l → ∀ i, A l i) (s : Σ l, S l) (i : I) : Σ l, A l i :=
  ⟨s.1, term s.1 s.2 i⟩

/-- A basis term of a grouped power chooses the terms of the factors independently. -/
def powerBasis {S : Type*} {A : I → Type*}
    (term : S → ∀ i, A i) (j : ℕ) (s : Fin j → S) (i : I) : Fin j → A i :=
  fun t => term (s t) i

/-- Direct sum of identical copies, recording the copy index at every site. -/
def copiesBasis {S : Type*} {A : I → Type*}
    (term : S → ∀ i, A i) (K : ℕ) (s : Fin K × S) (i : I) : Fin K × A i :=
  (s.1, term s.2 i)

/-- On the block tagged by one summand, the direct sum has precisely the coefficients
of that summand. At least one site is needed to distinguish the tags. -/
theorem basisTensor_sum_onBlock {L : Type*} [Fintype L] {S : L → Type*}
    [∀ l, Fintype (S l)] {A : L → I → Type*} [Nonempty I]
    (term : ∀ l, S l → ∀ i, A l i) (l : L) (x : ∀ i, A l i) :
    basisTensor (F := F) (sumBasis term) (fun i => ⟨l, x i⟩) = basisTensor (term l) x := by
  classical
  unfold basisTensor
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · refine Finset.sum_congr rfl fun s _ => ?_
    have h : (fun i => (⟨l, x i⟩ : Σ l, A l i)) = sumBasis term ⟨l, s⟩ ↔ x = term l s := by
      constructor
      · intro h
        funext i
        exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |>.eq
      · rintro rfl
        rfl
    simp [h]
  · intro l' _ hne
    refine Finset.sum_eq_zero fun s _ => ite_eq_right fun h => hne ?_
    let i := Classical.choice (inferInstance : Nonempty I)
    exact (congrArg Sigma.fst (congrFun h i)).symm
  · simp

/-- Mixed tags have zero coefficient in a tensor direct sum. -/
theorem basisTensor_sum_offBlock {L : Type*} [Fintype L] {S : L → Type*}
    [∀ l, Fintype (S l)] {A : L → I → Type*} (term : ∀ l, S l → ∀ i, A l i)
    (x : ∀ i, Σ l, A l i) (h : ¬ ∃ l, ∀ i, (x i).1 = l) :
    basisTensor (F := F) (sumBasis term) x = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply ite_eq_right
  rintro rfl
  exact h ⟨s.1, fun _ => rfl⟩

/-- The grouped tensor power has the product of the original coefficients. -/
theorem basisTensor_power {S : Type*} [Fintype S] {A : I → Type*}
    (term : S → ∀ i, A i) (j : ℕ) (x : ∀ i, Fin j → A i) :
    basisTensor (F := F) (powerBasis term j) x =
      ∏ t, basisTensor (F := F) term (fun i => x i t) := by
  classical
  unfold basisTensor
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.prod_boole]
  have h : x = powerBasis term j w ↔ ∀ t, (fun i => x i t) = term (w t) := by
    constructor
    · rintro rfl t
      rfl
    · intro ht
      funext i t
      exact congrFun (ht t) i
  simp [h]

/-- The matrix-coefficient definition of restriction by local linear maps. -/
def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
    (X : (∀ i, B i) → F) (Y : (∀ i, A i) → F) : Prop :=
  ∃ M : ∀ i, B i → A i → F, ∀ x,
    X x = ∑ a, Y a * ∏ i, M i (x i) (a i)

/-- Applying matrices to a sum of basis tensors sums the transformed pure tensors. -/
theorem restriction_basisTensor_iff {A B : I → Type*} [∀ i, Fintype (A i)]
    {S : Type*} [Fintype S] (term : S → ∀ i, A i) (X : (∀ i, B i) → F) :
    IsRestriction X (basisTensor term) ↔
      ∃ M : ∀ i, B i → A i → F, ∀ x, X x = ∑ s, ∏ i, M i (x i) (term s i) := by
  unfold IsRestriction basisTensor
  congr! 3 with M x
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- The leaf matrices of a network may jointly read all strings on incident wires. -/
abbrev LocalTables {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I) (F : Type*) :=
  ∀ i, B i → ((t : Fin j) → (wires t).Leg i) → F

/-- Coefficients of a network, obtained by contracting one shared index for each wire. -/
def network {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I)
    (T : LocalTables (B := B) wires F) (x : ∀ i, B i) : F :=
  ∑ s : (t : Fin j) → (Fin (wires t).width → Bool),
    ∏ i, T i (x i) (fun t => (wires t).basisTerm (s t) i)

/-- Reindex a word of tagged strings by first choosing the word of tags. -/
private def splitTags {J L : Type*} (S : L → Type*) :
    (J → Σ l, S l) ≃ (Σ w : J → L, (t : J) → S (w t)) where
  toFun s := ⟨fun t => (s t).1, fun t => (s t).2⟩
  invFun s t := ⟨s.1 t, s.2 t⟩
  left_inv := by intro s; rfl
  right_inv := by rintro ⟨w, s⟩; rfl

/-- The tensor in the strict comparison step, in the coordinate bases of its direct
sums and grouped tensor powers. -/
def copiesOfWirePower {E : Type*} [Fintype E] (wires : E → Wire I) (K j : ℕ) :=
  basisTensor (F := F) (copiesBasis (powerBasis (sumBasis fun l => (wires l).basisTerm) j) K)

/-- Ordinary local-matrix restriction from the tensor used in strict comparison. -/
def RestrictsWirePower {B : I → Type*} {E : Type*} [Fintype E]
    (X : (∀ i, B i) → F) (wires : E → Wire I) (K j : ℕ) : Prop :=
  IsRestriction X (copiesOfWirePower wires K j)

/-- Restricting the direct sum of `K` copies of `W^⊗j`, where `W` is a direct sum
of `L` wires, gives an ordinary sum indexed by a copy and a word of `j` wire choices. -/
theorem restriction_copiesOfWirePower {B : I → Type*} {E : Type*} [Fintype E] {K j : ℕ}
    (wires : E → Wire I) (X : (∀ i, B i) → F)
    (h : RestrictsWirePower X wires K j) :
    ∃ T : (k : Fin K) → (w : Fin j → E) → LocalTables (B := B) (wires ∘ w) F,
      ∀ x, X x = ∑ k, ∑ w, network (wires ∘ w) (T k w) x := by
  obtain ⟨M, hM⟩ := (restriction_basisTensor_iff _ X).mp h
  refine ⟨fun k w i y a => M i y (k, fun t => ⟨w t, a t⟩), ?_⟩
  intro x
  rw [hM, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  let e := splitTags (J := Fin j) (fun l => Fin (wires l).width → Bool)
  simp only [network]
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Number of network summands in the expansion. -/
theorem card_networks (K L j : ℕ) :
    Fintype.card (Fin K × (Fin j → Fin L)) = K * L ^ j := by simp

/-- With sites placed in a metric space, supply its distance for `length`. -/
def wireCost (length : I → I → ℝ) (e : Wire I) : ℝ :=
  e.width * length e.left e.right

omit [Fintype I] in
/-- Absorbing arbitrary local matrices does not increase the cost of a word of wires. -/
theorem network_cost_le {E : Type*} {j : ℕ} {bound : ℝ} (length : I → I → ℝ)
    (wires : E → Wire I) (h : ∀ l, wireCost length (wires l) ≤ bound)
    (w : Fin j → E) :
    ∑ t, wireCost length (wires (w t)) ≤ bound * j := by
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun t _ => h (w t))

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
