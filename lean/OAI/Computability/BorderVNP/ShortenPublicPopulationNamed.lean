import OAI.Computability.BorderVNP.ShortenPublicPopulationBatch

/-! # Histogram at the geometric pack's original factor names

A product-cover row circuit numbers factors by `Fin q`, while the shortening
layout uses factors indexed by the cube. Reading the batch through this
enumeration returns the original allocator count at each seed, with the
same gate budget.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped BigOperators Classical

variable {I A B C : Type} {U σ : Type*} {q l r w D : ℕ}

/-- Packing the ordered tuple of tile factors does not identify distinct addresses. -/
def indexBins (enum : Fin q ≃ I) : ((I → Deck l) × B) ≃ ((Fin q → Deck l) × B) where
  toFun a := (a.1 ∘ enum, a.2)
  invFun a := (a.1 ∘ enum.symm, a.2)
  left_inv a := by ext j <;> simp [Function.comp_def]
  right_inv a := by ext j <;> simp [Function.comp_def]

variable {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)

/-- Injective recoding of an optional bin leaves its bit population unchanged. -/
theorem count_map (bin : N.Edge → Option A) (f : A ↪ C) (a : A) :
    SeedIntervals.count N (fun e => (bin e).map f) (f a) = SeedIntervals.count N bin a := by
  rw [SeedIntervals.count_eq_sum,SeedIntervals.count_eq_sum]
  apply Finset.sum_congr rfl
  intro e _
  cases he : bin e <;> simp [f.injective.eq_iff]

variable [Fintype U] [Fintype σ] [Fintype B] [Fintype I] [DecidableEq I]
    (enum : Fin q ≃ I) (row : U → Frame σ (ProductSlots q l ⊕ B))
    (code : B ↪ Fin (2^r)) (active : U → σ) (width : U → Fin w → σ)

/-- Return the complete moved histogram in the geometric layout's own factor order. -/
noncomputable def namedRows : Frame σ (((I → Deck l) × B) × Fin w) :=
  (movedRows row code active width).select fun aj => (indexBins enum aj.1, aj.2)

/-- The size bound counts the occupied or reserved rows plus all actual legal geometric bins. -/
theorem namedRows_size :
    let n := Fintype.card U + Fintype.card (I → Deck l)*Fintype.card B
    (namedRows enum row code active width).size ≤ 1 + (∑ u, (row u).size) +
      (Fintype.card U*r*(2*Fintype.card B+1) + 2*(n+1)*laneCost (Nat.clog 2 n) (r+keyWidth q l) w) := by
  have card : Fintype.card (Fin q → Deck l) = Fintype.card (I → Deck l) := by
    simp only [Fintype.card_fun, Fintype.card_congr enum]
  simpa only [namedRows,Frame.select_size,card] using movedRows_size row code active width

variable (bin : N.Edge → Option ((I → Deck l) × B)) (slot : N.Edge ↪ U)

/-- Use the one-hot classifier's full output equality at each active old edge.
The result is the literal `count` at the original geometric seed. -/
theorem namedRows_count (x : σ → Bool)
    (enabled : ∀ e, x (active (slot e)) = (bin e).isSome)
    (empty : ∀ u, u ∉ Set.range slot → x (active u) = false)
    (classifies : ∀ e a, bin e = some a → (row (slot e)).eval x =
      Sum.elim (productWires l (a.1 ∘ enum)) (fun b => decide (b = a.2)))
    (widthWord : ∀ e a, bin e = some a → value (x ∘ width (slot e)) = N.width e)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (a : (I → Deck l) × B) :
    value (fun j => (namedRows enum row code active width).eval x (a,j)) = SeedIntervals.count N bin a := by
  let f := (indexBins (l := l) (B := B) enum).toEmbedding
  let tags (e : N.Edge) := (bin e).map f
  have unmap (e : N.Edge) (b) (h : tags e = some b) : ∃ c, bin e = some c ∧ f c = b := by
    cases hc : bin e <;> simp_all [tags]
  have hcount (c) : SeedIntervals.count N tags (f c) = SeedIntervals.count N bin c := count_map N bin f c
  rw [← hcount]
  simp only [namedRows,Frame.select_eval]
  apply movedRows_count row code active width N tags slot x _ empty _ _ _ _ (f a)
  · intro e
    simpa only [tags,Option.isSome_map] using enabled e
  · intro e b he j
    obtain ⟨c,hc,rfl⟩ := unmap e b he
    rw [classifies e c hc]
    rfl
  · intro e b he c
    obtain ⟨b,hb,rfl⟩ := unmap e b he
    rw [classifies e b hb]
    simp [f,indexBins]
  · intro e b he
    obtain ⟨c,hc,_⟩ := unmap e b he
    exact widthWord e c hc
  · intro b
    obtain ⟨c,rfl⟩ := (indexBins enum).surjective b
    exact (hcount c).trans_lt (fits c)

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
