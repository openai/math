import Lemmata.FockCircuits.BasisAction
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Embedding

/-!
# Finite exterior levels for wire relocation

The two summands in Appendix A.2 factor through the neighboring exterior
levels. The restricted creation and contraction matrices retain the integral
anticommutation identity in their ordered subset bases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.ExteriorLevels

open Lemmata.FockCircuits

/-- The coordinate indices for the degree-`b` exterior power on `Q` generators. -/
def Level (Q b : ℕ) := {s : Finset (Fin Q) // s.card = b}

instance (Q b : ℕ) : DecidableEq (Level Q b) :=
  inferInstanceAs (DecidableEq {s : Finset (Fin Q) // s.card = b})

instance (Q b : ℕ) : Fintype (Level Q b) :=
  inferInstanceAs (Fintype {s : Finset (Fin Q) // s.card = b})

@[simp] theorem card_level (Q b : ℕ) : Fintype.card (Level Q b) = Q.choose b := by
  calc
    Fintype.card (Level Q b) = Fintype.card {s : Finset (Fin Q) // s.card = b} :=
      Fintype.card_congr (Equiv.refl _)
    _ = Q.choose b := by
      simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin Q) b

/-- Realize bounded generator indices as natural-number indices. -/
def indexSet {Q b : ℕ} (s : Level Q b) : Finset ℕ := s.val.map Fin.valEmbedding

@[simp] theorem card_indexSet {Q b : ℕ} (s : Level Q b) : (indexSet s).card = b :=
  (Finset.card_map _).trans s.property

@[simp] theorem mem_indexSet {Q b : ℕ} (s : Level Q b) (i : Fin Q) :
    i.val ∈ indexSet s ↔ i ∈ s.val :=
  Finset.mem_map' _

theorem lt_of_mem_indexSet {Q b i : ℕ} (s : Level Q b) (hi : i ∈ indexSet s) : i < Q := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact j.isLt

theorem indexSet_injective {Q b : ℕ} : Function.Injective (@indexSet Q b) := by
  intro s t h
  exact Subtype.ext (Finset.map_injective Fin.valEmbedding h)

variable (R : Type*) [CommRing R]

/-- Rectangular matrix of an exterior operator between two finite levels. -/
noncomputable def entry {Q a b : ℕ} (f : Fock R →ₗ[R] Fock R)
    (β : Level Q b) (α : Level Q a) : R :=
  (Fock.basis R).repr (f (Fock.basis R (indexSet α))) (indexSet β)

private theorem level_expansion {Q b : ℕ} (x : Fock R)
    (hx : x = 0 ∨ ∃ (γ : Level Q b) (c : R), x = c • Fock.basis R (indexSet γ)) :
    ∑ γ : Level Q b, (Fock.basis R).repr x (indexSet γ) • Fock.basis R (indexSet γ) = x := by
  classical
  rcases hx with rfl | ⟨δ, c, rfl⟩
  · simp
  · rw [Finset.sum_eq_single δ]
    · simp
    · intro γ _ hγ
      simp [Ne.symm (indexSet_injective.ne hγ)]
    · simp

private theorem create_level {Q b : ℕ} (i : Fin Q) (α : Level Q b) :
    Fock.create R i (Fock.basis R (indexSet α)) = 0 ∨
      ∃ (γ : Level Q (b+1)) (c : R),
        Fock.create R i (Fock.basis R (indexSet α)) = c • Fock.basis R (indexSet γ) := by
  classical
  by_cases hi : i ∈ α.val
  · exact Or.inl (Fock.create_basis_of_mem R ((mem_indexSet α i).2 hi))
  · obtain ⟨ε, hε⟩ := Fock.create_basis_of_not_mem R (i := i.val) ((mem_indexSet α i).not.mpr hi)
    let γ : Level Q (b+1) := ⟨insert i α.val, by rw [Finset.card_insert_of_notMem hi, α.property]⟩
    have hγ : indexSet γ = insert i.val (indexSet α) := Finset.map_insert Fin.valEmbedding _ _
    exact Or.inr ⟨γ, (ε.val : R), by rw [hγ, hε, Units.smul_def, Int.cast_smul_eq_zsmul]⟩

private theorem contract_level {Q b : ℕ} (i : Fin Q) (α : Level Q b) :
    Fock.contract R i (Fock.basis R (indexSet α)) = 0 ∨
      ∃ (γ : Level Q (b-1)) (c : R),
        Fock.contract R i (Fock.basis R (indexSet α)) = c • Fock.basis R (indexSet γ) := by
  classical
  by_cases hi : i ∈ α.val
  · obtain ⟨ε, hε⟩ := Fock.contract_basis_of_mem R ((mem_indexSet α i).2 hi)
    let γ : Level Q (b-1) := ⟨α.val.erase i, by rw [Finset.card_erase_of_mem hi, α.property]⟩
    have hγ : indexSet γ = (indexSet α).erase i.val := by
      exact Finset.map_erase Fin.valEmbedding α.val i
    exact Or.inr ⟨γ, (ε.val : R), by rw [hγ, hε, Units.smul_def, Int.cast_smul_eq_zsmul]⟩
  · exact Or.inl (Fock.contract_basis_of_not_mem R ((mem_indexSet α i).not.mpr hi))

private theorem entry_comp {Q a b c : ℕ} (f g : Fock R →ₗ[R] Fock R)
    (β : Level Q c) (α : Level Q a)
    (hg : g (Fock.basis R (indexSet α)) = 0 ∨
      ∃ (γ : Level Q b) (r : R), g (Fock.basis R (indexSet α)) = r • Fock.basis R (indexSet γ)) :
    ∑ γ : Level Q b, entry R f β γ * entry R g γ α =
      entry R (f.comp g) β α := by
  let ev := ((Fock.basis R).coord (indexSet β)).comp f
  have hx := congrArg ev (level_expansion R _ hg)
  simp only [map_sum, map_smul, smul_eq_mul] at hx
  simpa only [entry, ev, LinearMap.comp_apply, Module.Basis.coord_apply, mul_comm] using hx

/-- Equation (A.1) in the bounded subset basis. The two intermediate sums
have `Q.choose (b+1)` and `Q.choose (b-1)` terms, respectively. -/
theorem matrix_car {Q b : ℕ} (i j : Fin Q) (β α : Level Q b) :
    (∑ γ : Level Q (b+1), entry R (Fock.contract R j) β γ * entry R (Fock.create R i) γ α) +
    (∑ γ : Level Q (b-1), entry R (Fock.create R i) β γ * entry R (Fock.contract R j) γ α) =
      if i = j ∧ β = α then 1 else 0 := by
  classical
  rw [entry_comp R _ _ _ _ (create_level R i α), entry_comp R _ _ _ _ (contract_level R j α)]
  have h := congrArg ((Fock.basis R).coord (indexSet β))
    (Fock.contract_create_add_create_contract R j i (Fock.basis R (indexSet α)))
  simp only [map_add, Module.Basis.coord_apply] at h
  unfold entry
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h]
  by_cases hij : i = j
  · subst j
    simp [Finsupp.single_apply, indexSet_injective.eq_iff, eq_comm]
  · simp [Ne.symm (Fin.val_injective.ne hij), hij]

/-- A single pair of integer matrix families gives (A.1) after base change
to any commutative ring, including fields of characteristic two. -/
theorem int_matrix_car {Q b : ℕ} (i j : Fin Q) (β α : Level Q b) :
    (∑ γ : Level Q (b+1), (entry ℤ (Fock.contract ℤ j) β γ : R) *
      (entry ℤ (Fock.create ℤ i) γ α : R)) +
    (∑ γ : Level Q (b-1), (entry ℤ (Fock.create ℤ i) β γ : R) *
      (entry ℤ (Fock.contract ℤ j) γ α : R)) =
      if i = j ∧ β = α then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (matrix_car ℤ i j β α)
  simpa only [map_add, map_sum, map_mul, apply_ite, map_one, map_zero, Int.coe_castRingHom] using h

/-- Contracting the old marked index against the two orders in (A.1) gives
the original coefficient at the new index times the identity wire. -/
theorem matrix_car_apply {Q b : ℕ} (T : Fin Q → R) (i : Fin Q) (β α : Level Q b) :
    (∑ j, T j * ∑ γ : Level Q (b+1),
      entry R (Fock.contract R j) β γ * entry R (Fock.create R i) γ α) +
    (∑ j, T j * ∑ γ : Level Q (b-1),
      entry R (Fock.create R i) β γ * entry R (Fock.contract R j) γ α) =
      if β = α then T i else 0 := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, matrix_car]
  by_cases h : β = α <;> simp [h]

end WireTensor.ExteriorLevels

end VPVNP
end Computability
end OAI
