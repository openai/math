import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinate configurations in the binary Grassmannian

Pair the coordinates in the ambient space and choose one from each pair. The
sum dimension of two resulting planes is the common plane dimension plus the
Hamming distance between the choices. Flipping two disjoint blocks of pairs
gives the quadrilateral used in the averaging argument of Lemma 5.3.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open scoped symmDiff

variable {m : ℕ}

private def selectedRow (A : Finset (Fin m)) (i : Fin m) : Fin 2 :=
  if i ∈ A then 1 else 0

private def rowEmbedding (A : Finset (Fin m)) : Fin m ↪ Fin 2 × Fin m :=
  ⟨fun i ↦ (selectedRow A i, i), fun _ _ h ↦ congrArg Prod.snd h⟩

private def rows (A : Finset (Fin m)) : Finset (Fin 2 × Fin m) :=
  Finset.univ.map (rowEmbedding A)

private lemma mem_rows (A : Finset (Fin m)) (j : Fin 2) (i : Fin m) :
    (j, i) ∈ rows A ↔ selectedRow A i = j := by
  rw [rows, Finset.mem_map]
  constructor
  · rintro ⟨k, _, hk⟩
    obtain ⟨hj, rfl⟩ := Prod.mk.inj hk
    exact hj
  · rintro rfl
    exact ⟨i, Finset.mem_univ _, rfl⟩

private lemma rows_sdiff (A B : Finset (Fin m)) :
    rows A \ rows B = (A ∆ B).map (rowEmbedding A) := by
  ext ⟨j, i⟩
  simp only [Finset.mem_sdiff, mem_rows, Finset.mem_map, rowEmbedding,
    Function.Embedding.coeFn_mk, Prod.mk.injEq,
    Finset.mem_symmDiff, selectedRow]
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [ha, hb] <;> rintro rfl <;> decide

private def chosenCoordinates (A : Finset (Fin m)) : Finset (Fin (2 * m)) :=
  (rows A).map finProdFinEquiv.toEmbedding

/-- The coordinate plane spanned by row one in each marked pair and row zero
in every other pair. -/
noncomputable def cubePlane (A : Finset (Fin m)) : Plane m :=
  ⟨Pi.spanSubset (ZMod 2) (chosenCoordinates A), by
    rw [Pi.dim_spanSubset, Set.ncard_coe_finset]
    simp [chosenCoordinates, rows]⟩

/-- In the coordinate cube the Grassmann pair type counts exactly the pairs of
coordinates on which the two choices differ. -/
theorem hasType_cubePlane (A B : Finset (Fin m)) :
    HasType (A ∆ B).card (cubePlane A) (cubePlane B) := by
  change Module.finrank (ZMod 2) (Pi.spanSubset (ZMod 2) (chosenCoordinates A) ⊔
    Pi.spanSubset (ZMod 2) (chosenCoordinates B) : Submodule (ZMod 2) (Space m)) = _
  have hsup : Pi.spanSubset (ZMod 2) (chosenCoordinates A) ⊔
      Pi.spanSubset (ZMod 2) (chosenCoordinates B) =
      Pi.spanSubset (ZMod 2) (↑(chosenCoordinates A ∪ chosenCoordinates B) : Set (Fin (2 * m))) := by
    simp [Pi.spanSubset, Set.image_union, Submodule.span_union]
  rw [hsup, Pi.dim_spanSubset, Set.ncard_coe_finset]
  rw [chosenCoordinates, chosenCoordinates, ← Finset.map_union, Finset.card_map,
    ← Finset.card_sdiff_add_card, rows_sdiff]
  simp [rows, Nat.add_comm]

/-- The face on the first `ℓ` coordinate pairs. For `ℓ < m` its pair types
are all strictly below `m`, as required in the equality argument of Lemma 5.3. -/
theorem exists_cube_face {ℓ : ℕ} (h : ℓ ≤ m) :
    ∃ face : Finset (Fin ℓ) → Plane m,
      ∀ A B, HasType (A ∆ B).card (face A) (face B) := by
  let e := Fin.castLEEmb h
  refine ⟨fun A ↦ cubePlane (A.map e), fun A B ↦ ?_⟩
  have hd : (A ∆ B).map e = (A.map e) ∆ (B.map e) := by
    simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]
  simpa only [← hd, Finset.card_map] using hasType_cubePlane (A.map e) (B.map e)

/-- Seed quadrilaterals for the Grassmannian averaging argument. Their
opposite sides have types `r` and `s`, and both diagonals have type `r + s`. -/
theorem exists_square {m r s : ℕ} (h : r + s ≤ m) :
    ∃ a b c d : Plane m,
      HasType r a b ∧ HasType s b c ∧ HasType r c d ∧ HasType s d a ∧
      HasType (r + s) a c ∧ HasType (r + s) b d := by
  obtain ⟨R, _, hR⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (n := r) (by simp; omega)
  obtain ⟨S, hSR, hS⟩ := Finset.exists_subset_card_eq
    (s := Rᶜ) (n := s) (by rw [Finset.card_compl, Fintype.card_fin, hR]; omega)
  have hdis : Disjoint R S := Finset.disjoint_left.mpr fun i hi his ↦
    Finset.mem_compl.mp (hSR his) hi
  have hRS : (R ∆ S).card = r + s := by
    rw [Finset.symmDiff_eq_union hdis, Finset.card_union_of_disjoint hdis, hR, hS]
  refine ⟨cubePlane ∅, cubePlane R, cubePlane (R ∆ S), cubePlane S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← Finset.bot_eq_empty, bot_symmDiff, hR] using hasType_cubePlane ∅ R
  · simpa only [symmDiff_symmDiff_cancel_left, hS] using hasType_cubePlane R (R ∆ S)
  · simpa only [symmDiff_symmDiff_cancel_right, hR] using hasType_cubePlane (R ∆ S) S
  · simpa only [← Finset.bot_eq_empty, symmDiff_bot, hS] using hasType_cubePlane S ∅
  · simpa only [← Finset.bot_eq_empty, bot_symmDiff, hRS] using hasType_cubePlane ∅ (R ∆ S)
  · simpa only [hRS] using hasType_cubePlane R S

/-- Every distance type up to the plane dimension occurs. -/
theorem exists_pair {m r : ℕ} (h : r ≤ m) :
    ∃ a b : Plane m, HasType r a b := by
  obtain ⟨a, b, _, _, hab, _⟩ := exists_square (s := 0) (by simpa using h)
  exact ⟨a, b, hab⟩

end Grassmann

end VPVNP
end Computability
end OAI
