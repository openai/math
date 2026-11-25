import OAI.LinearAlgebra.SpectralBooks.GridPlacementWidth

/-! # The occupied labels for the private and joint doubled-grid tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical

section

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Every doubled grid in positive dimension has a private noncentral site. -/
instance noncentralGrid_nonempty [Nonempty ι] : Nonempty (NoncentralGrid ι n) := by
  let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))
  have hz : z ∈ coordinateCubeCorners ι 1 :=
    mem_coordinateCubeCorners_iff.mpr (fun _ ↦ Or.inr rfl)
  refine ⟨⟨⟨(2 : ℝ) • z, double_corner_mem_cubeGrid n hz⟩, ?_⟩⟩
  intro h
  have := congrArg (fun x : EuclideanSpace ℝ ι ↦ x (Classical.arbitrary ι)) h
  norm_num [PiLp.smul_apply, z] at this

@[simp] theorem gridPlacement_center (page : Option Bool) :
    gridPlacement (n := n) (ι := ι) page gridCenter = 0 := rfl

@[simp] theorem gridPlacement_left (page : Option Bool) (b : NoncentralGrid ι n) :
    gridPlacement page (.inl (.inr (.inl b)) : DoubledGridSite ι n) =
      if page = none ∨ page = some false then (1 / 2 : ℝ) • (b.val : EuclideanSpace ℝ ι) else 0 := rfl

@[simp] theorem gridPlacement_right (page : Option Bool) (c : NoncentralGrid ι n) :
    gridPlacement page (.inl (.inr (.inr c)) : DoubledGridSite ι n) =
      if page = none ∨ page = some true then (1 / 2 : ℝ) • (c.val : EuclideanSpace ℝ ι) else 0 := rfl

@[simp] theorem gridPlacement_aux (page : Option Bool) (z : coordinateCubeCorners ι 1) :
    gridPlacement (n := n) page (.inr z) = if page = none then z.val else 0 := rfl

theorem mem_gridLabels_false_iff {s : DoubledGridSite ι n} :
    s ∈ gridLabels ι n false ↔ s = gridCenter ∨ ∃ b : NoncentralGrid ι n, s = .inl (.inr (.inl b)) := by
  simp only [gridLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : (x : EuclideanSpace ℝ ι) = 0
    · exact Or.inl (by simp [gridLabel, hx])
    · exact Or.inr ⟨⟨x, hx⟩, by simp [gridLabel, hx]⟩
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨⟨0, zero_mem_cubeGrid ι n⟩, by simp [gridLabel]⟩
    · exact ⟨b.val, by simp [gridLabel, b.property]⟩

theorem mem_gridLabels_true_iff {s : DoubledGridSite ι n} :
    s ∈ gridLabels ι n true ↔ s = gridCenter ∨ ∃ c : NoncentralGrid ι n, s = .inl (.inr (.inr c)) := by
  simp only [gridLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : (x : EuclideanSpace ℝ ι) = 0
    · exact Or.inl (by simp [gridLabel, hx])
    · exact Or.inr ⟨⟨x, hx⟩, by simp [gridLabel, hx]⟩
  · rintro (rfl | ⟨c, rfl⟩)
    · exact ⟨⟨0, zero_mem_cubeGrid ι n⟩, by simp [gridLabel]⟩
    · exact ⟨c.val, by simp [gridLabel, c.property]⟩

theorem mem_gridLabels_union_iff {s : DoubledGridSite ι n} :
    s ∈ gridLabels ι n false ∪ gridLabels ι n true ↔ ∃ t, s = .inl t := by
  rw [Finset.mem_union, mem_gridLabels_false_iff, mem_gridLabels_true_iff]
  rcases s with ((⟨⟩ | (b | c)) | o) <;> simp [gridCenter]

end

end SpectralBooks
end LinearAlgebra
end OAI
