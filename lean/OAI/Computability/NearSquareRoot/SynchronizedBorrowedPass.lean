import OAI.Computability.NearSquareRoot.SynchronizedBorrowing
import OAI.Computability.NearSquareRoot.SynchronizedComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Applying restored transforms on borrowed coordinates. Each batch may borrow
from earlier or later batches. The restored output on such a cell is its value
at entry to the current batch. This gives an exact full-fiber pass in 15 batches.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBorrowing

variable {a b r : ℕ} {R : Type*}

private theorem active_batch (hb : 8 ≤ b) (j : Fin 15) (i : Fin (size b j)) :
    batchOf hb (activeFiber (batchFits b j) i) = j := by
  apply batchOf_eq_of_mem
  · change first b j ≤ first b j + i.val
    omega
  · exact Nat.add_lt_add_left i.isLt _

private theorem exists_active (hb : 8 ≤ b) (i : Fin b) :
    ∃ p : Fin (size b (batchOf hb i)), activeFiber (batchFits b _) p = i := by
  obtain ⟨hlo, hhi⟩ := mem_batchOf hb i
  refine ⟨⟨i.val - first b (batchOf hb i), by omega⟩, Fin.ext ?_⟩
  change first b (batchOf hb i) + (i.val - first b (batchOf hb i)) = i.val
  omega

/-- Restrict an array to the indicated disjoint placements, apply independent
restored row operations, then write the results back. Cells outside all
placements retain their input values. -/
noncomputable def placedBatch (hr : 2*r ≤ 8*a) (j : Fin 15)
    (U : (Fin a → R) → Fin a → R) (x : Fin b × Fin a → R) : Fin b × Fin a → R :=
  let e := batchPlacement b j hr
  Function.extend e (fun p ↦ match p.2 with
    | Sum.inl t => U (fun u ↦ x (e (p.1, Sum.inl u))) t
    | Sum.inr t => x (e (p.1, Sum.inr t))) x

theorem placedBatch_apply (hb : 8 ≤ b) (hr : 2*r ≤ 8*a) (j : Fin 15)
    (U : (Fin a → R) → Fin a → R) (x : Fin b × Fin a → R) (i : Fin b) (t : Fin a) :
    placedBatch hr j U x (i, t) =
      if batchOf hb i = j then U (fun u ↦ x (i, u)) t else x (i, t) := by
  unfold placedBatch
  generalize he : batchPlacement b j hr = e
  by_cases hi : batchOf hb i = j
  · rw [ite_eq_left hi]
    have ht := exists_active hb i
    rw [hi] at ht
    obtain ⟨p, rfl⟩ := ht
    have he₁ (t' : Fin a) : e (p, Sum.inl t') = (activeFiber (batchFits b j) p, t') := he ▸ rfl
    rw [← he₁ t, e.injective.extend_apply]
    simp only [he₁]
  · rw [ite_eq_right hi]
    by_cases hmem : (i,t) ∈ Set.range e
    · obtain ⟨⟨p, c | c⟩, hp⟩ := hmem
      · have he₁ : e (p, Sum.inl c) = (activeFiber (batchFits b j) p, c) := he ▸ rfl
        have hf : activeFiber (batchFits b j) p = i := congrArg Prod.fst (he₁.symm.trans hp)
        exact (hi (hf ▸ active_batch hb j p)).elim
      · rw [← hp, e.injective.extend_apply]
    · exact Function.extend_apply' _ _ _ hmem

/-- Applying any sublist of distinct batches transforms each listed row once. -/
theorem fold_placedBatch (hb : 8 ≤ b) (hr : 2*r ≤ 8*a) (U : (Fin a → R) → Fin a → R)
    (x : Fin b × Fin a → R) (js : List (Fin 15)) (hn : js.Nodup) (i : Fin b) (t : Fin a) :
    js.foldr (placedBatch hr · U) x (i,t) =
      if batchOf hb i ∈ js then U (fun u ↦ x (i,u)) t else x (i,t) := by
  induction js generalizing t with
  | nil => simp
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hn
    rw [List.foldr_cons, placedBatch_apply hb]
    by_cases h : batchOf hb i = j
    · simp only [h, ite_true, List.mem_cons, true_or]
      congr 1
      funext u
      simpa [h, hj] using ih hjs u
    · simp [h, ih hjs]

/-- Running the fifteen physical batches completes the transform on every fiber. -/
theorem full_placedBatch (hb : 8 ≤ b) (hr : 2*r ≤ 8*a) (U : (Fin a → R) → Fin a → R)
    (x : Fin b × Fin a → R) :
    (List.finRange 15).foldr (placedBatch hr · U) x = fun p ↦ U (fun t ↦ x (p.1,t)) p.2 := by
  funext ⟨i,t⟩
  rw [fold_placedBatch hb hr U x _ (List.nodup_finRange _)]
  simp

section Matrix

open Matrix

/-- Coordinate inclusion of the primary cells of a row in its borrowed workspace. -/
def rowInclusion (a c : ℕ) : Matrix (Fin a ⊕ Fin c) (Fin a) ℂ := fromRows 1 0

theorem extend_rowInclusion (U : Matrix (Fin a) (Fin a) ℂ) (c : ℕ) :
    ShortFourier.extend (rowInclusion a c) U = fromBlocks U 0 0 1 := by
  rw [ShortFourier.extend, rowInclusion, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
    fromRows_mul_fromCols, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul]
  rw [← fromBlocks_one (l := Fin a) (m := Fin c), fromBlocks_add]
  simp

/-- Apply an arbitrary short matrix on the placed workspace of each active
fiber. The matrix may mix primary and borrowed coordinates. -/
noncomputable def placedMatrix (hr : 2*r ≤ 8*a) (j : Fin 15)
    (V : Matrix (Fin a ⊕ Fin (2*r-a)) (Fin a ⊕ Fin (2*r-a)) ℂ)
    (x : Fin b × Fin a → ℂ) : Fin b × Fin a → ℂ :=
  let e := batchPlacement b j hr
  Function.extend e (fun p ↦ (V *ᵥ (fun t ↦ x (e (p.1, t)))) p.2) x

/-- Consecutive local layers can be executed at the same placements. This
also covers arbitrary intermediate contents of the borrowed cells. -/
theorem placedMatrix_mul (hr : 2*r ≤ 8*a) (j : Fin 15)
    (M N : Matrix (Fin a ⊕ Fin (2*r-a)) (Fin a ⊕ Fin (2*r-a)) ℂ) :
    placedMatrix (b := b) hr j (M * N) =
      placedMatrix hr j M ∘ placedMatrix hr j N := by
  funext x p
  set e := batchPlacement b j hr
  have inside (V : Matrix (Fin a ⊕ Fin (2*r-a)) (Fin a ⊕ Fin (2*r-a)) ℂ) (y)
      (s : Fin (size b j)) (t) :
      placedMatrix hr j V y (e (s,t)) = (V *ᵥ fun u ↦ y (e (s,u))) t := by
    unfold placedMatrix
    rw [show batchPlacement b j hr = e from rfl, e.injective.extend_apply]
  have outside (V : Matrix (Fin a ⊕ Fin (2*r-a)) (Fin a ⊕ Fin (2*r-a)) ℂ) (y)
      (hp : p ∉ Set.range e) : placedMatrix hr j V y p = y p := by
    unfold placedMatrix
    rw [show batchPlacement b j hr = e from rfl]
    exact Function.extend_apply' _ _ _ hp
  by_cases hp : p ∈ Set.range e
  · obtain ⟨⟨s,t⟩, rfl⟩ := hp
    simp only [Function.comp_apply, inside, ← Matrix.mulVec_mulVec]
  · simp only [Function.comp_apply, outside _ _ hp]

/-- A matrix that restores the complement agrees, on each physical batch,
with a transform of the primary cells and exact return of all borrowed values. -/
theorem placedMatrix_extend (hr : 2*r ≤ 8*a) (j : Fin 15) (U : Matrix (Fin a) (Fin a) ℂ) :
    placedMatrix (b := b) hr j (ShortFourier.extend (rowInclusion a (2*r-a)) U) =
      placedBatch hr j (U *ᵥ ·) := by
  funext x
  rw [extend_rowInclusion]
  unfold placedMatrix placedBatch
  apply congrArg (fun f ↦ Function.extend (batchPlacement b j hr) f x)
  funext ⟨p, t⟩
  cases t <;> simp [fromBlocks_mulVec, Function.comp_def]

/-- The full batch schedule with a proved restored short matrix realizes the
specified matrix on every physical fiber, even when borrowed cells contain
earlier results. -/
theorem full_placedMatrix (hb : 8 ≤ b) (hr : 2*r ≤ 8*a)
    {V : Matrix (Fin a ⊕ Fin (2*r-a)) (Fin a ⊕ Fin (2*r-a)) ℂ}
    (U : Matrix (Fin a) (Fin a) ℂ) (h : V = ShortFourier.extend (rowInclusion a (2*r-a)) U)
    (x : Fin b × Fin a → ℂ) :
    (List.finRange 15).foldr (placedMatrix hr · V) x = fun p ↦ (U *ᵥ (fun t ↦ x (p.1,t))) p.2 := by
  rw [h]
  simp only [placedMatrix_extend]
  exact full_placedBatch hb hr _ x

end Matrix

end SynchronizedBorrowing

end NearSquareRoot
end Computability
end OAI
