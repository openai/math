import OAI.Computability.BorderVNP.CubeMeanExact

/-! # Reindexing live traffic into sparse public row slots

The cell names may be arbitrary public ordinals. Unoccupied rows and absorbed same-cell
cables contribute zero width. The integer scan still returns the same labels when zero-width
rows use dummy endpoint names, including actual crossing cables of width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Finset
open scoped BigOperators

variable {C D I K : Type*} [DecidableEq C] [DecidableEq D] [Fintype I] [Fintype K] {z : ℕ}

/-- Transport both endpoint names into the public numbering. -/
def Traffic.mapCells (e : C → D) : Traffic C → Traffic D
  | .cable a b w => .cable (e a) (e b) w
  | .delivery a w => .delivery (e a) w

/-- A zero-width descriptor may carry different dummy endpoint names. -/
def rowEquivalent (a b : Traffic C) : Prop := a = b ∨ a.width = 0 ∧ b.width = 0

/-- Indexed live rows and zero padding characterize the public input needed by the chooser. -/
structure RowPlacement (rows : I → Traffic C) (raw : K → Traffic D) (cells : C ≃ D) (slots : I ↪ K) : Prop where
  /-- The slot carries this row's width and named endpoints whenever its width is positive. -/
  live : ∀ i, rowEquivalent (raw (slots i)) ((rows i).mapCells cells)
  /-- Every other slot has zero width, regardless of its endpoint names. -/
  unused : ∀ k ∉ Set.range slots, (raw k).width = 0

private theorem update_map (cells : C ≃ D) (x : C → Fin (z+1)) (c : C) (u : Fin (z+1)) :
    (Function.update x c u) ∘ cells.symm = Function.update (x ∘ cells.symm) (cells c) u := by
  funext k
  obtain ⟨a,rfl⟩ := cells.surjective k
  by_cases h : a = c
  · subst a; simp
  · simp [Function.update_of_ne h,show cells a ≠ cells c from cells.injective.ne h]

private theorem factor_map (cells : C ≃ D) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    factor (s.map cells.toEmbedding) (x ∘ cells.symm) (cells c) v = factor s x c v := by
  simp [factor]

private theorem rowNat_map (cells : C ≃ D) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) (r : Traffic C) :
    rowNat (s.map cells.toEmbedding) (x ∘ cells.symm) j (r.mapCells cells) = rowNat s x j r := by
  rcases j with ⟨u,v⟩|u <;> cases r <;> simp [rowNat,Traffic.mapCells,factor_map]

private theorem rowNat_zero (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) {r : Traffic C} (h : r.width = 0) :
    rowNat s x j r = 0 := Nat.eq_zero_of_le_zero (by simpa [h] using rowNat_le s x j r)

private theorem sum_slots (slots : I ↪ K) (f : K → ℕ) (g : I → ℕ) (live : ∀ i, f (slots i) = g i)
    (unused : ∀ k ∉ Set.range slots, f k = 0) : ∑ k, f k = ∑ i, g i := by
  classical
  rw [← sum_subset (subset_univ (univ.map slots)) (fun k _ h => unused k (by
    rintro ⟨i,rfl⟩; exact h (mem_map.mpr ⟨i,mem_univ _,rfl⟩))),sum_map]
  exact sum_congr rfl fun i _ => live i

/-- Sparse row packing and public cell renaming preserve every scaled conditional mean. -/
theorem RowPlacement.cache_eq {rows : I → Traffic C} {raw : K → Traffic D} {cells : C ≃ D} {slots : I ↪ K}
    (p : RowPlacement rows raw cells slots) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) :
    cache raw (s.map cells.toEmbedding) (x ∘ cells.symm) j = cache rows s x j := by
  apply sum_slots slots
  · intro i
    rcases p.live i with same|⟨hraw,htyped⟩
    · rw [same,rowNat_map]
    · rw [rowNat_zero _ _ _ hraw,← rowNat_map cells s x j (rows i),rowNat_zero _ _ _ htyped]
  · intro k hk
    exact rowNat_zero _ _ _ (p.unused k hk)

private theorem RowPlacement.choose {rows : I → Traffic C} {raw : K → Traffic D} {cells : C ≃ D} {slots : I ↪ K}
    (p : RowPlacement rows raw cells slots) (s : Finset C) (x : C → Fin (z+1)) (c : C) :
    firstMinimum (scoreNat raw (s.map cells.toEmbedding) (x ∘ cells.symm) (cells c)) =
      firstMinimum (scoreNat rows s x c) := by
  obtain ⟨off,h⟩ := exists_offset rows s x c
  obtain ⟨off',h'⟩ := exists_offset raw (s.map cells.toEmbedding) (x ∘ cells.symm) (cells c)
  have eq (v : Fin (z+1)) : scoreNat raw (s.map cells.toEmbedding) (x ∘ cells.symm) (cells c) v + off' =
      scoreNat rows s x c v + off := by
    have next (j : Bins z) := p.cache_eq (insert c s) (Function.update x c v) j
    simp only [map_insert,Equiv.coe_toEmbedding,update_map] at next
    rw [h' v,h v]
    simp only [p.cache_eq,next]
  apply firstMinimum_of_compare
  intro u v
  have := eq u
  have := eq v
  omega

/-- Visiting the corresponding public cells in the same order produces identical
labels under the given renaming. -/
theorem RowPlacement.scan {rows : I → Traffic C} {raw : K → Traffic D} {cells : C ≃ D} {slots : I ↪ K}
    (p : RowPlacement rows raw cells slots) (cs : List C) (s : Finset C) (x : C → Fin (z+1)) :
    scanNat raw (cs.map cells) (s.map cells.toEmbedding) (x ∘ cells.symm) (cache raw (s.map cells.toEmbedding) (x ∘ cells.symm)) =
      (scanNat rows cs s x (cache rows s x)) ∘ cells.symm := by
  induction cs generalizing s x with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c ∈ s
    · simpa only [List.map_cons,scanNat,mem_map_equiv,Equiv.symm_apply_apply,ite_eq_left hc] using ih s x
    · have sel := p.choose s x c
      unfold scoreNat at sel
      simp only [List.map_cons,scanNat,mem_map_equiv,Equiv.symm_apply_apply,ite_eq_right hc,sel,commit_cache]
      simpa only [map_insert,Equiv.coe_toEmbedding,update_map] using
        ih (insert c s) (Function.update x c (firstMinimum (candidate rows s x c (cache rows s x))))

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
