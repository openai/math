import OAI.Computability.BorderVNP.PackedCellAddresses
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-! # Compact bank size is charged to the actual incident records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing Shortening Finset
open scoped Classical

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C)

private theorem filter_sum {A : Type*} [Fintype A] (p : A → Prop) (f : A → ℕ) :
    (∑ t : {t // p t}, f t.val) = ∑ t, if p t then f t else 0 := by
  rw [← sum_filter, sum_subtype (p := p) _ (fun _ => by simp) f]

/-- Summing both endpoint widths counts every internal wire twice and every crossing
endpoint once. All attached port widths occur once. -/
theorem incidence_width :
    guessedSize N cell c + suppliedSize N cell c + guessedSize N cell c =
    testedWidth N.width (fun e => cell (N.src e) = c) +
    testedWidth N.width (fun e => cell (N.dst e) = c) +
    testedWidth bits (fun p => cell (N.attach p) = c) := by
  have inside : guessedSize N cell c = ∑ e : N.Edge,
      if cell (N.src e) = c ∧ cell (N.dst e) = c then N.width e else 0 := by
    unfold guessedSize
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro e he
      simp only [Set.mem_range,Subtype.exists,exists_prop,exists_eq_right] at he
      simp [he]
    · intro e
      simp [e.property]
  have crossing : (∑ e : Boundary N cell c, N.width e.val.val) = ∑ e : N.Edge,
      if cell (N.src e) ≠ cell (N.dst e) ∧ (cell (N.src e) = c ∨ cell (N.dst e) = c) then N.width e else 0 := by
    apply Fintype.sum_of_injective (fun e : Boundary N cell c => e.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    · intro e he
      have hn : ¬(cell (N.src e) ≠ cell (N.dst e) ∧ (cell (N.src e) = c ∨ cell (N.dst e) = c)) :=
        fun h => he ⟨⟨⟨e,h.1⟩,h.2⟩,rfl⟩
      simp [hn]
    · intro e
      simp [e.val.property,e.property]
  unfold suppliedSize testedWidth
  simp only [inside,Fintype.sum_sum_type,suppliedWidth,Sum.elim_inl,Sum.elim_inr]
  have portEq := filter_sum (fun p => cell (N.attach p) = c) bits
  rw [crossing,portEq]
  have point (e : N.Edge) :
      (if cell (N.src e) = c ∧ cell (N.dst e) = c then N.width e else 0) +
      (if cell (N.src e) ≠ cell (N.dst e) ∧ (cell (N.src e) = c ∨ cell (N.dst e) = c) then N.width e else 0) +
      (if cell (N.src e) = c ∧ cell (N.dst e) = c then N.width e else 0) =
      (if cell (N.src e) = c then N.width e else 0) + (if cell (N.dst e) = c then N.width e else 0) := by
    by_cases hs : cell (N.src e) = c <;> by_cases hd : cell (N.dst e) = c <;>
      by_cases he : cell (N.src e) = cell (N.dst e) <;> simp_all
  have heq := congrArg (fun f : N.Edge → ℕ => ∑ e, f e) (funext point)
  simp only [sum_add_distrib] at heq
  omega

private theorem mono {A : Type*} [Fintype A] (f : A → ℕ) (p : A → Prop) :
    testedWidth f p ≤ testedWidth (fun x => recordCost true (f x)) p := by
  unfold testedWidth
  apply sum_le_sum
  intro x _
  by_cases h : p x <;> simp [h,recordCost]


/-- All canonical wire and supplied bits fit in the paper's local expanded record count. -/
theorem wireCapacity_le (prior payload : N.Site → ℕ) :
    guessedSize N cell c + suppliedSize N cell c ≤
      localRecords N true prior payload (fun v => cell v = c) := by
  have hs := mono N.width (fun e => cell (N.src e) = c)
  have hd := mono N.width (fun e => cell (N.dst e) = c)
  have hp := mono bits (fun p => cell (N.attach p) = c)
  have he := incidence_width N cell c
  unfold localRecords
  dsimp only
  omega

omit [Fintype P] in
/-- Site staging uses exactly the sum of the required widths on the owning cell. -/
theorem siteSize_eq (aux : N.Site → ℕ) : siteSize N cell c aux = testedWidth aux (fun v => cell v = c) :=
  filter_sum _ _

end Packing.CellAddresses

namespace Packing.CellAddresses

open Crossing Shortening Finset
open scoped Classical

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C)

/-- The sum of per-site staging costs in a cell is controlled by the sum of
the original physical charges in that cell. -/
theorem stagedCapacity_le (aux prior payload : N.Site → ℕ) (K : ℕ)
    (stage : ∀ v, aux v ≤ K*localRecords N true prior payload (fun u => u = v)) :
    guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c ≤
      (K+1)*localRecords N true prior payload (fun v => cell v = c) := by
  let sites := univ.filter (fun v : N.Site => cell v = c)
  have cost := localRecords_near N true prior payload id sites
  have same : (fun u : N.Site => id u ∈ sites) = (fun u => cell u = c) := by
    funext u; apply propext; simp [sites]
  rw [same] at cost
  simp only [id_eq] at cost
  have ha : siteSize N cell c aux = ∑ v ∈ sites, aux v := by
    rw [siteSize_eq,testedWidth,←sum_filter]
  have hb := sum_le_sum (s := sites) (fun v _ => stage v)
  rw [← mul_sum,← cost,← ha] at hb
  have hw := wireCapacity_le N cell c prior payload
  rw [Nat.add_mul,one_mul]
  omega

end Packing.CellAddresses

end BorderVNP
end Computability
end OAI
