import OAI.Hierarchy.ProbeStageAllocation

namespace OAI
/-! # Candidate masks, permanent full colors, and amortized fallback scans -/

namespace Hierarchy.ProbeStage

open Finset
open scoped BigOperators

abbrev MaskIndex (B : ℕ) := Fin (B^2) × Fin (B^2)

/-- A mask has a set bit exactly at a position whose color is available at both blocks. -/
def freeBits {B ℓ : ℕ} (row : Fin ℓ → Fin B) (good : Finset (Fin B)) : Finset (Fin ℓ) :=
  univ.filter fun t => row t ∈ good

def maskedChoice {B ℓ : ℕ} (pos : 0<B) (row : Fin ℓ → Fin B) (good : Finset (Fin B)) : Fin B :=
  let bits := freeBits row good
  if h : bits.Nonempty then row (bits.min' h) else Greedy.first pos good

theorem maskedChoice_mem {B ℓ : ℕ} (pos : 0<B) (row : Fin ℓ → Fin B) {good : Finset (Fin B)}
    (hgood : good.Nonempty) : maskedChoice pos row good ∈ good := by
  dsimp only [maskedChoice]
  split
  next h =>
    have hm := min'_mem (freeBits row good) h
    exact (mem_filter.mp hm).2
  next => exact Greedy.first_mem pos hgood

/-- The fixed residue pair used to select the mask row for an actual tile. -/
def maskIndex {n m B : ℕ} {G : Type*} (p : Tiles (Fin n) G m) (pos : 0<B) (i : Fin n) : MaskIndex B :=
  (⟨((decode m B pos (p.input i)).2.val) % (B^2), Nat.mod_lt _ (pow_pos pos _)⟩,
   ⟨((decode m B pos (p.output i)).2.val) % (B^2), Nat.mod_lt _ (pow_pos pos _)⟩)

/-- The deterministic allocation used by a fixed candidate-string table. -/
noncomputable def allocateMasked {n m B ℓ : ℕ} {G : Type*} (p : Tiles (Fin n) G m) (pos : 0<B)
    (strings : MaskIndex B → Fin ℓ → Fin B) : Allocation B (leftBlock p pos) (rightBlock p pos) :=
  allocateWith p pos (fun i => maskedChoice pos (strings (maskIndex p pos i)))
    (fun _ _ => maskedChoice_mem pos _)

namespace Greedy

variable {n B : ℕ} {L H : Type*} [DecidableEq L] [DecidableEq H]

theorem colors_stable (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (left : Fin n → L) (right : Fin n → H) {k t : ℕ} (h : k ≤ t) (i : Fin n) (hi : i.val < k) :
    colors pos pick left right t i = colors pos pick left right k i := by
  induction t, h using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [colors]
    by_cases htn : t<n
    · have hne : i ≠ ⟨t,htn⟩ := fun e => by have hh := congrArg Fin.val e; dsimp at hh; omega
      simpa [htn, Function.update_of_ne hne] using ih
    · simpa [htn] using ih

theorem load_final_ge (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (left : Fin n → L) (right : Fin n → H) {E : Type*} [DecidableEq E] (key : Fin n → E)
    {k : ℕ} (hk : k ≤ n) (x : E) (c : Fin B) :
    load key (before n k) (colors pos pick left right k) x c ≤ load key univ (colors pos pick left right n) x c := by
  apply card_le_card
  intro i hi
  obtain ⟨hd,hkey,hc⟩ := mem_filter.mp hi
  have hbefore : i.val<k := (mem_filter.mp hd).2
  exact mem_filter.mpr ⟨mem_univ _,hkey,(colors_stable pos pick left right hk i hbefore).trans hc⟩

def fullColors {E : Type*} [DecidableEq E] (key : Fin n → E) (color : Fin n → Fin B) (x : E) :=
  univ.filter fun c => quota B ≤ load key univ color x c

theorem fullColors_card {E : Type*} [DecidableEq E] (pos : 0 < B) (key : Fin n → E)
    (color : Fin n → Fin B) (x : E) (cap : (univ.filter fun i => key i=x).card ≤ blockSize B) :
    4*(fullColors key color x).card ≤ B := by
  let S := fullColors key color x
  have h₁ : ∑ q ∈ S, quota B ≤ ∑ q ∈ S, load key univ color x q :=
    sum_le_sum (fun q hq => (mem_filter.mp hq).2)
  have h₂ : ∑ q ∈ S, load key univ color x q ≤ ∑ q, load key univ color x q :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => by omega)
  simp only [sum_const, nsmul_eq_mul] at h₁
  rw [sum_load] at h₂
  have h₃ := (h₁.trans h₂).trans cap
  have h₄ : (4*S.card)*B^8 ≤ B*B^8 := by simpa [quota,blockSize,pow_succ B 8,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h₃
  exact Nat.le_of_mul_le_mul_right h₄ (pow_pos pos _)

end Greedy

/-- If a row misses every currently free color, one endpoint's final set of full colors
covers at least half of the row, counting repeated occurrences. -/
theorem absent_hits_half {B ℓ : ℕ} (row : Fin ℓ → Fin B) (left right : Finset (Fin B))
    (miss : ∀ t, row t ∈ left ∨ row t ∈ right) :
    ℓ ≤ 2*(univ.filter fun t => row t ∈ left).card ∨ ℓ ≤ 2*(univ.filter fun t => row t ∈ right).card := by
  let l := univ.filter fun t => row t ∈ left
  let r := univ.filter fun t => row t ∈ right
  have hu : l ∪ r = univ := by ext t; simpa [l,r] using miss t
  have hc := Finset.card_union_le l r
  rw [hu,card_univ,Fintype.card_fin] at hc
  change ℓ ≤ 2*l.card ∨ ℓ ≤ 2*r.card
  omega

/-- A missed candidate row in the actual scan is permanently charged to one of the two
endpoint masks, even if more colors become full later. -/
theorem fallback_charge {B ℓ n : ℕ} {L H : Type*} [DecidableEq L] [DecidableEq H]
    (pos : 0<B) (left : Fin n → L) (right : Fin n → H) (pick : Fin n → Finset (Fin B) → Fin B)
    (rows : Fin n → Fin ℓ → Fin B) (i : Fin n)
    (miss : freeBits (rows i) (Greedy.available left right (Greedy.before n i.val) (Greedy.colors pos pick left right i.val) i) = ∅) :
    let final := Greedy.colors pos pick left right n
    ℓ ≤ 2*(univ.filter fun t => rows i t ∈ Greedy.fullColors left final (left i)).card ∨
    ℓ ≤ 2*(univ.filter fun t => rows i t ∈ Greedy.fullColors right final (right i)).card := by
  apply absent_hits_half
  intro t
  have no : rows i t ∉ Greedy.available left right (Greedy.before n i.val) (Greedy.colors pos pick left right i.val) i := by
    intro h
    have : t ∈ freeBits (rows i) _ := mem_filter.mpr ⟨mem_univ _,h⟩
    simp [miss] at this
  simp only [Greedy.available,mem_filter,mem_univ,true_and,not_and_or,not_lt] at no
  rcases no with hl|hr
  · exact Or.inl (mem_filter.mpr ⟨mem_univ _,hl.trans (Greedy.load_final_ge pos pick left right left i.isLt.le _ _)⟩)
  · exact Or.inr (mem_filter.mpr ⟨mem_univ _,hr.trans (Greedy.load_final_ge pos pick left right right i.isLt.le _ _)⟩)

end Hierarchy.ProbeStage

end OAI
