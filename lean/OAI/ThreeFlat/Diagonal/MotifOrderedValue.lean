import OAI.ThreeFlat.Diagonal.MotifOrderedCells

namespace OAI
/-! # Uniqueness of all local guesses in a tiled payload expansion -/

namespace ThreeFlat.Diagonal.MotifOrderedCells

open Routing.StableCompaction TraceCircuit
open scoped BigOperators Classical

variable {r e d b : ℕ} {F : Type*} [CommRing F]

abbrev Mask (r e d b : ℕ) := Fin r → (Fin b → Bool) → Fin e → Fin d → Bool
abbrev Table (F : Type*) (r e d b : ℕ) := Fin r → (Fin b → Bool) → (Fin (e*d) → Bool) → F

def observed (rule : Mask r e d b) (head : Fin r → Fin b → Bool) : Fields r e d :=
  fun a i j => rule i (head i) a j

def Supported (M D : Fields r e d) : Prop := ∀ a i j, M a i j = false → D a i j = false

def Good (rule : Mask r e d b) (head : Fin r → Fin b → Bool) (M D : Fields r e d) (i : Fin r) : Prop :=
  ∀ a j, M a i j = rule i (head i) a j ∧ (M a i j = false → D a i j = false)

/-- This single bounded-arity tile table both enforces each candidate bit's
mask and sets every unselected candidate bit to zero. -/
noncomputable def checkedTile (rule : Mask r e d b) (table : Table F r e d b) (i : Fin r)
    (z : Fin (b+(e*d+e*d)) → Bool) : F :=
  let head := fun j : Fin b => z (j.castAdd _)
  let M := fun k : Fin (e*d) => z (Fin.natAdd b (k.castAdd _))
  let D := fun k : Fin (e*d) => z (Fin.natAdd b (Fin.natAdd _ k))
  if ∀ a j, M (finProdFinEquiv (a,j)) = rule i head a j ∧
      (M (finProdFinEquiv (a,j)) = false → D (finProdFinEquiv (a,j)) = false)
    then table i head D else 0

private theorem check_at (rule : Mask r e d b) (table : Table F r e d b)
    (head : Fin r → Fin b → Bool) (M D : Fields r e d) (i : Fin r) :
    checkedTile rule table i (Fin.append (head i) (Fin.append (copyPayload M i) (copyPayload D i))) =
      if Good rule head M D i then table i (head i) (copyPayload D i) else 0 := by
  by_cases good : Good rule head M D i
  · have conditions := good
    unfold Good at conditions
    simp [checkedTile,good,conditions,copyPayload,-Fin.natAdd_eq_addNat]
    intro a j unselected nonzero
    obtain ⟨mask,zero⟩ := conditions a j
    have off := zero (mask.trans unselected)
    simp [off] at nonzero
  · have conditions := good
    unfold Good at conditions
    simp [checkedTile,good,conditions,copyPayload,-Fin.natAdd_eq_addNat]

private theorem correct_iff (rule : Mask r e d b) (head : Fin r → Fin b → Bool)
    (M D : Fields r e d) : (∀ i, Good rule head M D i) ↔ M = observed rule head ∧ Supported M D := by
  constructor
  · intro ok
    exact ⟨funext fun a => funext fun i => funext fun j => (ok i a j).1,
      fun a i j => (ok i a j).2⟩
  · rintro ⟨rfl,support⟩ i a j
    exact ⟨rfl,support a i j⟩

/-- Equality of packed arrays determines every supported candidate bit. -/
private theorem decoded (M D Z : Fields r e d) (hd : Supported M D) (hz : Supported M Z)
    (same : ∀ a, compact (blocks r d (M a)) (blocks r d (D a)) =
      compact (blocks r d (M a)) (blocks r d (Z a))) : D = Z := by
  funext a
  apply (blocks r d).injective
  have supp (T : Fields r e d) (ht : Supported M T) (j : Fin (r*d)) :
      blocks r d (M a) j = false → blocks r d (T a) j = false := by
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    simpa only [blocks_at] using ht a i j
  rw [← expand_compact _ (blocks r d (D a)) (supp D hd),same,
    expand_compact _ (blocks r d (Z a)) (supp Z hz)]

noncomputable def boundary (M Z : Fields r e d) (a : Fin e) :=
  compact (blocks r d (M a)) (blocks r d (Z a))

/-- Every guessed mask and expanded bit is forced by the headers and the
packed bit streams. The remaining value is precisely the product of the
base-tile coefficients on their correct per-copy payload slices. -/
theorem network_value (rule : Mask r e d b) (table : Table F r e d b)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) =
      if Y = compact M X then 1 else 0) (head : Fin r → Fin b → Bool) (Z : Fields r e d)
    (valid : Supported (observed rule head) Z) :
    (network (checkedTile rule table) C).eval (arguments head (boundary (observed rule head) Z)) =
      ∏ i, table i (head i) (copyPayload Z i) := by
  classical
  let M0 := observed rule head
  rw [network_eval]
  simp only [check_at,hC]
  have prod_bad (M D : Fields r e d) (bad : ¬∀ i, Good rule head M D i) :
      (∏ i, if Good rule head M D i then table i (head i) (copyPayload D i) else 0) = 0 := by
    obtain ⟨i,hi⟩ := not_forall.mp bad
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [Fintype.sum_eq_single M0]
  · rw [Fintype.sum_eq_single Z]
    · have good := (correct_iff rule head M0 Z).2 ⟨rfl,valid⟩
      simp [good,boundary,M0]
    · intro D ne
      by_cases gd : ∀ i, Good rule head M0 D i
      · have hd := ((correct_iff rule head M0 D).1 gd).2
        have diff : ∃ a, boundary M0 Z a ≠ compact (blocks r d (M0 a)) (blocks r d (D a)) := by
          by_contra! h
          exact ne (decoded M0 D Z hd valid (fun a => (h a).symm))
        obtain ⟨a,ha⟩ := diff
        have zero : (∏ j, if boundary M0 Z j = compact (blocks r d (M0 j)) (blocks r d (D j))
            then (1 : F) else 0) = 0 := Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)
        rw [zero,mul_zero]
      · rw [prod_bad _ _ gd,zero_mul]
  · intro M ne
    apply Finset.sum_eq_zero
    intro D _
    have bad : ¬∀ i, Good rule head M D i := fun h => ne ((correct_iff rule head M D).1 h).1
    rw [prod_bad _ _ bad,zero_mul]

end ThreeFlat.Diagonal.MotifOrderedCells

end OAI
