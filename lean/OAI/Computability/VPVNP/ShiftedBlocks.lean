import OAI.Computability.VPVNP.VacuumPairing
import OAI.Computability.VPVNP.ShiftedBlockCuts

/-!
# Assembly of the shifted crossing blocks

Appendix B indexes a block by the particle number and the two doubled source
energies. We extend both factors of each cut by zero at incompatible source
indices, concatenate their intermediate coordinates, and remove the integral
pairing by its inverse. Each cut retains its own set of intermediate states.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open scoped BigOperators

/-- The nonempty source states of doubled energy at most `H`. -/
abbrev CrossingState (n H : ℕ) := Σ m : Fin n, EnergySector n (m.val + 1) H

/-- The first coordinate is the particle number minus one. The other coordinates
are the doubled energies of the two operator indices. -/
abbrev CrossingBlock (n H : ℕ) := Fin n × Fin (H + 1) × Fin (H + 1)

/-- The doubled energy of a crossing source state, viewed as a grade between zero and the
cutoff. -/
def sourceGrade {n H : ℕ} (i : CrossingState n H) : Fin (H + 1) :=
  ⟨doubledSectorEnergy i.2.val, Nat.lt_succ_of_le i.2.property⟩

/-- The exponent of the multiplier `(z - w)^L` for this block. For an inhabited block it is the
sum of the two source energies minus one. -/
def blockPoleDegree {n H : ℕ} (t : CrossingBlock n H) : ℕ :=
  (t.2.1.val + t.2.2.val) / 2 - 1

/-- A source state belongs to the row block when its particle number and doubled energy agree
with the first source index of the block. -/
def isBlockRow {n H : ℕ} (t : CrossingBlock n H) (i : CrossingState n H) : Prop :=
  (t.1, t.2.1) = (i.1, sourceGrade i)

/-- A source state belongs to the column block when its particle number and doubled energy
agree with the second source index of the block. -/
def isBlockColumn {n H : ℕ} (t : CrossingBlock n H) (i : CrossingState n H) : Prop :=
  (t.1, t.2.2) = (i.1, sourceGrade i)

/-- The source states with the particle number and row energy specified by the crossing block. -/
abbrev BlockRows {n H : ℕ} (t : CrossingBlock n H) := {i // isBlockRow t i}
/-- The source states with the particle number and column energy specified by the crossing
block. -/
abbrev BlockColumns {n H : ℕ} (t : CrossingBlock n H) := {j // isBlockColumn t j}

/-- Each intermediate coordinate retains its block and its binomial index. -/
abbrev BlockCoordinates (n H : ℕ) (M : Type*) :=
  Σ t : CrossingBlock n H, Fin (blockPoleDegree t + 1) × M

theorem blockCoordinates_card_le (n H : ℕ) (M : Type*) [Fintype M] :
    Fintype.card (BlockCoordinates n H M) ≤ n * (H + 1)^3 * Fintype.card M := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : CrossingBlock n H, (H + 1) * Fintype.card M := by
      apply Finset.sum_le_sum
      intro t _
      rw [Fintype.card_prod, Fintype.card_fin]
      apply Nat.mul_le_mul_right
      have := t.2.1.isLt
      have := t.2.2.isLt
      unfold blockPoleDegree
      omega
    _ = _ := by simp [CrossingBlock]; ring

/-- The local decomposition on the block tagged by `t`. It uses the two opposite
orders of the input and output state, with the binomial index ranging to its
actual pole degree. -/
def BlockDecomposition {n H : ℕ} (t : CrossingBlock n H)
    (Y K L : Type*) [Fintype K] [Fintype L] [DecidableEq Y] : Prop :=
  ∃ (a : Fin (blockPoleDegree t + 1) × K → BlockRows t → Y → ℤ)
    (b : Fin (blockPoleDegree t + 1) × K → BlockColumns t → Y → ℤ)
    (c : Fin (blockPoleDegree t + 1) × L → BlockRows t → Y → ℤ)
    (d : Fin (blockPoleDegree t + 1) × L → BlockColumns t → Y → ℤ),
    ∀ i j α β, ∑ k, a k i α * b k j β + ∑ l, c l i β * d l j α =
      crossingPairing n H i.val j.val * (if α = β then 1 else 0)

private noncomputable def extendByZero {X Y : Type*} {p : X → Prop}
    (f : {x // p x} → Y → ℤ) (x : X) (y : Y) : ℤ := by
  classical
  exact if h : p x then f ⟨x, h⟩ y else 0

/-- Concatenate the local factorizations and apply the inverse of the signed
integral pairing. The first summand factors on `(i, α) | (j, β)` and the second
on `(i, β) | (j, α)`. -/
theorem assembleCrossingBlocks (n H : ℕ) (Y K L : Type*)
    [Fintype K] [Fintype L] [DecidableEq Y]
    (blocks : ∀ t : CrossingBlock n H, BlockDecomposition t Y K L) :
    ∃ (a b : BlockCoordinates n H K → CrossingState n H → Y → ℤ)
      (c d : BlockCoordinates n H L → CrossingState n H → Y → ℤ),
      ∀ i j α β, ∑ k, a k i α * b k j β + ∑ l, c l i β * d l j α =
        (if i = j then 1 else 0) * (if α = β then 1 else 0) := by
  classical
  unfold BlockDecomposition at blocks
  choose a b c d hblock using blocks
  let a' (v : BlockCoordinates n H K) := extendByZero (a v.1 v.2)
  let b' (v : BlockCoordinates n H K) := extendByZero (b v.1 v.2)
  let c' (v : BlockCoordinates n H L) := extendByZero (c v.1 v.2)
  let d' (v : BlockCoordinates n H L) := extendByZero (d v.1 v.2)
  suffices h : ∀ i j α β, ∑ k, a' k i α * b' k j β + ∑ l, c' l i β * d' l j α =
      crossingPairing n H i j * (if α = β then 1 else 0) by
    obtain ⟨a'', c'', h'⟩ :=
      normalizeCrossing a' b' c' d' _ (crossingPairing_isUnit n H) h
    exact ⟨a'', b', c'', d', h'⟩
  intro i j α β
  rw [Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_add_distrib]
  let t₀ : CrossingBlock n H := (i.1, sourceGrade i, sourceGrade j)
  have off (t : CrossingBlock n H) (h : t ≠ t₀ ∨ i.1 ≠ j.1) :
      ¬(isBlockRow t i ∧ isBlockColumn t j) := by
    rintro ⟨hr, hc⟩
    obtain ⟨hm, he⟩ := Prod.mk.inj hr
    obtain ⟨hm', he'⟩ := Prod.mk.inj hc
    have ht : t = t₀ := Prod.ext hm (Prod.ext he he')
    exact h.elim (· ht) (· (hm.symm.trans hm'))
  have zero (t : CrossingBlock n H) (ht : ¬(isBlockRow t i ∧ isBlockColumn t j)) :
      ∑ k, a' ⟨t, k⟩ i α * b' ⟨t, k⟩ j β +
        ∑ l, c' ⟨t, l⟩ i β * d' ⟨t, l⟩ j α = 0 := by
    by_cases hr : isBlockRow t i
    · have hc : ¬isBlockColumn t j := fun hc => ht ⟨hr, hc⟩
      simp [b', d', extendByZero, hc]
    · simp [a', c', extendByZero, hr]
  by_cases hij : i.1 = j.1
  · rw [Finset.sum_eq_single t₀]
    · have hr : isBlockRow t₀ i := rfl
      have hc : isBlockColumn t₀ j := Prod.ext hij rfl
      simpa only [a', b', c', d', extendByZero, dite_eq_left hr, dite_eq_left hc] using
        hblock t₀ ⟨i, hr⟩ ⟨j, hc⟩ α β
    · intro t _ ht
      exact zero t (off t (.inl ht))
    · simp
  · rw [Finset.sum_eq_zero (fun t _ => zero t (off t (.inr hij)))]
    rcases i with ⟨mi, i⟩
    rcases j with ⟨mj, j⟩
    rw [crossingPairing, Matrix.blockDiagonal'_apply_ne _ _ _ hij, zero_mul]


open Lemmata.FockCircuits.FiniteIdentity

/-- Finite-mode states of doubled energy at most `B`. -/
abbrev CrossingCutoff (N : ℕ) (B : ℤ) :=
  Cutoff (fun i : Index N => (Lemmata.FockCircuits.doubledEnergy i.val : ℤ)) B

private theorem degree_of_inhabited_block {n H : ℕ} {t : CrossingBlock n H}
    (i : BlockRows t) (j : BlockColumns t) :
    2 * blockPoleDegree t + 2 = t.2.1.val + t.2.2.val := by
  have hi := Prod.mk.inj i.property
  have hj := Prod.mk.inj j.property
  have he : t.2.1.val = doubledSectorEnergy i.val.2.val := congrArg Fin.val hi.2
  have he' : t.2.2.val = doubledSectorEnergy j.val.2.val := congrArg Fin.val hj.2
  have hm := congrArg Fin.val (hi.1.symm.trans hj.1)
  rw [blockPoleDegree, he, he', doubledSectorEnergy_eq, doubledSectorEnergy_eq]
  omega

/-- Integral crossing at a fixed energy cutoff and shift. The finite-mode
window contains the coefficient of both products, and the sizes of the two
intermediate spaces retain the signs of the shift. -/
theorem finiteShiftedCrossing (N B H E : ℕ) (s : ℤ)
    (hHN : H ≤ N) (hcut : E + B + H + 4 ≤ 2 * N)
    (hs : |2 * (-s - 1)| ≤ (B : ℤ)) :
    ∃ (a b : BlockCoordinates H H (CrossingCutoff N ((E : ℤ) + H + 2*s)) →
        CrossingState H H → CrossingCutoff N E → ℤ)
      (c d : BlockCoordinates H H (CrossingCutoff N ((E : ℤ) + H - 2*s)) →
        CrossingState H H → CrossingCutoff N E → ℤ),
      ∀ i j α β, ∑ k, a k i α * b k j β + ∑ l, c l i β * d l j α =
        (if i = j then 1 else 0) * (if α = β then 1 else 0) := by
  apply assembleCrossingBlocks
  intro t
  classical
  by_cases ht : Nonempty (BlockRows t × BlockColumns t)
  · obtain ⟨⟨i₀, j₀⟩⟩ := ht
    let A (i : BlockRows t) := sectorIndex hHN i.val.2.val
    let C (j : BlockColumns t) := sectorIndex hHN j.val.2.val
    have hA (i : BlockRows t) : Lemmata.FockCircuits.doubledEnergy (A i).val = t.2.1.val := by
      simp only [A, sectorIndex_energy]
      exact congrArg Fin.val (Prod.mk.inj i.property).2.symm
    have hC (j : BlockColumns t) : Lemmata.FockCircuits.doubledEnergy (C j).val = t.2.2.val := by
      simp only [C, sectorIndex_energy]
      exact congrArg Fin.val (Prod.mk.inj j.property).2.symm
    have hcA (i : BlockRows t) : (A i).val.card = t.1.val + 1 := by
      simp only [A, sectorIndex_card, (Prod.mk.inj i.property).1]
    have hcC (j : BlockColumns t) : (C j).val.card = t.1.val + 1 := by
      simp only [C, sectorIndex_card, (Prod.mk.inj j.property).1]
    obtain ⟨p, q, r, u, hf⟩ := fock_block_cuts N B H E t.2.1.val t.2.2.val
      (t.1.val + 1) (blockPoleDegree t) s A C hA hC hcA hcC
      (degree_of_inhabited_block i₀ j₀) (Nat.le_of_lt_succ t.2.1.isLt)
      (Nat.le_of_lt_succ t.2.2.isLt) hcut hs
    refine ⟨p, q, r, u, ?_⟩
    intro i j α β
    simpa only [A, C, vacuum_matrix_crossingPairing] using (hf i j α β).symm
  · exact ⟨0, 0, 0, 0, fun i j => (ht ⟨(i, j)⟩).elim⟩

end Crossing

end VPVNP
end Computability
end OAI
