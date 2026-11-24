import OAI.Computability.VPVNP.MacaulayCoordinates

/-!
# Querying basis ordinals after a prescribed row prefix

Appendix D keeps the independent monomial rows following the equation rows.
Their dense indices are the ordinals of the greedy rows of the full matrix
offset by the rank of the equation prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

variable {K : Type*} [Field K] [DecidableEq K] {n m w : ℕ}

theorem prefix_rankQuery_mono (A : Matrix (Fin n) (Fin m) K) {s u : ℕ} (hs : s ≤ n)
    (hu : u ≤ n) (hsu : s ≤ u) :
    rankQuery (prefixRows A s hs) ≤ rankQuery (prefixRows A u hu) := by
  simp only [rankQuery_eq, rank_prefixRows]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hval⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hval.trans_le hsu⟩

theorem greedyRowIndex_lt_iff (A : Matrix (Fin n) (Fin m) K)
    (k : Fin (rankQuery A)) (s : ℕ) (hs : s ≤ n) :
    (greedyRowIndex A k).val < s ↔ k.val < rankQuery (prefixRows A s hs) := by
  cases s with
  | zero => simp [rankQuery_eq, rank_prefixRows]
  | succ s =>
    let g := greedyRowIndex A k
    have htest : k.val < rankQuery (prefixRows A (g.val + 1) g.isLt) := by
      unfold g greedyRowIndex firstPrefixAbove
      apply Fin.find_spec (p := fun i : Fin n => k.val < rankQuery (prefixRows A (i.val+1) i.isLt))
    constructor
    · intro hg
      exact htest.trans_le (prefix_rankQuery_mono A g.isLt hs (Nat.succ_le_of_lt hg))
    · intro hk
      let j : Fin n := ⟨s, hs⟩
      have hle : g ≤ j := by
        unfold g greedyRowIndex firstPrefixAbove
        apply Fin.find_le_of_pos
        exact hk
      exact Nat.lt_succ_of_le hle

omit [Field K] [DecidableEq K] in
private theorem prefix_append_eq (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) : prefixRows (appendRows W M) w (Nat.le_add_right _ _) = W := by
  funext i j
  change appendRows W M (i.castAdd n) j = W i j
  rw [appendRows_left]

/-- Number of independent monomial rows after reducing modulo the preceding rows. -/
def suffixDimension (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K) : ℕ :=
  rankQuery (appendRows W M) - rankQuery W

private def offsetOrdinal (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (k : Fin (suffixDimension W M)) : Fin (rankQuery (appendRows W M)) :=
  ⟨rankQuery W + k.val, by have := k.isLt; unfold suffixDimension at this; omega⟩

/-- Read the original index of a selected monomial by its ordinal among the
independent monomial rows. The prefix rank scan always uses the original rows. -/
def suffixBasisIndex (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (k : Fin (suffixDimension W M)) : Fin n :=
  let g := greedyRowIndex (appendRows W M) (offsetOrdinal W M k)
  ⟨g.val - w, by
    have hg := (greedyRowIndex_lt_iff (appendRows W M) (offsetOrdinal W M k) w
      (Nat.le_add_right _ _))
    rw [prefix_append_eq] at hg
    have ho : rankQuery W ≤ (offsetOrdinal W M k).val := Nat.le_add_right _ _
    have hge : w ≤ g.val := le_of_not_gt (fun h => (Nat.not_lt_of_ge ho) (hg.mp h))
    have := g.isLt
    omega⟩

private theorem suffixBasisIndex_natAdd (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (k : Fin (suffixDimension W M)) :
    (suffixBasisIndex W M k).natAdd w = greedyRowIndex (appendRows W M) (offsetOrdinal W M k) := by
  apply Fin.ext
  let g := greedyRowIndex (appendRows W M) (offsetOrdinal W M k)
  change w + (g.val - w) = g.val
  have h := greedyRowIndex_lt_iff (appendRows W M) (offsetOrdinal W M k) w (Nat.le_add_right _ _)
  rw [prefix_append_eq] at h
  have ho : rankQuery W ≤ (offsetOrdinal W M k).val := Nat.le_add_right _ _
  have hge : w ≤ g.val := le_of_not_gt (fun hg => (Nat.not_lt_of_ge ho) (h.mp hg))
  omega

theorem suffixBasisIndex_strictMono (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K) :
    StrictMono (suffixBasisIndex W M) := by
  intro i j hij
  have ho : offsetOrdinal W M i < offsetOrdinal W M j := Nat.add_lt_add_left hij _
  let A := appendRows W M
  have h := ((greedyIndices K A.row).orderEmbOfFin (greedyRows_card A)).strictMono ho
  rw [← greedyRowIndex_eq, ← greedyRowIndex_eq, ← suffixBasisIndex_natAdd, ← suffixBasisIndex_natAdd] at h
  exact Nat.lt_of_add_lt_add_left h

theorem suffixBasisIndex_injective (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K) :
    Function.Injective (suffixBasisIndex W M) :=
  (suffixBasisIndex_strictMono W M).injective

theorem mem_range_suffixBasisIndex (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (j : Fin n) :
    j ∈ Set.range (suffixBasisIndex W M) ↔ j.natAdd w ∈ greedyIndices K (appendRows W M).row := by
  let A := appendRows W M
  constructor
  · rintro ⟨k, rfl⟩
    rw [suffixBasisIndex_natAdd, greedyRowIndex_eq]
    exact Finset.orderEmbOfFin_mem ..
  · intro hj
    let S := greedyIndices K A.row
    have he : j.natAdd w ∈ Set.range (greedyRowIndex A) := by
      have hf : greedyRowIndex A = S.orderEmbOfFin (greedyRows_card A) := funext (greedyRowIndex_eq A)
      rw [hf, Finset.range_orderEmbOfFin]
      exact hj
    obtain ⟨k, hk⟩ := he
    have hw := greedyRowIndex_lt_iff A k w (Nat.le_add_right _ _)
    rw [hk, prefix_append_eq] at hw
    have hge : rankQuery W ≤ k.val := le_of_not_gt (fun h => by
      have := hw.mpr h
      change w + j.val < w at this
      omega)
    let u : Fin (suffixDimension W M) := ⟨k.val - rankQuery W, by
      have hlt := k.isLt
      change k.val < rankQuery (appendRows W M) at hlt
      unfold suffixDimension; omega⟩
    have hu : offsetOrdinal W M u = k := Fin.ext (by change _ + (k.val - _) = k.val; omega)
    refine ⟨u, ?_⟩
    have h := suffixBasisIndex_natAdd W M u
    rw [hu, hk] at h
    exact Fin.natAdd_injective _ _ h

end RankQuery

end VPVNP
end Computability
end OAI
