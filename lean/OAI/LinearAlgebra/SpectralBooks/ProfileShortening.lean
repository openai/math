import OAI.LinearAlgebra.SpectralBooks.ProfileAmplification
import OAI.LinearAlgebra.SpectralBooks.ProfileBroadcast
import OAI.LinearAlgebra.SpectralBooks.ProfileNetworkGrouping
import OAI.LinearAlgebra.SpectralBooks.ProfileWireCost

/-! # Shortening with profiles from an exact sum of crossing networks

The finite set of term cables is reused at every power. The endpoints reorder their external
slots by the common selector. A cable of one term carries the strings of its consecutive
occurrences, ordered by their positions in the selected word.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

noncomputable section
open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {D M A b j : ℕ} {budget : ℝ}

/-- Data assigned to all shared wires of one summand. -/
abbrev CrossingNetworkSum.Assignment (S : CrossingNetworkSum F D M A budget) (a : Fin A) :=
  (u : Fin (S.count a)) → BitString (S.wires a u).width

/-- At one vertex use its incident bits and the external data in the original word slot. -/
private def profileEntry (S : CrossingNetworkSum F D M A budget)
    (x : Fin j → (v : AxisSite D) → AxisLeg M v)
    (a : Fin A) (i : Fin j) (s : S.Assignment a) (v : AxisSite D) : F :=
  S.tables a v (x i v) (fun u ↦ (S.wires a u).basisTerm (s u) v)

/-- Local contraction for a fixed histogram. The selectors have `j*b` bits each. For each wire
of summand `a`, the corresponding block in `z` has `π a` strings of that wire's width. -/
def profileContraction (S : CrossingNetworkSum F D M A budget)
    (code : Fin A ↪ BitString b) (π : Fin A → ℕ)
    (x : Fin j → (v : AxisSite D) → AxisLeg M v) : F :=
  ∑ z : (a : Fin A) → Fin (π a) → S.Assignment a,
    selectorBroadcast (profileCode (π := π) (j := j) code) fun v w ↦
      ∏ a, ∏ k, profileEntry S x a (w.occurrence a k).val (z a k) v

/-- The original multiplicities and external slots are preserved, in every characteristic. -/
theorem profileContraction_eq (S : CrossingNetworkSum F D M A budget)
    (code : Fin A ↪ BitString b) (π : Fin A → ℕ)
    (x : Fin j → (v : AxisSite D) → AxisLeg M v) :
    profileContraction S code π x =
      ∑ w : WordsOfContent (Fin j) (Fin A) π,
        ∏ i, network (S.wires (w.val i)) (S.tables (w.val i)) (x i) := by
  simp only [profileContraction, selectorBroadcast_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [network, Fintype.prod_sum]
  symm
  apply Fintype.sum_equiv (w.assignmentEquiv S.Assignment)
  intro s
  let entry (a : Fin A) (i : Fin j) (u : S.Assignment a) := ∏ v, profileEntry S x a i u v
  change ∏ i, entry (w.val i) i (s i) = _
  rw [w.contraction_prod_blocks entry]
  dsimp [entry]
  conv_lhs =>
    congr
    · skip
    · ext a
      rw [Finset.prod_comm]
  rw [Finset.prod_comm]

/-- A fixed one-copy identity and profile shortening at every power. The same local wiring rule
and finite sets of terminals and data cables work for every histogram, and all selector cables
are included in the relative saving. -/
def HasProfileShortening (F : Type*) [CommSemiring F] (D : ℕ) : Prop :=
    ∃ (m A b : ℕ) (budget ν : ℝ) (S : CrossingNetworkSum F D m A budget)
      (code : Fin A ↪ BitString b), 0 < m ∧ 0 < A ∧ 0 < ν ∧ ν < 1 ∧
      ∀ (j : ℕ) (π : Fin A → ℕ), ∑ a, π a = j →
        profileWireCost S.count S.wires π j b ≤ (1 - ν) * 2 * D * m * j ∧
        ∀ x : Fin j → (v : AxisSite D) → AxisLeg m v,
          profileContraction S code π x =
            ∑ w : WordsOfContent (Fin j) (Fin A) π,
              ∏ i, network (S.wires (w.val i)) (S.tables (w.val i)) (x i)

/-- The exact-identity case of the companion manuscript's shortening lemma. -/
theorem ShortenedCrossing.hasProfileShortening (h : ShortenedCrossing F D M)
    (hD : 2 ≤ D) (hM : 0 < M) : HasProfileShortening F D := by
  obtain ⟨m, A, b, budget, ν, hm, hA, hν, hν', hsave, ⟨code⟩, ⟨S⟩⟩ :=
    h.exists_profile_block (by omega) hM
  exact ⟨m, A, b, budget, ν, S, code, hm, hA, hν, hν', fun j π hπ ↦
    ⟨profileWireCost_le hπ S.cost_le hsave, profileContraction_eq S code π⟩⟩

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
