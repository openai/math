import OAI.ThreeFlat.RouteExpanders
import OAI.ThreeFlat.Concentrator.GreedyMixing
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Bounded-degree greedy concentrators at arbitrary sizes

Padding embeds both sets of slots in an expander whose order is at most twice
the common size bound. The port degree depends only on the desired residual
density. The same candidate lists work for every active mask and free set.
-/

namespace ThreeFlat.Concentrator

universe u v

theorem exists_greedy_candidate_cover {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ degree : ℕ, ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      [DecidableEq L] [DecidableEq R] (work : ℕ), 0 < work →
      Fintype.card L ≤ work → Fintype.card R ≤ work →
      ∃ N : L → List R,
        (∀ x, (N x).length ≤ degree) ∧
        (∀ r, (Finset.univ.filter fun x => r ∈ N x).card ≤ degree) ∧
        ∀ (N' : L → List R), (∀ x r, r ∈ N x → r ∈ N' x) → ∀ (xs : List L) (F : Finset R) (threshold : ℕ),
          xs.length + threshold ≤ F.card → ρ * work ≤ threshold →
          (Greedy.run N' xs F).missed.card < threshold := by
  obtain ⟨h, hpos, _, lam, hlam, family⟩ :=
    RouteUnits.exists_routing_graphs 0 (ε := (ρ / 4) ^ 2) (by positivity)
  refine ⟨2 * h, ?_⟩
  intro L R _ _ _ _ work hw hL hR
  let k := Nat.log 2 work + 1
  let m := 2 ^ k
  have padded : work ≤ m := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) work).le
  have comparable : m ≤ 2 * work := by
    dsimp [m, k]
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hw.ne')
  have hm : 0 < m := hw.trans_le padded
  let : NeZero (2 * h) := ⟨(by omega)⟩
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨G, cert⟩ := family k
  obtain ⟨left⟩ := Function.Embedding.nonempty_of_card_le (α := L) (β := Fin m)
    (by simpa using hL.trans padded)
  obtain ⟨right⟩ := Function.Embedding.nonempty_of_card_le (α := R) (β := Fin m)
    (by simpa using hR.trans padded)
  let readRight := Function.partialInv right
  let ports := List.finRange (2 * h)
  refine ⟨portCandidates G ports left readRight, ?_, ?_, ?_⟩
  · intro x
    simpa [ports] using portCandidates_length G ports left readRight x
  · intro r
    simpa using portCandidates_contenders_card G ports left right readRight
      (fun eq => ((right.injective.isPartialInv _ _).mp eq).symm) r
  · intro N' covers xs F threshold slack density
    apply greedy_missed_card_lt_of_candidate_cover G cert ports List.mem_finRange left right readRight
      right.injective.isPartialInv.eq N' covers xs F threshold slack
    have hrho : lam ≤ ρ / 4 := le_of_sq_le_sq hlam (by positivity)
    change lam < (threshold : ℝ) / (Fintype.card (Fin m) : ℝ)
    rw [Fintype.card_fin]
    refine (lt_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).2 ?_
    calc
      lam * m < (ρ / 2) * m :=
        mul_lt_mul_of_pos_right (by linarith : lam < ρ / 2) (by exact_mod_cast hm)
      _ ≤ (ρ / 2) * (2 * work) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast comparable) (by positivity)
      _ = ρ * work := by ring
      _ ≤ _ := density

/-- One may use the candidate lists directly in port order. -/
theorem exists_greedy_candidates {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ degree : ℕ, ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      [DecidableEq L] [DecidableEq R] (work : ℕ), 0 < work →
      Fintype.card L ≤ work → Fintype.card R ≤ work →
      ∃ N : L → List R,
        (∀ x, (N x).length ≤ degree) ∧
        (∀ r, (Finset.univ.filter fun x => r ∈ N x).card ≤ degree) ∧
        ∀ (xs : List L) (F : Finset R) (threshold : ℕ),
          xs.length + threshold ≤ F.card → ρ * work ≤ threshold →
          (Greedy.run N xs F).missed.card < threshold := by
  obtain ⟨degree, graph⟩ := exists_greedy_candidate_cover.{u,v} hρ
  refine ⟨degree, ?_⟩
  intro L R _ _ _ _ work hw hL hR
  obtain ⟨N, l, r, cover⟩ := graph L R work hw hL hR
  exact ⟨N, l, r, cover N (fun _ _ h => h)⟩

end ThreeFlat.Concentrator

end OAI
