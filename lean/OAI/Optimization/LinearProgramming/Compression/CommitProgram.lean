import OAI.Optimization.LinearProgramming.Compression.Commit
import OAI.Optimization.LinearProgramming.Lattice.Oracle

/-! ## Computing a committed vector from affine comparisons

Each augmented integer query is answered by one strict-negative affine
comparison of the proxy entries. The concrete program below uses finite
rational search. The selector-parametric theorem also applies to lattice
reduction implementations satisfying the same approximation contract.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open SignType
open OAI.Optimization.LinearProgramming.Lattice

/-- Interpret a homogeneous nonnegative query on the augmented vector using the
strict-negative oracle on the original affine forms. -/
def affineCommitReply {d : ℕ} (negative : (Fin d → ℤ) → ℤ → Bool)
    (a : Fin (d+1) → ℤ) : Bool :=
  !(negative (fun i => a i.castSucc) (a (Fin.last d)))

theorem affineCommitReply_correct {d : ℕ} (x : Fin d → ℝ)
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm x a + c < 0) (a : Fin (d+1) → ℤ) :
    affineCommitReply negative a = true ↔ 0 ≤ formValue a (Fin.snoc x (1 : ℝ)) := by
  have ha : formValue a (Fin.snoc x (1 : ℝ)) =
      requestForm x (fun i => a i.castSucc) + a (Fin.last d) := by
    simp [formValue, requestForm, Fin.sum_univ_castSucc]
  rw [ha]
  cases h : negative (fun i => a i.castSucc) (a (Fin.last d)) with
  | false =>
    have hnon : ¬ requestForm x (fun i => a i.castSucc) + a (Fin.last d) < 0 :=
      fun hh => by simpa [h] using (ho _ _).mpr hh
    simp [affineCommitReply, h, le_of_not_gt hnon]
  | true =>
    have hneg := (ho _ _).mp h
    simp [affineCommitReply, h, hneg.not_ge]

/-- Normalize the integer returned by the rounding program with a chosen
rational simultaneous-approximation routine. -/
def computeCommitWith {d : ℕ} (M : ℕ)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (negative : (Fin d → ℤ) → ℤ → Bool) : Fin d → ℚ :=
  normalizeCommit (SignQueries.run (affineCommitReply negative) (roundingProgramWith M select))

/-- Polynomial bound for the output numerator and denominator binary sizes. -/
def affineCommitWidth (d M : ℕ) : ℕ := radixWidth (d+1) M * (d+1)

/-- A finite rational selector meeting Appendix A's quantitative approximation
guarantee gives the committed vector for all later affine queries. -/
theorem computeCommitWith_spec {d M : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator (d+1) M ^ ((d+1)+1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * ((d+1 : ℕ) : ℚ) * M))
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm x a + c < 0) :
    let γ := computeCommitWith M select negative
    (∀ i, (γ i).num.natAbs.size ≤ affineCommitWidth d M ∧ (γ i).den.size ≤ affineCommitWidth d M) ∧
    (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
      sign (requestForm (fun i => (γ i : ℝ)) a + c) = sign (requestForm x a + c)) ∧
    RequestSigns x (fun i => (γ i : ℝ)) M := by
  let z := SignQueries.run (affineCommitReply negative) (roundingProgramWith M select)
  obtain ⟨hzb, hz⟩ := roundingProgramWith_correct (Nat.succ_pos d) hM select hsel
    (Fin.snoc x (1 : ℝ)) (affineCommitReply negative) (affineCommitReply_correct x negative ho)
  have hheight (i : Fin (d+1)) : (z i).natAbs < 2^(affineCommitWidth d M) :=
    Nat.size_le.mp (hzb i)
  obtain ⟨_, hh, hs, ht⟩ := normalizeCommit_spec_of_height x hM z hheight hz
  exact ⟨fun i => ⟨Nat.size_le.mpr (hh i).1, Nat.size_le.mpr (hh i).2⟩, hs, ht⟩

/-- Every execution makes at most the stated number of affine comparisons,
including executions with inconsistent oracle answers. -/
theorem computeCommitWith_query_count {d : ℕ} (M : ℕ)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (negative : (Fin d → ℤ) → ℤ → Bool) :
    SignQueries.cost (affineCommitReply negative) (roundingProgramWith M select) ≤
      (d+1) * (2*(d+1) + 1 + (d+1) * searchPrecision (d+1) M) :=
  roundingProgramWith_cost _ _ _

/-- Deterministic computation using the finite exhaustive rational selector. -/
def computeCommit {d : ℕ} (M : ℕ) (negative : (Fin d → ℤ) → ℤ → Bool) : Fin d → ℚ :=
  computeCommitWith M (rationalDirichlet (searchDenominator (d+1) M)) negative

/-- The result of the concrete finite comparison program has bounded binary
length and preserves all affine comparisons exactly, including equality. -/
theorem computeCommit_spec {d M : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm x a + c < 0) :
    let γ := computeCommit M negative
    (∀ i, (γ i).num.natAbs.size ≤ affineCommitWidth d M ∧ (γ i).den.size ≤ affineCommitWidth d M) ∧
    (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
      sign (requestForm (fun i => (γ i : ℝ)) a + c) = sign (requestForm x a + c)) ∧
    RequestSigns x (fun i => (γ i : ℝ)) M :=
  computeCommitWith_spec x hM _ (search_selector_correct (Nat.succ_pos d) hM) negative ho

end Compression
end LinearProgramming
end Optimization
end OAI
