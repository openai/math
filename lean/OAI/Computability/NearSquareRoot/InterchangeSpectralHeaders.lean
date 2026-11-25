import OAI.Computability.NearSquareRoot.InterchangeSpectralRuns

/-!
# Building every comparison fibre from the field and suffix rulers

The early-field rank rulers occupy quadratic space in the field length, which
is available because the field occurs twice. A stack map receives a shared
field and suffix ruler alongside each rank, converts the three rulers to binary,
and runs the comparison generator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SpectralHeaders

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Code.Task
open IntegerMultiplication.Carry IntegerMultiplication.Bits IntegerMultiplication.Strip
open NearSquareRoot.SpectralRuns

variable {I A : Type} [Codec A] {H T : I → Type}

/-- Enumerating the ranks of any ordered series produces the same sequence of
unary rulers. -/
theorem rank_stripe {H : Type} (h : Series H) :
    stripe h (fun x => send (tally (h.index x).val)) = send (Iter.lineup (tally h.count)) := by
  rw [stripe_eq', Iter.lined]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hi'
  let j : Fin h.count := ⟨i, by simpa only [Series.card] using hi⟩
  rw [h.get _ j]
  simp [j]

private def binary (x : Tally × Tally × Tally) : Word × Word × Word :=
  (born x.1.length, born x.2.1.length, born x.2.2.length)

private theorem binary_easy : Easy binary := by
  unfold binary
  exact (Easy.fst.compose easy_chart).pair
    (((Easy.snd.compose Easy.fst).compose easy_chart).pair
     ((Easy.snd.compose Easy.snd).compose easy_chart))

/-- From unary ranks supplied in order, construct all rows, including the
binary compression of every input header. -/
theorem rows_of_ranks (h : (i : I) → Series (H i)) (t : (i : I) → Series (T i))
    (hh : ∀ i, 0 < (h i).count) (ht : ∀ i, 0 < (t i).count)
    (before equal after : A) {w : I → ℝ} {src : I → Tree}
    (hm : ∀ i, (((h i).count * ((h i).count * (t i).count) : ℕ) : ℝ) ≤ w i)
    (hd : Carries w src (fun i => send (tally (h i).count)))
    (hs : Carries w src (fun i => send (tally (t i).count)))
    (ranks : Carries w src (fun i => stripe (h i) fun x => send (tally ((h i).index x).val))) :
    Carries w src (fun i => stripe (h i) fun x => stripe ((h i).cart (t i)) fun y =>
      send (mask (h i) ((h i).index x) before equal after y.1)) := by
  let volume i := (h i).count * (t i).count
  have positive i : 0 < volume i := Nat.mul_pos (hh _) (ht _)
  have d_bound i : (h i).count ≤ volume i := Nat.le_mul_of_pos_right _ (ht i)
  have s_bound i : (t i).count ≤ volume i := Nat.le_mul_of_pos_left _ (hh i)
  let shared i := (tally (h i).count, tally (t i).count)
  have shared_size i : size (shared i) ≤ 7 * volume i := by
    simp only [shared, size_prod, size_tally, tally_length]
    have := d_bound i
    have := s_bound i
    have := positive i
    omega
  have broadcast : Carries w src (stackRun h fun i _ => send (shared i)) := by
    apply spread h _ (hd.twice (hd.twice hs))
    refine ⟨14, fun i => ?_⟩
    have bound : ((h i).count + 1) * (size (shared i)) ≤ 14 * ((h i).count * volume i) := by
      calc
        _ ≤ (2 * (h i).count) * (7 * volume i) :=
          Nat.mul_le_mul (by have := hh i; omega) (shared_size i)
        _ = _ := by ring
    calc
      _ ≤ 14 * (((h i).count * volume i : ℕ) : ℝ) := by exact_mod_cast bound
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by norm_num)
  let head3 (i : I) (x : H i) := (tally ((h i).index x).val, shared i)
  have assembled : Carries w src (stackRun h (fun i x => send (head3 i x))) :=
    coalesce h _ _ ranks broadcast
  let allowance (u : Sigma H) : ℝ := volume u.1
  have enough (u : Sigma H) : 1 ≤ allowance u := by
    change (1 : ℝ) ≤ ↑(volume u.1)
    exact_mod_cast (show 1 ≤ volume u.1 from positive _)
  have headerSize : Volume allowance (fun u : Sigma H => send (head3 u.1 u.2)) := by
    refine ⟨11, fun u => ?_⟩
    have e := ((h u.1).index u.2).isLt
    have b : size (head3 u.1 u.2) ≤ 11 * volume u.1 := by
      simp only [head3, shared, size_prod, size_tally, tally_length]
      have := s_bound u.1
      have := d_bound u.1
      have := positive u.1
      omega
    change (size (head3 u.1 u.2) : ℝ) ≤ 11 * (volume u.1 : ℝ)
    exact_mod_cast b
  let rows (i : I) (x : H i) := stripe ((h i).cart (t i)) fun y =>
      send (mask (h i) ((h i).index x) before equal after y.1)
  have perRow : Carries allowance (fun u : Sigma H => send (head3 u.1 u.2))
      (fun u => rows u.1 u.2) := by
    have convert := Carries.func (y := fun u : Sigma H => head3 u.1 u.2)
      enough headerSize binary binary_easy
    apply convert.chain
    simpa only [binary, head3, shared, tally_length] using
      fibre_stripe (fun u : Sigma H => h u.1) (fun u => t u.1) (fun u => ht u.1)
        (fun u => (h u.1).index u.2) before equal after
  apply assembled.chain
  apply (liftoff h (fun i x => send (head3 i x)) rows (fun i => (volume i : ℝ)) perRow).times
    hd.budget 2
  intro i
  have bound := hm i
  change (((h i).count * volume i : ℕ) : ℝ) ≤ w i at bound
  push_cast at bound
  have := hd.budget i
  norm_num
  linarith

/-- Construct all the early-field fibres, in order, from only the physical
field and suffix rulers. -/
theorem nestedMasks (h : (i : I) → Series (H i)) (t : (i : I) → Series (T i))
    (hh : ∀ i, 0 < (h i).count) (ht : ∀ i, 0 < (t i).count)
    (before equal after : A) {w : I → ℝ} {src : I → Tree}
    (hm : ∀ i, (((h i).count * ((h i).count * (t i).count) : ℕ) : ℝ) ≤ w i)
    (hd : Carries w src (fun i => send (tally (h i).count)))
    (hs : Carries w src (fun i => send (tally (t i).count))) :
    Carries w src (fun i => stripe (h i) fun x => stripe ((h i).cart (t i)) fun y =>
      send (mask (h i) ((h i).index x) before equal after y.1)) := by
  apply rows_of_ranks h t hh ht before equal after hm hd hs
  simp_rw [rank_stripe]
  apply hd.sequence
  refine ⟨hd.budget, _, enumerate_ranks.on (fun i => tally (h i).count), 5, fun i => ?_⟩
  have small : ((h i).count + 1)^2 ≤ 4 * ((h i).count * ((h i).count * (t i).count)) := by
    calc
      _ ≤ (2 * (h i).count)^2 := Nat.pow_le_pow_left (by have := hh i; omega) 2
      _ = 4 * ((h i).count * (h i).count) := by ring
      _ ≤ _ := by
        gcongr
        exact Nat.le_mul_of_pos_right _ (ht i)
  have b : ((((h i).count + 1)^2 : ℕ) : ℝ) ≤ 4 * w i := by
    calc
      _ ≤ 4 * (((h i).count * ((h i).count * (t i).count) : ℕ) : ℝ) := by exact_mod_cast small
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by norm_num)
  have := hd.budget i
  simp only [tally_length, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at *
  linarith

end SpectralHeaders

end NearSquareRoot
end Computability
end OAI
