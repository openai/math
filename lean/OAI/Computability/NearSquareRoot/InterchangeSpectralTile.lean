import OAI.Computability.IntegerMultiplication.Strip.Cars

/-!
# Replicating comparison fibres across spectators

A mask for an early field and a late field first computes one row for each
early value.  Two streaming copies insert a gap and a prefix of arbitrary
sizes.  The work is linear in the number of physical output positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SpectralTile

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Code.Task

variable {I : Type}

private theorem row_bound {A : Type} (s : Series A) (v : A → Tree) (k : ℕ)
    (hs : 0 < s.count) (hv : ∀ a, (v a).count ≤ k) :
    (stripe s v).count ≤ (k + 2) * s.count := by
  calc
    _ ≤ s.count * (k + 1) + 1 := stripe_size s v k hv
    _ ≤ s.count * (k + 1) + s.count := Nat.add_le_add_left hs _
    _ = _ := by ring

/-- From a tally and one complete flat row, produce an ordered array with a copy
of that row at every position of the outer series. -/
theorem repeatFlat {A B : I → Type} (s : (i : I) → Series (A i))
    (t : (i : I) → Series (B i)) (v : (i : I) → B i → Tree)
    (hs : ∀ i, 0 < (s i).count) (ht : ∀ i, 0 < (t i).count)
    (k : ℕ) (hv : ∀ i b, (v i b).count ≤ k)
    {w : I → ℝ} {src : I → Tree}
    (hp : Carries w src (fun i => Tree.fork (send (tally (s i).count))
      (stripe (t i) (v i))))
    (hm : ∀ i, (((s i).count * (t i).count : ℕ) : ℝ) ≤ w i) :
    Carries w src (fun i => stripe ((s i).cart (t i)) fun a => v i a.2) := by
  apply IntegerMultiplication.Strip.flatten s t
  apply spread s _ hp
  refine ⟨2 * (k + 2), fun i => ?_⟩
  have hrow := row_bound (t i) (v i) k (ht i) (hv i)
  have hprod : ((s i).count + 1) * (stripe (t i) (v i)).count ≤
      (2 * (k + 2)) * ((s i).count * (t i).count) := by
    calc
      _ ≤ (2 * (s i).count) * ((k + 2) * (t i).count) :=
        Nat.mul_le_mul (by have := hs i; omega) hrow
      _ = _ := by ring
  calc
    _ ≤ ((2 * (k + 2) : ℕ) : ℝ) * (((s i).count * (t i).count : ℕ) : ℝ) := by
      exact_mod_cast hprod
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by positivity)

/-- One genuine stack program, including production and distribution of the gap
tallies, expands the mask to prefix × early × gap × tail order. -/
theorem tile {P H G T : I → Type}
    (p : (i : I) → Series (P i)) (h : (i : I) → Series (H i))
    (g : (i : I) → Series (G i)) (t : (i : I) → Series (T i))
    (v : (i : I) → H i → T i → Tree)
    (pp : ∀ i, 0 < (p i).count) (ph : ∀ i, 0 < (h i).count)
    (pg : ∀ i, 0 < (g i).count) (pt : ∀ i, 0 < (t i).count)
    (k : ℕ) (hv : ∀ i a b, (v i a b).count ≤ k)
    {w : I → ℝ} {src : I → Tree}
    (hm : ∀ i, (((p i).count * ((h i).count * ((g i).count * (t i).count)) : ℕ) : ℝ) ≤ w i)
    (prefixCount : Carries w src (fun i => send (tally (p i).count)))
    (earlyCount : Carries w src (fun i => send (tally (h i).count)))
    (gapCount : Carries w src (fun i => send (tally (g i).count)))
    (rows : Carries w src (fun i => stripe (h i) fun a => stripe (t i) (v i a))) :
    Carries w src (fun i => stripe ((p i).cart ((h i).cart ((g i).cart (t i))))
      fun x => v i x.2.1 x.2.2.2) := by
  let fibre i := (g i).count * (t i).count
  have fibrePos i : 0 < fibre i := Nat.mul_pos (pg i) (pt i)
  have hf i : (((h i).count * fibre i : ℕ) : ℝ) ≤ w i := by
    apply le_trans _ (hm i)
    exact_mod_cast Nat.le_mul_of_pos_left ((h i).count * fibre i) (pp i)
  let copies i := send (tally (g i).count)
  have hcopies i : (copies i).count ≤ 3 * (g i).count := by
    change size (tally _) ≤ _
    rw [size_tally, tally_length]
    have := pg i
    omega
  have manyCopies : Carries w src (stackRun h fun i _ => copies i) := by
    apply spread h _ (earlyCount.twice gapCount)
    refine ⟨6, fun i => ?_⟩
    have copySize : ((h i).count + 1) * (copies i).count ≤ 6 * ((h i).count * fibre i) := by
      calc
        _ ≤ (2 * (h i).count) * (3 * (g i).count) :=
          Nat.mul_le_mul (by have := ph i; omega) (hcopies i)
        _ = 6 * ((h i).count * (g i).count) := by ring
        _ ≤ _ := by
          gcongr
          exact Nat.le_mul_of_pos_right _ (pt i)
    calc
      _ ≤ 6 * (((h i).count * fibre i : ℕ) : ℝ) := by exact_mod_cast copySize
      _ ≤ _ := by exact mul_le_mul_of_nonneg_left (hf i) (by norm_num)
  let f (i : I) (a : H i) := stripe (t i) (v i a)
  let fc (i : I) (a : H i) := Tree.fork (copies i) (f i a)
  let expanded (i : I) (a : H i) := stripe ((g i).cart (t i)) fun b => v i a b.2
  have pairs : Carries w src (stackRun h fc) :=
    coalesce h _ _ manyCopies rows
  let small (a : Sigma H) : ℝ := fibre a.1
  have positive (a : Sigma H) : 1 ≤ small a := by
    change (1 : ℝ) ≤ ↑(fibre a.1)
    exact_mod_cast (show 1 ≤ fibre a.1 from fibrePos _)
  have copyVol : Volume small (fun a : Sigma H => copies a.1) := by
    refine ⟨3, fun a => ?_⟩
    have hg : (g a.1).count ≤ fibre a.1 := Nat.le_mul_of_pos_right _ (pt _)
    change ((copies a.1).count : ℝ) ≤ 3 * (fibre a.1 : ℝ)
    exact_mod_cast (hcopies a.1).trans (Nat.mul_le_mul_left 3 hg)
  have rowVol : Volume small (fun a : Sigma H => f a.1 a.2) := by
    refine ⟨k + 2, fun a => ?_⟩
    have ht : (t a.1).count ≤ fibre a.1 := Nat.le_mul_of_pos_left _ (pg _)
    change ((stripe (t a.1) (v a.1 a.2)).count : ℝ) ≤ ((k+2 : ℕ) : ℝ) * (fibre a.1 : ℝ)
    exact_mod_cast (row_bound (t a.1) _ k (pt _) (hv a.1 a.2)).trans
      (Nat.mul_le_mul_left (k + 2) ht)
  have each : Carries small (fun a : Sigma H => fc a.1 a.2)
      (fun a => expanded a.1 a.2) := by
    apply repeatFlat (fun a : Sigma H => g a.1) (fun a => t a.1) (fun a => v a.1 a.2)
      (fun a => pg a.1) (fun a => pt a.1) k (fun a => hv a.1 a.2)
    · exact Carries.idles positive (copyVol.fork rowVol positive)
    · exact fun _ => le_rfl
  have computed : Carries w src (stackRun h expanded) := by
    apply pairs.chain
    apply (liftoff h fc expanded (fun i => (fibre i : ℝ)) each).times pairs.budget 2
    intro i
    have mulBound := hf i
    rw [Nat.cast_mul] at mulBound
    have := pairs.budget i
    norm_num
    linarith
  have unrolled := IntegerMultiplication.Strip.flatten h (fun i => (g i).cart (t i))
    (fun i x => v i x.1 x.2.2) computed
  apply repeatFlat p (fun i => (h i).cart ((g i).cart (t i)))
    (fun i x => v i x.1 x.2.2) pp _ k (fun i x => hv i x.1 x.2.2)
    (prefixCount.twice unrolled)
  · simpa only [Series.count_cart] using hm
  · intro i
    simp only [Series.count_cart]
    exact Nat.mul_pos (ph _) (fibrePos _)

end SpectralTile

end NearSquareRoot
end Computability
end OAI
