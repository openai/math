import OAI.Optimization.LinearProgramming.Recovery.InitialPairRun

/-! One physical callable fragment runs the public LP layout and then the first
row/complement computation, on the two banks produced by the common parity boot. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Call RAM.Callable RAM.Tape Geometry
open scoped Matrix

/-- The result carries the exact contiguous [rank,nullity] subspace-call tape, a
reusable even-bank footprint, and the undisturbed original LP on the odd bank. -/
theorem fragment_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    let E := max 3 (totalBits (lpInput A b))
    let W := fragmentWidth m d E
    ∃ (front back : Memory ℚ) (k s : ℕ) (F : Matrix (Fin k) (Fin (m+1)) ℚ) (R : Matrix (Fin s) (Fin (m+1)) ℚ),
      fragment.Run (fun x => ratBits x ≤ W) (Odd.memory blank (start [m,d] (lpInput A b)).memory)
        (fragmentTime m d) (Odd.memory front back) ∧
      PairBuilder.Within W front ∧ PairBuilder.Within W back ∧
      Footprint (PairBuilder.capacity (d+1) (m+1) 0-1) (front.atPC 0) ∧ Retained A b back ∧
      PairBuilder.Prepared false (layout m d) (slackColumns A b)ᵀ F R back ∧ k ≤ d+1 ∧
      (∀ i j, ratBits (F i j) ≤ PairBuilder.rowWidth (d+1) (m+1) E) ∧
      ∀ i j, ratBits (R i j) ≤ PairBuilder.rowWidth (m+1) (m+1)
        (PairBuilder.residualWidth (m+1) (m+1) (PairBuilder.rowWidth (d+1) (m+1) E)) := by
  let E := max 3 (totalBits (lpInput A b))
  let W := fragmentWidth m d E
  have E3 : 3 ≤ E := le_max_left _ _
  have EW : E ≤ W := le_max_left _ _
  have W3 := E3.trans EW
  have zero : ratBits (0 : ℚ) ≤ W := (by decide : ratBits (0 : ℚ) ≤ 3).trans W3
  have one : ratBits (1 : ℚ) ≤ W := (by decide : ratBits (1 : ℚ) ≤ 3).trans W3
  have entry : ∀ i j, ratBits ((slackColumns A b)ᵀ i j) ≤ E := by
    obtain ⟨_,_,_,_,_,bound⟩ := program_tape_spec A b
    exact bound
  obtain ⟨caller,c,clock,logical,ready⟩ := program_spec A b (fun q => ratBits q ≤ W) zero one
    (fun q h => by simpa only [PrimalDual.ratBits_neg] using h)
    (fun i => (tape_height A b i).trans EW)
  have lifted := Odd.leaf_run (fun q => ratBits q ≤ W) blank (blank_within W3) logical
  obtain ⟨front,back,k,s,F,R,pair,hf,hb,foot,frame,prepared,rank,bitsF,bitsR⟩ :=
    run_from_ready A b caller W E ready W3 logical.safe_end entry
  have same : max W (PairBuilder.pairWidth (d+1) (m+1) E)=W := max_eq_left (le_max_right _ _)
  simp only [same] at pair hf hb
  have whole := lifted.seq pair
  refine ⟨front,back,k,s,F,R,whole.mono ?_,hf,hb,foot,retained_after_pair ready frame,
    prepared,rank,bitsF,bitsR⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 (clock.trans (stepBound_le m d))) _

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
