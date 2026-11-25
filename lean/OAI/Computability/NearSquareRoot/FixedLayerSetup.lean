import OAI.Computability.NearSquareRoot.FixedLayerFrame
import OAI.Computability.NearSquareRoot.PrecisionActualPhaseClock
import OAI.Computability.NearSquareRoot.PrecisionDigitInput

/-! # Constructing a polynomial schedule from an operand-width ruler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code Space FixedCandidate DigitPacking FixedPoint Brief

private theorem widthRuler {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i) :
    BoundedTask n n (fun i => send (tally (n i))) (fun i => send (tally (addressBits (n i)))) := by
  have volume : Volume (measure n) (fun i => send (tally (n i))) := by
    refine ⟨3,fun i => ?_⟩
    change (size (tally (n i)) : ℝ) ≤ 3*((n i : ℝ)+1)
    rw [size_tally,tally_length]
    push_cast
    linarith
  have bin : Carries (measure n) (fun i => send (tally (n i))) (journals n).header := by
    have h := Carries.func (y := fun i => tally (n i)) (here n) volume _ Carry.easy_chart
    change Carries _ _ (fun i => send (Carry.born (n i)))
    simpa only [tally_length] using h
  have h := bin.chain (header_addressBits n hn)
  have h' : Carries (fun i => ((n i+1 : ℕ):ℝ)) (fun i => send (tally (n i))) (fun i => send (tally (addressBits (n i)))) := by simpa [Brief.measure] using h
  exact (Controlled.boundedOfCarries h').bound 2 2 (fun _ => by omega) (fun _ => by omega)

/-- The polynomial output occupies linear volume in the original operand
length, including on the smallest widths satisfying the packing bounds. -/
theorem headerVolume {I X : Type} [Codec X] (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (E : Tally → X) (poly : Poly E) :
    ∃ K : ℕ, ∀ i, size (E (tally (addressBits (n i)))) ≤ K*(n i+1) := by
  let k i := addressBits (n i)
  have tiny : Dom k (fun i => size (tally (k i))) := ⟨1,3,by intro i; simp [size_tally]; omega⟩
  obtain ⟨B,hB⟩ := setup_le_array ((poly.length.map (fun i => tally (k i))).sub tiny)
  refine ⟨B*192,fun i => ?_⟩
  have v : 2^k i ≤ 192*(n i+1) := by
    have h := array_volume (hn i)
    change (2^k i+1)*(k i+1) ≤ _ at h
    exact (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)).trans
      (h.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
  exact (hB i).trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ v)

/-- One fixed command computes the selected header, while keeping all
array records and the original operand length together on the other stack. -/
theorem prepareHeader {I X : Type} [Codec X] (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (E : Tally → X) (poly : Poly E) (x : (i : I) → Array (n i)) :
    BoundedTask n n (fun i => framed (x i))
      (fun i => .fork (send (E (tally (addressBits (n i))))) (framed (x i))) := by
  let k i := addressBits (n i)
  have tiny : Dom k (fun i => size (tally (k i))) := ⟨1,3,by intro i; simp [size_tally]; omega⟩
  obtain ⟨b,hb,run⟩ := poly.on tiny
  obtain ⟨D,cap⟩ := setup_le_array hb
  have vol i : 2^k i ≤ 192*(n i+1) := by
    have v := array_volume (hn i)
    change (2^k i+1)*(k i+1) ≤ _ at v
    exact (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)).trans
      (v.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
  have price i : b i ≤ (D*192)*(n i+1) := by
    rw [Nat.mul_assoc]
    exact (cap i).trans (Nat.mul_le_mul_left _ (vol i))
  have header := (BoundedTask.of_time run).bound (time' := n) (space' := n)
    (D*192+1) (D*192+577) (fun i => by have := price i; rw [Nat.add_mul]; omega) (fun i => by
      have h := price i
      have g := array_volume (hn i)
      have w : k i+1 ≤ 192*n i := (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans g
      change size (tally (k i)) + b i + 1 ≤ _
      simp only [size_tally,tally_length,Nat.add_mul]
      omega)
  have raw := sequence (widthRuler n hn) header
  have paired := (raw.left (fun i => framed (x i))).bound (time' := n) (space' := n)
    1 75002 (fun _ => by simp) (fun i => by have := framed_size (hn i) (x i); omega)
  have duplicate := linearTree (fun a : Tally × List Dusk.Pair => (a.1,a))
    (Easy.fst.pair Easy.identity) (fun i => (tally (n i),records (x i))) 75000 (fun _ => le_rfl)
    (fun i => framed_size (hn i) (x i))
  exact sequence duplicate paired

end FixedLayer

end NearSquareRoot
end Computability
end OAI
