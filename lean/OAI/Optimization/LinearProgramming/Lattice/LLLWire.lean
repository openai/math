import OAI.Optimization.LinearProgramming.Lattice.QueryWire
import OAI.Optimization.LinearProgramming.Lattice.QueryTheorem
import OAI.Optimization.LinearProgramming.Lattice.LLLRounding

/-! The concrete native LLL sign-rounding algorithm, with the repository's serialized wire format. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open OracleSpec SignType

/-- Ternary comparison responses in the bit oracle have the usual sign interpretation. -/
def orderOfSign : SignType → Ordering | .neg => .lt | .zero => .eq | .pos => .gt

private theorem orderOfSign_test (s : SignType) : decide (orderOfSign s ≠ .lt) = decide (0 ≤ s) := by
  cases s <;> rfl

/-- Run the concrete algorithm on serialized, signed requests and replies; serialize its final
integer vector in the same fixed-dimension format. -/
def lllRoundWords {p : ℕ} (M : ℕ) (oracle : WordOracle) : Option (Word × Transcript) :=
  (SignQueries.runWords oracle (lllRoundingProgram p M) []).map fun (z,tr) ↦ (signRowWord z, tr)

/-- Any concrete, possibly history-dependent bit oracle agreeing on valid packets yields exactly
the same serialized run. Its replies to malformed packets may be arbitrary. -/
theorem lllRoundWords_on_valid_packets {p : ℕ} (M : ℕ) (so : (Fin p → ℤ) → Ordering)
    (wire : WordOracle) (hs : ∀ tr a, wire tr (signRowWord a) = signReply (so a)) :
    lllRoundWords (p := p) M wire = lllRoundWords (p := p) M (wordSignOracle so) := by
  have go {α : Type} (t : SignQueries p α) (tr : Transcript) :
      SignQueries.runWords wire t tr = SignQueries.runWords (wordSignOracle so) t tr := by
    induction t generalizing tr with
    | done x => rfl
    | ask a next ih => simp [SignQueries.runWords, hs, ih]
  unfold lllRoundWords
  rw [go]

/-- The actual returned word decodes to a sign-preserving integer vector. The two explicit
polynomials bound its output length and the total bits sent and received during the computation. -/
theorem lllRoundWords_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℝ)
    (oracle : (Fin p → ℤ) → SignType) (hv : ∀ c, oracle c = sign (dotProduct (realCoordinates c) v)) :
    let so := fun c ↦ orderOfSign (oracle c)
    ∃ (out : Word) (tr : Transcript) (z : Fin p → ℤ),
      lllRoundWords (p := p) M (wordSignOracle so) = some (out,tr) ∧ readSignRow p out = some (z,[]) ∧
      out.length ≤ p*(2*(radixWidth p M*p)+2) ∧
      communicationBits tr ≤ p*(2*p+1+p*searchPrecision p M) * (p*(2*queryCoefficientWidth p M+2)+2) ∧
      emitAskCost tr ≤ p*(2*p+1+p*searchPrecision p M) * (2*(p*(2*queryCoefficientWidth p M+2))+3) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  intro so
  let s := signNonnegative so
  let t := lllRoundingProgram p M
  let z := SignQueries.run s t
  have he : s = fun c ↦ decide (0 ≤ oracle c) := funext fun c ↦ orderOfSign_test (oracle c)
  have hh := lllRoundingProgram_correct hp hM v oracle hv
  rw [← he] at hh
  have hc : ∀ c, s c = true ↔ 0 ≤ formValue c v := by
    intro c; rw [he]; simp only [decide_eq_true_eq, hv, sign_nonneg_iff]; rfl
  have hio := roundingProgramWith_communication hp hM (lllShortSelector M) (lllShortSelector_correct hp hM) v so hc
  refine ⟨signRowWord z, SignQueries.wireTranscript so t, z, ?_, ?_, ?_, hio.1, hio.2, hh.2.2.2⟩
  · unfold lllRoundWords
    rw [SignQueries.runWords_eq, List.append_nil]
    rfl
  · simpa using readSignRow_append z []
  · rw [signRowWord_length]
    calc
      _ ≤ ∑ _ : Fin p, (2*(radixWidth p M*p)+2) := Finset.sum_le_sum fun i _ ↦ by
        have h := hh.2.2.1 i
        change (z i).natAbs.size ≤ _ at h
        omega
      _ = _ := by simp

private theorem wire_parameter_bounds (p M : ℕ) :
    let bound := 110000*(p+M.size+12)^13
    let calls := p*(2*p+1+p*searchPrecision p M)
    let packet := p*(2*queryCoefficientWidth p M+2)
    p*(2*(radixWidth p M*p)+2) ≤ bound ∧ calls*(packet+2) ≤ bound ∧ calls*(2*packet+3) ≤ bound := by
  let X := p + M.size + 12
  let B := 100 * X^6
  let packet := p*(2*queryCoefficientWidth p M+2)
  obtain ⟨hcall,hwidth,hout⟩ := rounding_parameter_bounds p M
  have hB : 0 < B := by dsimp [B,X]; positivity
  have hX : p ≤ X := by dsimp [X]; omega
  have hXB : 0 < X*B := Nat.mul_pos (by dsimp [X]; omega) hB
  have hsize (w : ℕ) (hw : w ≤ B) : p*(2*w+2) ≤ 4*(X*B) := by
    calc
      _ ≤ X*(4*B) := Nat.mul_le_mul hX (by omega)
      _ = _ := by ring
  have hpa : packet ≤ 4*(X*B) := hsize _ hwidth
  have hc : B*(11*(X*B)) = 110000*X^13 := by dsimp [B]; ring
  change _ ≤ 110000*X^13 ∧ _ ≤ 110000*X^13 ∧ _ ≤ 110000*X^13
  rw [← hc]
  constructor
  · have h := hsize _ hout
    exact h.trans ((show 4*(X*B) ≤ 11*(X*B) by omega).trans (Nat.le_mul_of_pos_left _ hB))
  constructor
  · exact Nat.mul_le_mul hcall (show packet+2 ≤ 11*(X*B) by omega)
  · exact Nat.mul_le_mul hcall (show 2*packet+3 ≤ 11*(X*B) by omega)

/-- One fixed polynomial in dimension and the bit length of `M` bounds the encoded output,
all oracle-boundary communication, and the `emit`/`ask` share of the finite machine cost. -/
theorem lllRoundWords_polynomial {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℝ)
    (oracle : (Fin p → ℤ) → SignType) (hv : ∀ c, oracle c = sign (dotProduct (realCoordinates c) v)) :
    let so := fun c ↦ orderOfSign (oracle c)
    let bound := 110000*(p+M.size+12)^13
    ∃ (out : Word) (tr : Transcript) (z : Fin p → ℤ),
      lllRoundWords (p := p) M (wordSignOracle so) = some (out,tr) ∧ readSignRow p out = some (z,[]) ∧
      out.length ≤ bound ∧ communicationBits tr ≤ bound ∧ emitAskCost tr ≤ bound ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  obtain ⟨out,tr,z,hr,hd,hle,hc,he,hz⟩ := lllRoundWords_correct hp hM v oracle hv
  obtain ⟨blo,blc,ble⟩ := wire_parameter_bounds p M
  exact ⟨out,tr,z,hr,hd,hle.trans blo,hc.trans blc,he.trans ble,hz⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
