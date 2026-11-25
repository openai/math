import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameEncoding
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameRun
import OAI.LinearAlgebra.SpectralBooks.SignedFrame.SignedFrameVerifier
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHot

/-! # The full clock, final sign and parse check in the Boolean verifier -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine ExactQuantumFactoring

noncomputable section

abbrev frameWidth (n r : ℕ) := Fintype.card (FrameWire n r)

variable {n h : ℕ}

private def startCircuit (n h r : ℕ) : BooleanNetwork (n+h) (frameWidth n r) :=
  (BooleanNetwork.select (Fin.castAdd h : Fin n → Fin (n+h))).comp (initialFrameCircuit n r)

private theorem start_eval (r : ℕ) (x : Basis n) (g : Basis h) :
    (startCircuit n h r).eval (Fin.append x g) = (Frame.initial x).encodeBits := by
  rw [startCircuit, BooleanNetwork.eval_comp, BooleanNetwork.eval_select]
  have e : Fin.append x g ∘ Fin.castAdd h = x := by funext i; simp
  rw [e, initialFrameCircuit_eval]

private def readoutCircuit (accept : BooleanNetwork (n+h) 1) :
    BooleanNetwork ((n+h)+frameWidth n 0) 2 :=
  let left := BooleanNetwork.select (Fin.castAdd (frameWidth n 0) : Fin (n+h) → _)
  let sign (o : Output) := BooleanNetwork.bit
    (Fin.natAdd (n+h) (Fintype.equivFin (FrameWire n 0) (.inl (.inl o))))
  BooleanNetwork.vector ![(left.comp accept).band (sign .pos), (left.comp accept).band (sign .neg)]

private theorem readout_score (accept : BooleanNetwork (n+h) 1) (imm : Basis (n+h))
    (bits : Basis (frameWidth n 0)) :
    let out := (readoutCircuit accept).eval (Fin.append imm bits)
    ((if out 0 then (1 : ℤ) else 0) - (if out 1 then 1 else 0)) =
      if accept.eval imm 0 then
        (if bits (Fintype.equivFin (FrameWire n 0) (.inl (.inl .pos))) then 1 else 0) -
        (if bits (Fintype.equivFin (FrameWire n 0) (.inl (.inl .neg))) then 1 else 0)
      else 0 := by
  have e : Fin.append imm bits ∘ Fin.castAdd (frameWidth n 0) = imm := by funext i; simp
  cases ha : accept.eval imm 0 <;> simp [readoutCircuit, BooleanNetwork.eval_comp, e, ha]

private theorem frame_score (f : Frame n 0) :
    ((if f.encodeBits (Fintype.equivFin (FrameWire n 0) (.inl (.inl .pos))) then (1 : ℤ) else 0) -
      (if f.encodeBits (Fintype.equivFin (FrameWire n 0) (.inl (.inl .neg))) then 1 else 0)) =
      f.output.value := by
  cases he : f.control with
  | inl o => cases o <;> simp [Frame.encode, Frame.output, he, Output.value]
  | inr q => simp [Frame.encode, Frame.output, he, Output.value]

variable (step : (r : ℕ) → BooleanNetwork ((n+h+1)+frameWidth n (r+1)) (frameWidth n r))

private theorem unroll_encoded (imm : Basis (n+h)) (t : Table n)
    (hs : ∀ r b (f : Frame n (r+1)), f.bounded →
      SignedFrame.tickEval (frameWidth n) step r imm b f.encodeBits = (f.tick t b).encodeBits)
    (r : ℕ) (b : Basis r) (f : Frame n r) (hf : f.bounded) :
    SignedFrame.run (frameWidth n) (SignedFrame.tickEval _ step) imm r b f.encodeBits =
      (Frame.run t r b f).encodeBits := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [SignedFrame.run, hs _ _ f hf, Frame.run, ih _ _ (Frame.bounded_tick ..)]

/-- Compile the full clock and reject all inputs with an invalid parse certificate. -/
def fullVerifier (accept : BooleanNetwork (n+h) 1) : BooleanNetwork (n+(h+n^100)) 2 :=
  SignedFrame.withCertificate (frameWidth n) step (n^100)
    (startCircuit n h (n^100)) (readoutCircuit accept)

/-- Over the valid parse certificate the signed count is the original path sum.
All other certificates contribute zero through the final two output gates. -/
theorem fullVerifier_coefficient (accept : BooleanNetwork (n+h) 1)
    (table : Basis h → Table n)
    (sound : ∀ x g, accept.eval (Fin.append x g) 0 = true →
      ProgramCode.decode (List.ofFn x) = some (table g).program)
    (unique : ∀ (x : Basis n) (p : Program), ProgramCode.decode (List.ofFn x) = some p →
      ∃! g : Basis h, accept.eval (Fin.append x g) 0 = true)
    (tick : ∀ x g, accept.eval (Fin.append x g) 0 = true →
      ∀ r b (f : Frame n (r+1)), f.bounded →
      SignedFrame.tickEval (frameWidth n) step r (Fin.append x g) b f.encodeBits =
        (f.tick (table g) b).encodeBits) (x : Basis n) :
    BooleanChoice.pathCoefficient (fullVerifier step accept) x = signedWitness x := by
  classical
  rw [fullVerifier, SignedFrame.pathCoefficient_withCertificate]
  simp_rw [readout_score]
  cases hd : ProgramCode.decode (List.ofFn x) with
  | none =>
    have bad (g : Basis h) : accept.eval (Fin.append x g) 0 = false := by
      cases he : accept.eval (Fin.append x g) 0
      · rfl
      · exact by cases hd.symm.trans (sound x g he)
    simp [bad, signedWitness, hd]
  | some p =>
    obtain ⟨g, hg, hall⟩ := unique x p hd
    rw [Finset.sum_eq_single g]
    · simp only [hg, ↓reduceIte, start_eval, unroll_encoded step _ (table g) (tick x g hg)
        _ _ _ (Frame.bounded_initial x), frame_score, sum_run_eq_signedWitness _ _ (sound x g hg)]
    · intro g' _ hne
      have bad : accept.eval (Fin.append x g') 0 = false := by
        cases he : accept.eval (Fin.append x g') 0
        · rfl
        · exact (hne (hall g' he)).elim
      simp [bad]
    · simp

/-- Each compiled tick is used once. Parsing is tested at both signed output wires. -/
theorem fullVerifier_count (accept : BooleanNetwork (n+h) 1) :
    (fullVerifier step accept).net.count ≤ frameWidth n (n^100) +
      (∑ r : Fin (n^100), (step r.val).net.count) + 2*(accept.net.count+1) := by
  rw [fullVerifier, SignedFrame.withCertificate_count]
  have hstart : (startCircuit n h (n^100)).net.count ≤ frameWidth n (n^100) := by
    simpa [startCircuit, BooleanNetwork.count_comp] using initialFrameCircuit_count n (n^100)
  have hend : (readoutCircuit accept).net.count = 2*(accept.net.count+1) := by
    simp [readoutCircuit, BooleanNetwork.count_comp, Fin.sum_univ_two, two_mul]
  rw [hend]
  omega

end
end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
