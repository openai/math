import OAI.LinearAlgebra.SpectralBooks.SignedFrame.SignedFrameUnroll
import OAI.LinearAlgebra.SpectralBooks.BooleanChoice.SignedBooleanVerifier

/-! # Splitting immutable certificate bits from chronological verifier guesses -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedFrame
open ExactQuantumFactoring BooleanChoice
open scoped BigOperators

variable {n h O : ℕ} (F : ℕ → ℕ) (step : ∀ r, BooleanNetwork ((n+h+1) + F (r+1)) (F r))

/-- Input bits consist of `n` public bits followed by one private witness. Its
first `h` bits form an immutable certificate and its last `t` bits drive the ticks. -/
def withCertificate (t : ℕ) (start : BooleanNetwork (n+h) (F t))
    (readout : BooleanNetwork (n+h+F 0) O) : BooleanNetwork (n+(h+t)) O :=
  (BooleanNetwork.select (Fin.cast (Nat.add_assoc n h t))).comp (verifier F step t start readout)

theorem withCertificate_eval (t : ℕ) (start : BooleanNetwork (n+h) (F t))
    (readout : BooleanNetwork (n+h+F 0) O) (x : Fin n → Bool) (cert : Fin h → Bool) (bits : Fin t → Bool) :
    (withCertificate F step t start readout).eval (Fin.append x (Fin.append cert bits)) =
      let imm := Fin.append x cert
      readout.eval (Fin.append imm (run F (tickEval F step) imm t bits (start.eval imm))) := by
  rw [withCertificate, BooleanNetwork.eval_comp, BooleanNetwork.eval_select, ← Fin.append_assoc]
  exact verifier_eval F step t start readout _ _

theorem withCertificate_count (t : ℕ) (start : BooleanNetwork (n+h) (F t))
    (readout : BooleanNetwork (n+h+F 0) O) :
    (withCertificate F step t start readout).net.count =
      start.net.count + (∑ r : Fin t, (step r.val).net.count) + readout.net.count := by
  simp [withCertificate, BooleanNetwork.count_comp, verifier_count]

/-- The signed path count separates the sum over certificates from the sum
over chronological choices, without imposing uniqueness on either. -/
theorem pathCoefficient_withCertificate (t : ℕ) (start : BooleanNetwork (n+h) (F t))
    (readout : BooleanNetwork (n+h+F 0) 2) (x : Fin n → Bool) :
    pathCoefficient (withCertificate F step t start readout) x =
      ∑ cert : Fin h → Bool, ∑ bits : Fin t → Bool,
        let imm := Fin.append x cert
        let output := readout.eval (Fin.append imm (run F (tickEval F step) imm t bits (start.eval imm)))
        ((if output 0 then (1:ℤ) else 0) - (if output 1 then 1 else 0)) := by
  unfold pathCoefficient
  rw [← (Fin.appendEquiv h t).sum_comp, Fintype.sum_prod_type]
  have he (y : (Fin h → Bool) × (Fin t → Bool)) :
      Fin.appendEquiv h t y = Fin.append y.1 y.2 := rfl
  simp only [he, withCertificate_eval]

end SignedFrame

end SpectralBooks
end LinearAlgebra
end OAI
