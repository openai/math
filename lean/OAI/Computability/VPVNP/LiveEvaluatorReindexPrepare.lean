import OAI.Computability.VPVNP.LiveEvaluatorReindexImage

/-!
# Joining the physical prefix and runtime initialization writes

The prefix copy stops at the true length of the advised evaluator input.
The runtime skeleton starts at that address. Together these prepare the
state bank used by the exponent scatter phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorInitialize

open BurstRAM LiveEvaluatorEncoding EvaluatorProgramRawInput
open scoped Fin.CommRing

variable {w : ℕ}

/-- Adjacent completed native copies agree with a single copy of the
concatenated stream, including the case of an empty first or second piece. -/
theorem Copied.append {A R : List Bool} {base : ℕ} {m₀ m₁ m₂ : Memory w}
    (prefixCopy : Copied A base A.length m₀ m₁)
    (runtimeCopy : Copied R (base+A.length) R.length m₁ m₂) :
    Copied (A++R) base (A++R).length m₀ m₂ := by
  constructor
  · intro j hj
    rw [List.length_append] at hj
    by_cases hp : j < A.length
    · rw [runtimeCopy.outside _ (Or.inl (by omega)), prefixCopy.symbols _ hp,
        List.getElem?_append_left hp]
    · have eq : base+j = (base+A.length)+(j-A.length) := by omega
      rw [eq, runtimeCopy.symbols _ (by omega), List.getElem?_append_right (Nat.le_of_not_gt hp)]
  · intro a ha
    rw [List.length_append] at ha
    exact (runtimeCopy.outside a (by omega)).trans (prefixCopy.outside a (by omega))

/-- Native control, exact advice-prefix and runtime-skeleton writes prepare
the zero-exponent bank. The addresses here use the actual prefix length. -/
theorem prefix_runtime_stores {t Z : ℕ} (hw : 2 ≤ w) (pub : Fin 4 → Word w)
    (p : UniversalMachine.Program) (running : p.extra ≠ 0) (hs : p.extra+2 ≤ 2^w) (A : List Bool)
    (blank m₁ m₂ : Memory w)
    (space : (A ++ runtime (fun _ : Fin t => (0 : Word Z))).length ≤ (pub 0).val + 1)
    (zero : ∀ k : Fin (fieldWords (pub 0).val), blank ((pub 1).val + k.val) = 0)
    (prefixCopy : Copied A (firstData pub) A.length
      (writeMemory blank (pub 1) (Fin.ofNat _ (controlTag p).val)) m₁)
    (runtimeCopy : Copied (runtime (fun _ : Fin t => (0 : Word Z))) (firstData pub+A.length)
      (2*(t*Z)+6*Z+4) m₁ m₂) :
    Stores hw hs (pub 1).val m₂ (LiveEvaluatorTail.initialCode (pub 0).val (UniversalMachine.initial p
      (A ++ runtime (fun _ : Fin t => (0 : Word Z))))) := by
  apply copied_stores hw pub p hs _ blank m₂ space zero
  rw [activeLength, ite_eq_right running]
  exact prefixCopy.append (by simpa only [runtime_length] using runtimeCopy)

end LiveEvaluatorInitialize

end VPVNP
end Computability
end OAI
