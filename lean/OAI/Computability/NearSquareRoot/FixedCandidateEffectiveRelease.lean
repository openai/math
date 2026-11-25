import OAI.Computability.NearSquareRoot.FixedCandidateEffective
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveGuard
import OAI.Computability.NearSquareRoot.FixedCandidateClock

/-! # Effective command files for the complete guarded multiplication candidates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code CommonRegisters GeneratorSyntax EffectiveBoundedTask Filter

variable {P : Type} [Primcodable P]

/-- The outer code generator computes every candidate file, including its
threshold test and both control branches. All the files use one finite set of
data registers, and their certified outputs are the canonical MSF words. -/
theorem effective_multiplier (K : P → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (plan : ∀ p i, Plan (hv p i)) (c : P → Clocks) (ops : EffectiveTransports K hv plan c) :
    Family (fun p (i : MultiplicationInput) => i.width+(c p).total i.width) (fun _ i => 21*i.width)
      (fun _ i => send i.operands) (fun _ i => send (Lea.answer i.operands)) :=
  effective_all_widths K hK (fun p => (c p).total) (effective_largeTask K hv plan c hN ops)

/-- Program files, resource certificates for those exact files, and the
per-parameter exponents. Each running-time estimate allows its parameter's own
constant. The register bound precedes every candidate and every input. -/
theorem effective_candidate_files (K : P → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (plan : ∀ p i, Plan (hv p i)) (c : P → Clocks) (ops : EffectiveTransports K hv plan c)
    (γ : P → ℝ) (hg : ∀ p, 0 < γ p)
    (hc : ∀ p clock, clock ∈ [(c p).route,(c p).forward,(c p).inverse] →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (clock n : ℝ) ≤ C*n*logScale n^(γ p)) :
    ∃ (cmd : P → Cmd) (R : ℕ) (T : P → ℕ → ℕ), Effective ltr cmd ∧ 0 < R ∧ ∀ p,
      Within R (cmd p) ∧ Runs (cmd p) (fun i : MultiplicationInput => T p i.width)
        (fun i => 21*i.width) (fun i => send i.operands) (fun i => send (Lea.answer i.operands)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (T p n : ℝ) ≤ C*n*logScale n^(γ p)) := by
  obtain ⟨cmd,R,he,hR,hm⟩ := effective_multiplier K hK hN hv plan c ops
  refine ⟨cmd,R,fun p n => n+(c p).total n,he,hR,fun p => ⟨(hm p).1,(hm p).2,?_⟩⟩
  obtain ⟨C,hC,h⟩ := (c p).eventually_total (hg p) (hc p)
  obtain ⟨D,hD,hd⟩ := affine_io_eventually (hg p).le hC h 1
  refine ⟨D,hD,?_⟩
  filter_upwards [hd] with n hn
  apply le_trans _ hn
  exact_mod_cast (show n+(c p).total n ≤ 1*((c p).total n+n+1) by omega)

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
