import OAI.Computability.NearSquareRoot.CRTPositionCommand
import OAI.Computability.NearSquareRoot.CRTPositionNamedOpcode
import OAI.Computability.NearSquareRoot.CRTPositionEffectiveTable
import OAI.Computability.NearSquareRoot.FixedCandidateBoxCutoff

/-! # The register-bounded native position-permutation source -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom CommonRegisters GeneratorSyntax

/-- The only candidate-dependent child command is the rectangular interchanger.
The two reserve coefficients and their associated cutoff are literal integers. -/
noncomputable def routeCmd (low high : ℕ) (rectangle : Cmd) : Cmd :=
  PositionCmd.positionCmd (FixedCandidate.boxCutoff low high) low high (tableCmd (opcodeCmd rectangle))

theorem routeCmd_effective {P : Type} [Primcodable P] {a b : P → ℕ} {rect : P → Cmd}
    (ha : Computable a) (hb : Computable b) (ec : GeneratorSyntax.Effective ltr rect) :
    GeneratorSyntax.Effective ltr (fun j => routeCmd (a j) (b j) (rect j)) :=
  PositionCmd.position_effective (FixedCandidate.boxCutoff_primrec.to_comp.comp ha hb) ha hb (tableCmd_effective (opcodeCmd_effective ec))

theorem routeCmd_within (R : ℕ) :
    ∃ S, 0<S ∧ ∀ a b c, Within R c → Within S (routeCmd a b c) := by
  obtain ⟨r,_,op⟩ := opcodeCmd_within R
  obtain ⟨s,_,tab⟩ := tableCmd_within r
  obtain ⟨t,pos,top⟩ := PositionCmd.position_within s
  exact ⟨t,pos,fun a b c hc => top _ a b _ (tab _ (op c hc))⟩

/-- A single pair of sufficiently large reserve degrees serves all input
permutations and all positive-width arrays for the supplied rectangle program. -/
theorem routeCmd_runs {ρ : ℝ} {rect : Cmd} (positive : 0 ≤ ρ) (ready : Effective.rectContract rect ρ) :
    ∃ D : ℕ, ∀ a b, D ≤ a → D ≤ b → ⌈ρ⌉₊+2 ≤ b →
      ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i:I) → Series (U i)), (∀ i, 0 < (u i).count) →
        ∀ (p : (i:I) → Equiv.Perm (Fin (k i))) (f : (i:I) → Block 2 (k i) → U i → Bead),
          PositionCmd.PositionRuns (routeCmd a b rect) ρ k u p f := by
  have inner := tableCmd_grouped positive (opcodeCmd_runs positive ready)
  obtain ⟨D,go⟩ := PositionCmd.position_runs_from_cutoff positive _ inner
  exact ⟨D,fun a b ha hb bound => go a b _ ha hb bound (fun _ h => FixedCandidate.position_reserves_of_cutoff h.le)⟩

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
