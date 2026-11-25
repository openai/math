import OAI.Computability.BorderVNP.DiagonalStagedChart
import OAI.Computability.BorderVNP.TeamContractionLayout
import OAI.Computability.BorderVNP.DiagonalEvaluator

/-! # The concrete row expansion and live-column target for the fixed processor

Both equalities refer to the same programmed literals and physical wiring.
Every term records each selected parameter bit and the multiplicity of every
original scalar table position, even if that position contains zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch ResiduePins ResidueBox MvPolynomial
open scoped Classical BigOperators

variable {E Gadget Edge : Type} [Field E] [Fintype Gadget] [Fintype Edge]
variable {p d k s H Q pin : ℕ} [Fact p.Prime] [Algebra (ZMod p) E]

/-- Output required of the physical processor construction. The same placed
and programmed wiring computes the live universal-machine counts and the
numbered table polynomial. -/
structure RealizedBranchColumn (B : Module.Basis (Fin d) (ZMod p) E) (hQ : 0 < Q)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (g : Fin (pairedTableParameters (k+1) s) →
      MvPolynomial (Option (Fin (pairedTableParameters (k+1) s))) E)
    (values : Gadget → E) (hd : d ≤ 2^pin) (hH : 2*H < 2^pin)
    (star : Index (Fin d) (Fin (pairedTableParameters (k+1) s)) H)
    (teamsPred r t link inner : ℕ) (Edge : Type) [Fintype Edge] where
  /-- Literal bits and every real wire index of the programmed processor input. -/
  wiring : TeamContraction.Wiring teamsPred r t ((pairedTableParameters (k+1) s+2)*pin)
    link inner (k+1) Edge
  /-- Choices left free after fixing the substituted pin. -/
  Path : Index (Fin d) (Fin (pairedTableParameters (k+1) s)) H → Type
  [pathFinite : ∀ i, Fintype (Path i)]
  /-- Powers and table occurrences seen on each physical assignment. -/
  assigned : ∀ i, Path i → Tally (Fin (teamsPred+1)) (Fin (pairedTableParameters (k+1) s))
    Gadget (Nat.clog 2 (r*(2*k+1)+1))
  /-- Equation (11.2) on the substituted pin. -/
  expansion : ∀ i, numberedSubstituted E k s ord wiring.slot
    ((boxPinCodec (pairedTableParameters (k+1) s) hd hH).encode i) =
      ∑ j, monomial (assigned i j).exponents ((assigned i j).coefficient values)
  /-- Equation (11.3) on the live pin, evaluated by the same literal program. -/
  column : ∀ j, (signedContraction wiring.slot
      ((boxPinCodec (pairedTableParameters (k+1) s) hd hH).encode j) : ZMod p) =
      (if j = star then 1 else 0) + ∑ i, ∑ a, entryWeight p B H Q hQ g
        (assigned i a).exponents i j ((assigned i a).coefficient values)

attribute [instance] RealizedBranchColumn.pathFinite

/-- A realized column would contradict the actual arithmetic branch at its
distinguished pin. The fixed processor must supply both displayed equalities
for this very wiring in order to invoke the contradiction. -/
theorem RealizedBranchColumn.contradiction
    {B : Module.Basis (Fin d) (ZMod p) E} {hQ : 0 < Q}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {g : Fin (pairedTableParameters (k+1) s) →
      MvPolynomial (Option (Fin (pairedTableParameters (k+1) s))) E}
    {values : Gadget → E} {hd : d ≤ 2^pin} {hH : 2*H < 2^pin}
    {star : Index (Fin d) (Fin (pairedTableParameters (k+1) s)) H}
    {teamsPred r t link inner : ℕ}
    (col : RealizedBranchColumn B hQ ord g values hd hH star teamsPred r t link inner Edge)
    (fail : ColumnFailure (Pin := Fin ((pairedTableParameters (k+1) s+2)*pin))
      (Wire := Layout.Wire teamsPred r link Edge) B H Q hQ (teamsPred+1) r k s ord g star) : False := by
  obtain ⟨j,hj⟩ := fail col.wiring.slot (boxPinCodec (pairedTableParameters (k+1) s) hd hH).encode
    col.Path (fun i a => (col.assigned i a).exponents)
    (fun i a => (col.assigned i a).coefficient values) col.expansion
  exact hj (col.column j)

end Diagonal

end BorderVNP
end Computability
end OAI
