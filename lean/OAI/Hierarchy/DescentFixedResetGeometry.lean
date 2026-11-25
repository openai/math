import OAI.Hierarchy.DescentChosenRotorMenu

namespace OAI
/-! # Recovering the common finite reset geometry at every actual cut of the schedule -/
namespace Hierarchy.DescentSixParty
open DescentCompiler NonlinearExpanders
noncomputable section

variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {dim : ℕ} {bits : P→ℕ} {k : ℕ} {q ε : ℝ}

theorem ResetRates.same_geometry {D n h C f g cut tail D' n' h' C' f' g' cut' tail' : ℕ}
    (a : ResetRates G S k D n h C f g cut tail) (b : ResetRates G S k D' n' h' C' f' g' cut' tail')
    (same : RotorSpec.ofRates a=RotorSpec.ofRates b) :
    D=D' ∧ n=n' ∧ h=h' ∧ C=C' ∧ f=f' ∧ g=g' ∧ a.bitsR=b.bitsR ∧ HEq a.board b.board := by
  have nn := congrArg RotorSpec.n same
  have hh := congrArg RotorSpec.regularity same
  change n=n' at nn
  change h=h' at hh
  subst n'
  subst h'
  have e:=congrArg (fun spec : RotorSpec=>(⟨spec.n,spec.arcs⟩ : Σ j : ℕ,Fin (2^j)→Fin (2^j)→ℕ)) same
  have arcs : a.board.arcs=b.board.arcs:=eq_of_heq (Sigma.mk.inj e).2
  have ext (x y : Graph n h) (eqn : x.arcs=y.arcs) : x=y := by
    cases x;cases y;cases eqn;rfl
  exact ⟨congrArg RotorSpec.stageDegree same,rfl,rfl,congrArg RotorSpec.C same,
    congrArg RotorSpec.rowExponent same,congrArg RotorSpec.reserveExponent same,congrArg RotorSpec.w same,
    heq_of_eq (ext _ _ arcs)⟩

namespace Chronology
variable {W₀ W₁ W₂ : MarkedWorld F dim P bits} {i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ wire atoms : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire atoms}
    {middle : Reached W₁ G q ε S k i₁ z₁ D₁ wire atoms}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ wire atoms}

theorem Path.onlyRotor_left (before : Path first middle) (after_ : Path middle last) (op : RotorSpec)
    (same : (before.append after_).OnlyRotor op) : before.OnlyRotor op := by
  induction after_ with
  | here=>exact same
  | ordinary prev next ih=>exact ih same
  | reset prev next ih=>exact ih same.1

theorem reset_geometry_on_cut {n h C f g cut tail D' n' h' C' f' g' cut' tail' : ℕ}
    {ctl : ResetRates G S k D₁ n h C f g cut tail} (b : ClosedReset middle ctl)
    (before : Path first middle) (after_ : Path b.next last) {run : Path first last}
    (split : (before.reset b).append after_=run)
    (source : ResetRates G S k D' n' h' C' f' g' cut' tail')
    (fixed : run.OnlyRotor (RotorSpec.ofRates source)) :
    D₁=D' ∧ n=n' ∧ h=h' ∧ C=C' ∧ f=f' ∧ g=g' ∧ ctl.bitsR=source.bitsR ∧ HEq ctl.board source.board := by
  rw [←split] at fixed
  exact ctl.same_geometry source ((before.reset b).onlyRotor_left after_ _ fixed).2

end Chronology
end
end Hierarchy.DescentSixParty

end OAI
