import OAI.Hierarchy.DescentRotorSpecOfRates
import OAI.Hierarchy.DescentRotorAlphabet
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # All configured banks along a measured branch share one immutable operator menu -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentRotor
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k : ℕ}


namespace Chronology
variable {W₀ W₁ W₂ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ w t : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ w t} {middle : Reached W₁ G q ε S k i₁ z₁ D₁ w t}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ w t}

def resetSpec {n h C f g cut tail} {ctl : ResetRates G S k D₁ n h C f g cut tail} (_ : ClosedReset middle ctl) :=
  RotorSpec.ofRates ctl

def Path.OnlyRotor (x : Path first middle) (op : RotorSpec) : Prop := by
  induction x with
  | here => exact True
  | ordinary prev link ih => exact ih
  | reset prev bank ih => exact ih ∧ resetSpec bank = op

theorem Path.ordinary_rotor (x : Path first middle) (op : RotorSpec) (ordinary : x.ordinaryOnly) : x.OnlyRotor op := by
  induction x with
  | here=>trivial
  | ordinary prev _ ih=>exact ih ordinary
  | reset prev _ _=>exact ordinary.elim

theorem Path.onlyRotor_append (x : Path first middle) (y : Path middle last) (op : RotorSpec)
    (hx : x.OnlyRotor op) (hy : y.OnlyRotor op) : (x.append y).OnlyRotor op := by
  induction y with
  | here=>exact hx
  | ordinary prev _ ih=>exact ih hy
  | reset prev bank ih=>exact ⟨ih hy.1,hy.2⟩
end Chronology
end
end Hierarchy.DescentSixParty

end OAI
