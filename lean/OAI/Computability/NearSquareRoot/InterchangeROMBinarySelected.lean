import OAI.Computability.NearSquareRoot.InterchangeROMBinarySelectedCore
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryParts
import OAI.Computability.NearSquareRoot.InterchangeROMFamily

/-! # Selected binary rectangle commands for the interchange exponents -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Selected

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

/-- The same degree and the same register file serve all selected exponents. -/
theorem ofFamily {J : Type} [Primcodable J] (b p : J → ℕ) (hb : Computable b)
    (large : ∀ j, Net.Shuttle.base ≤ b j) (primeSize : ∀ j, 2 ≤ p j)
    (ρ : J → ℝ) (rate : ∀ j, 0 ≤ ρ j) (c : J → Cmd) (eff : Effective ltr c)
    (R : ℕ) (reg : ∀ j, Within R (c j)) (k : ℕ) (native : ∀ j, Native (b j) (p j) k (ρ j) (c j)) :
    ∃ (D H : ℕ) (cmd : J → Cmd), Effective ltr cmd ∧
      ∀ j, Within H (cmd j) ∧ RectPhysical (cmd j) (ρ j) D := by
  obtain ⟨t,pre,post,hpre,hpost⟩ := Ticket.parts k
  exact compile k (Ticket.request k) (fun _ h => Ticket.request_valid k h) (Ticket.request_volume k)
    (fun _ => rfl) t pre post hpre hpost b p hb large primeSize ρ rate c eff R reg native

/-- Instantiate the binary compiler at the selected field, radix and native
controller for each requested interchange exponent. -/
theorem ofNative (F : InterchangeROMFamily.NativeFamily) :
    ∃ (D R : ℕ) (cmd : ℕ → Cmd), Effective ltr cmd ∧
      ∀ j, Within R (cmd j) ∧ RectPhysical (cmd j) (Generator.targetExponent j) D := by
  let index (j : ℕ) : InterchangeROMFamily.Index := (j,Net.Shuttle.base)
  have ci : Computable index := Computable.id.pair (Computable.const _)
  let select (j : ℕ) := InterchangeROMFamily.selected (index j)
  have hs : Computable select := InterchangeROMFamily.computable_selected.comp ci
  exact ofFamily (fun j => (select j).b) (fun j => (select j).p)
    ((Interchange.Template.Data.primrec_header 1).to_comp.comp hs)
    (fun j => (InterchangeROMFamily.NativeFamily.geometry (index j)).2.2.2.le)
    (fun j => (InterchangeROMFamily.NativeFamily.geometry (index j)).2.1.le)
    Generator.targetExponent (fun j => by unfold Generator.targetExponent; positivity)
    (F.command ∘ index) (F.effective.comp ci) F.registers (fun j => F.within (index j)) F.degree
    (fun j => F.run (index j))

end InterchangeROMBinary.Selected

end NearSquareRoot
end Computability
end OAI
