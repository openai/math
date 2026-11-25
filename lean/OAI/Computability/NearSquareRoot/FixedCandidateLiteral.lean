import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveRelease
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxMultipliers

/-! # Literal public ROM files and the fixed machine running each candidate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code GeneratorSyntax GeneratorSyntax.Pack CommonAlphabet Filter
open EffectiveBoundedTask

abbrev PublicTapes (R : ℕ) := Pipeline.Index (Option (FixedTapes R))
abbrev SourceTag (R : ℕ) := Universal.Tag Public.Letter (PublicTapes R)
abbrev sourceMarker (R : ℕ) : Universal.Letter Public.Letter (PublicTapes R) := .inr .origin

/-- One encoding shared by the literal programs, their physical loader and
input generator, and all execution traces. Each candidate's time and visited-cell
coefficients are independent of its input words and the location of its index. -/
structure LiteralFamily (T : ℕ → ℕ → ℕ) where
  registers : ℕ
  positive : 0 < registers
  cmd : ℕ → Cmd
  effective : Effective ltr cmd
  bounded : ∀ j, CommonRegisters.Within registers (cmd j)
  coeff : ℕ → ℕ
  body : ∀ j, MultiplicationBody (cmd j) (T j) 21 (coeff j) (fun i => Lea.answer i.operands)
  lastTag : ℕ
  enumeration : SourceTag registers ≃ Fin (lastTag+1)
  files : Computable fun j =>
    (publicROM positive (multiplyWrap (cmd j)) (within_multiplyWrap positive (bounded j))).map
      (fun t => (enumeration t).val)
  generator : Turing.ToPartrec.Code
  finiteControl : Finite (GeneratorInputRun.Control generator lastTag)
  finiteAlphabet : Finite (Universal.Letter Public.Letter (PublicTapes registers))
  finiteTapes : Finite (GeneratorInputRun.Index (PublicTapes registers))
  trace : ∀ j, ∃ E D : ℕ, ∀ (H : ℤ) (i : MultiplicationInput),
    let m := GeneratorInputRun.rule none (sourceMarker registers) generator enumeration
    let init := GeneratorInputRun.initial none (sourceMarker registers) generator H j
      (Pipeline.publicLoad i.operands.1 i.operands.2)
    let z := Lea.answer i.operands
    ∃ t done, t ≤ E*(T j i.width+i.width+1) ∧ Trace (TM.advance m) init t done ∧
      TM.advance m done = none ∧
      done.tape (.inl ()) = Generator.Input.source (.inl none) (sourceMarker registers) H j ∧
      done.tape (.inr (.inr (.inl (.inl true)))) =
        TM.Tape.loaded (.inl none) (z.map fun b => .inl (Public.bit b)) ∧
      z.length = 2*i.width ∧ bitValue z = bitValue i.operands.1*bitValue i.operands.2 ∧
      VisitsAtMost m init t (D*i.width)

/-- Register an effective family of certified arithmetic bodies in the physical
public-ROM interpreter. The register alphabet, unary number marker and finite
numbering of all literal tag values are shared by every candidate. -/
theorem literal_of_effective {T : ℕ → ℕ → ℕ}
    (runs : Family (fun j (i : MultiplicationInput) => T j i.width) (fun _ i => 21*i.width)
      (fun _ i => send i.operands) (fun _ i => send (Lea.answer i.operands))) :
    Nonempty (LiteralFamily T) := by
  classical
  obtain ⟨cmd,R,he,hR,h⟩ := runs
  have within (j : ℕ) := (h j).1
  choose cost body using fun j => (h j).2
  let _ : Fintype (SourceTag R) := Fintype.ofFinite _
  let _ : Nonempty (SourceTag R) := ⟨.origin⟩
  let last := Fintype.card (SourceTag R) - 1
  have card : Fintype.card (SourceTag R) = last+1 := by
    dsimp [last]
    have := Fintype.card_pos (α := SourceTag R)
    omega
  let en := Fintype.equivFinOfCardEq card
  have out (_j : ℕ) (i : MultiplicationInput) : (Lea.answer i.operands).length = 2*i.width ∧
      bitValue (Lea.answer i.operands) = bitValue i.operands.1 * bitValue i.operands.2 :=
    ⟨Lea.date_length _, Lea.value_answer i.val.property⟩
  obtain ⟨g,ctl,tapes,trace⟩ := unary_multipliers hR cmd he within T (fun _ => 21) cost
    (fun _ i => Lea.answer i.operands) body out (sourceMarker R) (by intro h; cases h) en
  exact ⟨⟨R,hR,cmd,he,within,cost,body,last,en,computable_publicROM hR _ (effective_multiplyWrap he)
    (fun j => within_multiplyWrap hR (within j)) en,g,ctl,inferInstance,tapes,trace⟩⟩

/-- The generated complete arithmetic candidates as literal public ROM files. -/
theorem literal_of_transports (K : ℕ → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (plan : ∀ p i, Plan (hv p i)) (c : ℕ → Clocks) (ops : EffectiveTransports K hv plan c) :
    Nonempty (LiteralFamily (fun p n => n+(c p).total n)) :=
  literal_of_effective (effective_multiplier K hK hN hv plan c ops)

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
