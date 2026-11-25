import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxSimulation
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSourceRun

/-! # Executing generated P192 programs on raw operand tapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet
open IntegerMultiplication.Code (Cmd Ltr)
variable [Fintype Ltr] {R : ℕ} (hR : 0 < R)

abbrev rawPair := Pipeline.srcWord Ltr.bit Ltr.sep

private theorem input_eq (p : Cmd) (x y : List Bool) :
    inputWords hR p (rawPair x y) =
      Pipeline.sourceLoad (fun b => symbol p (.bit b)) (symbol p .sep) (fixedInput hR) x y := by
  funext i
  by_cases h : i = fixedInput hR
  · subst i
    simp [inputWords, Pipeline.sourceLoad, Pipeline.load, rawPair, Pipeline.srcWord,
      Function.comp_def]
  · simp [inputWords, Pipeline.sourceLoad, Pipeline.load, h]

private theorem source_run (p : Cmd) (bound : CommonRegisters.Within R p) (x y z : List Bool)
    {r : Reg Ltr} {n cap depth : ℕ}
    (run : Space.BoundedRun cap depth [] p (fun i => if i = 0 then rawPair x y else []) n r)
    (out : r 0 = z.map Ltr.bit) :
    let m := paddedRule hR p bound
    let bit := fun b => symbol p (.bit b)
    let init := loadedConfig (entry p) none (Pipeline.sourceLoad bit (symbol p .sep) (fixedInput hR) x y)
    let steps := 2*n+1+z.length
    ∃ done, Trace (TM.advance m) init steps done ∧ TM.advance m done = none ∧
      TM.whole none (z.map bit) (done.tape none) ∧
      VisitsAtMost m init steps ((R+2)*(4*max cap depth+6)) := by
  simpa only [input_eq, out, List.length_map, List.map_map, Function.comp_def] using
    padded_run hR p bound run

private theorem decode_blank (p : Cmd) :
    Generator.PublicProgram.decode (dataNum ltrNumbering p) (fun b => symbol p (.bit b)) none = none :=
  Generator.PublicProgram.decode_blank _ _ _ (fun _ => nofun)

private theorem decode_bit (p : Cmd) (b : Bool) :
    Generator.PublicProgram.decode (dataNum ltrNumbering p) (fun v => symbol p (.bit v))
      (symbol p (.bit b)) = some b :=
  Generator.PublicProgram.decode_bit _ _ (by simp [symbol]) b

/-- Starting with the literal installed program and unexpanded operands, the
common interpreter writes all output bits to a clean tape with its head at zero. -/
theorem publicROM_run (p : Cmd) (bound : CommonRegisters.Within R p) (x y z : List Bool)
    {r : Reg Ltr} {n cap depth : ℕ}
    (run : Space.BoundedRun cap depth [] p (fun i => if i = 0 then rawPair x y else []) n r)
    (out : r 0 = z.map Ltr.bit) :
    let rom := publicROM hR p bound
    let c := blockCode ltrNumbering p
    let K := 4*(rom.length+1)
    let H := Fintype.card (Pipeline.Index (Option (FixedTapes R)))
    let e := Pipeline.expandSteps c.width x y
    let d := Pipeline.compactSteps c.width z
    let coreSpace := 2*((2*(1+5*c.width)+1)*((R+2)*(4*max cap depth+6)))
    let init := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom (Pipeline.publicLoad x y))
    let m := Universal.Loader.installAndRun (I := Pipeline.Index (Option (FixedTapes R))) (none : Public.Letter)
    ∃ t done, t ≤ 2*rom.length+3+K*(e+1+(2*clock c (2*n+1+z.length)+3)+1+d+1) ∧
      Trace (TM.advance m) init t done ∧ TM.advance m done = none ∧
      done.tape (.inl (.inl true)) = TM.Tape.loaded (.inl none) (z.map fun b => .inl (Public.bit b)) ∧
      VisitsAtMost m init t (H+2*(rom.length+1)+((2*(e+1)+H+(coreSpace+H)+(2*(d+1)+H))*(2*K+1)+2*(rom.length+2*K+1))) := by
  obtain ⟨done,tr,halt,word,vis⟩ := source_run hR p bound x y z run out
  exact Pipeline.installed_from_source (dataNum ltrNumbering p) (controlNum ltrNumbering p)
    (Padding.fixed R) (blockCode ltrNumbering p) _ (symbol p .sep) none
    (oneHot_blank _ _) _ (decode_blank p) (decode_bit p) (fixedInput hR) none
    (paddedRule hR p bound) (entry p) x y z done tr halt word vis

include hR in
/-- One fixed finite machine generates and runs a family of P192 programs.
Only the unary tape carries the parameter. The per-parameter coefficient covers
generation and simulation, and is uniform over all bounded runs on the operands. -/
theorem unary_family (p : ℕ → Cmd) (eff : Effective ltr p)
    (bound : ∀ j, CommonRegisters.Within R (p j)) {M : ℕ}
    (mark : Universal.Letter Public.Letter (Pipeline.Index (Option (FixedTapes R))))
    (distinct : Sum.inl none ≠ mark)
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option (FixedTapes R))) ≃ Fin (M+1)) :
    ∃ g : Turing.ToPartrec.Code, Finite (GeneratorInputRun.Control g M) ∧
      Finite (GeneratorInputRun.Index (Pipeline.Index (Option (FixedTapes R)))) ∧
      ∀ j, ∃ E : ℕ, 0 < E ∧ ∀ (H : ℤ) (x y z : List Bool) {r : Reg Ltr} {n cap depth : ℕ},
        Space.BoundedRun cap depth [] (p j) (fun i => if i = 0 then rawPair x y else []) n r →
        r 0 = z.map Ltr.bit →
        let m := GeneratorInputRun.rule none mark g enum
        let init := GeneratorInputRun.initial none mark g H j (Pipeline.publicLoad x y)
        ∃ t done, t ≤ E*(2*n+1+z.length+x.length+y.length+z.length+1) ∧
          Trace (TM.advance m) init t done ∧ TM.advance m done = none ∧
          done.tape (.inl ()) = Generator.Input.source (.inl none) mark H j ∧
          done.tape (.inr (.inr (.inl (.inl true)))) =
            TM.Tape.loaded (.inl none) (z.map fun b => .inl (Public.bit b)) ∧
          VisitsAtMost m init t (E*((R+2)*(4*max cap depth+6)+x.length+y.length+z.length+1)) := by
  obtain ⟨g,hg,hi,exec⟩ := GeneratorInputRun.source_family (fun j => dataNum ltrNumbering (p j))
    (fun j => controlNum ltrNumbering (p j)) (Padding.fixed R) (fun j => blockCode ltrNumbering (p j))
    (fun j b => symbol (p j) (.bit b)) (fun j => symbol (p j) .sep) (fun _ => none)
    (fun j => Generator.PublicProgram.decode _ (fun b => symbol (p j) (.bit b)))
    (fixedInput hR) none (fun j => paddedRule hR (p j) (bound j)) (fun j => entry (p j))
    (fun _ => oneHot_blank _ _) (fun j => decode_blank (p j)) (fun j => decode_bit (p j))
    mark distinct enum (computable_publicROM hR p eff bound enum)
  refine ⟨g,hg,hi,fun j => ?_⟩
  obtain ⟨E,pos,work⟩ := exec j
  refine ⟨E,pos,fun H x y z _ _ _ _ run out => ?_⟩
  obtain ⟨done,tr,halt,word,vis⟩ := source_run hR (p j) (bound j) x y z run out
  exact work H x y z done tr halt word vis

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
