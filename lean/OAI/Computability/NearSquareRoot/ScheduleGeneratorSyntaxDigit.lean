import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPublicRun

/-! # Direct public machines for register-bounded digit commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet
open IntegerMultiplication.Code (Cmd Ltr)

variable [Fintype Ltr]

/-- The two public heads accompany the padded source bank and its alignment tape. -/
abbrev DigitIndex (R : ℕ) := Pipeline.Index (Option (FixedTapes R))

abbrev DigitControl (R : ℕ) (p : Cmd) :=
  Pipeline.SourceControl (Data p) (Control p) (FixedTapes R) (blockCode ltrNumbering p).width

def digitIndexNum (R : ℕ) : Numbering (DigitIndex R) :=
  Numbering.publicIndex (Padding.fixed R).option

noncomputable def digitNum (R : ℕ) (p : Cmd) : Numbering (DigitControl R p) :=
  let a := dataNum ltrNumbering p
  let q := controlNum ltrNumbering p
  let w := (blockCode ltrNumbering p).width
  Numbering.pipeline a (Numbering.controller a q (Padding.fixed R) w).align w

noncomputable def digitEntry (R : ℕ) (p : Cmd) : DigitControl R p :=
  Pipeline.sourceEntry (Data p) (Control p) (FixedTapes R) (blockCode ltrNumbering p).width

/-- The digit rule operates directly on literal four-letter tapes, including input
expansion, physical head alignment and output compaction. -/
noncomputable def digitMachine {R : ℕ} (hR : 0 < R) (p : Cmd) (bound : CommonRegisters.Within R p) :
    TM.Rule Public.Letter (DigitControl R p) (DigitIndex R) :=
  let a := dataNum ltrNumbering p
  let bit := fun b => symbol p (.bit b)
  Pipeline.sourceMachine (blockCode ltrNumbering p) bit (symbol p .sep)
    (Generator.PublicProgram.decode a bit) (fixedInput hR) none (paddedRule hR p bound) (entry p)

@[simp] theorem digitEntry_rank (R : ℕ) (p : Cmd) :
    ((digitNum R p).equiv (digitEntry R p)).val = 0 := rfl

theorem computable_digitSize {R : ℕ} (hR : 0 < R) (p : ℕ → Cmd)
    (eff : Effective ltr p) (bound : ∀ j, CommonRegisters.Within R (p j)) :
    Computable fun j => (digitNum R (p j)).size := by
  obtain ⟨ha,hq,_⟩ := paddedRows ltrNumbering hR p eff bound
  let a := fun j => dataNum ltrNumbering (p j)
  let q := fun j => controlNum ltrNumbering (p j)
  let c := fun j => blockCode ltrNumbering (p j)
  have hw : Computable fun j => (c j).width := ha
  have hctrl := (Generator.Phase.states a q (Padding.fixed R) (fun j => (c j).width) ha hq hw).size_eff
  open Generator.PipelineRows in
  exact Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp (computable_expand_size a c ha hw) (computable_align_size _ hctrl))
    (computable_compact_size c hw)

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
