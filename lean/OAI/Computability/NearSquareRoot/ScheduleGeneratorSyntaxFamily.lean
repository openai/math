import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxCompleteEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPaddingEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxRelease

/-! # Physical machines and transition tables of a register-bounded program family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet

variable {A : Type} [Fintype A] (a : Numbering A)

noncomputable def dataNum (p : Prog A) : Numbering (Data p) :=
  (symbols a (UnitSites p)).option

noncomputable def controlNum (p : Prog A) : Numbering (Control p) :=
  (Generator.StackRows.pc (symbols a (UnitSites p)) (pcs a (UnitSites p))
    (Pack.stacks (UnitSites p))).option

theorem entry_rank (p : Prog A) :
    ((controlNum a p).equiv (entry p)).val = ((pcs a (UnitSites p)).equiv (start p)).val + 1 := by
  exact Generator.StackRows.option_some _ _

@[simp] theorem blank_rank (p : Prog A) : ((dataNum a p).equiv none).val = 0 :=
  Generator.StackRows.option_none _

theorem symbol_rank (p : Prog A) (v : A) :
    ((dataNum a p).equiv (symbol p v)).val = (a.equiv v).val + 1 :=
  Generator.StackRows.option_some _ _

variable {R : ℕ} (hR : 0 < R)

noncomputable def paddedRule (p : Prog A) (hp : CommonRegisters.Within R p) :
    TM.Rule (Data p) (Control p) (Option (Option (Fin R))) :=
  CommonTapes.rule (CommonRegisters.indexEmbedding hR hp) (released p)

variable (p : ℕ → Prog A) (hp : Effective (letter a) p) (bound : ∀ j, CommonRegisters.Within R (p j))

include hp in
/-- From a single computable syntax emitter, compute all finite widths and one
row evaluator on the common tape bank, including the final output-copy states. -/
theorem paddedRows :
    Computable (fun j => (dataNum a (p j)).size) ∧
    Computable (fun j => (controlNum a (p j)).size) ∧
    Computable (fun j => ((controlNum a (p j)).equiv (entry (p j))).val) ∧
    ∃ rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ), Computable₂ rows ∧
      ∀ j s r, rows j (((controlNum a (p j)).equiv s).val,
          (((Padding.fixed R).arrow (dataNum a (p j))).equiv r).val) =
        (paddedRule hR (p j) (bound j) s r).map (fun z =>
          (((controlNum a (p j)).equiv z.1).val,
          (((Padding.fixed R).arrow ((dataNum a (p j)).prod Numbering.move)).equiv z.2).val)) := by
  obtain ⟨hs,hq,hi,ho,h⟩ := source_family a p hp
  obtain ⟨cs,ca,_,rows,correct⟩ := Generator.CompleteRows.compile_family _ _ _
    (fun j => zeroStack (UnitSites (p j))) _ _ hs hq hi (computable_zeroStack a hp) ho h
  obtain ⟨padded,ok⟩ := Padding.padded_family a hp hR bound (fun j => dataNum a (p j))
    (fun j => controlNum a (p j)) (fun j => released (p j)) _ ca rows correct
  refine ⟨ca,cs,?_,_,padded,ok⟩
  simp only [entry_rank]
  exact Computable.succ.comp (computable_start a hp)

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
