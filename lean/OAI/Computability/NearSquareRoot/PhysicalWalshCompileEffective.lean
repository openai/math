import OAI.Computability.NearSquareRoot.PhysicalWalshCompile
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFold
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.IntegerMultiplication.Interface

/-! # Total computability of the physical template's exact P192 program file

The numeric assembly carries every compiler site, including its enclosing
recursion scope. Its result is the file of the physical command itself.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code KernelPass.ComputableSyntax GeneratorSyntax

private noncomputable def leftFile (v : File) : File := lookFile 0
  (Prog.options.map fun a : Option Ltr => joinFile (file ltr (.pop 0))
    (match a with | some .node => joinFile v (file ltr (pack 0)) | _ => file ltr .pass))

private theorem leftFile_file (c : Cmd) : leftFile (file ltr c) = file ltr (left c) := by
  unfold leftFile left splitRoot
  rw [← lookFile_file]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a with
  | none => exact joinFile_file ..
  | some s => cases s <;> simp [joinFile_file]

private theorem computable_leftFile : Computable leftFile := by
  apply primrec_lookFile.to_comp.comp (Computable.const 0)
  apply computable_options_map
  intro a _
  apply primrec_joinFile.to_comp.comp (Computable.const _)
  cases a with
  | none => exact Computable.const _
  | some s => cases s <;> first | exact Computable.const _ | exact primrec_joinFile.to_comp.comp Computable.id (Computable.const _)

private noncomputable def parallelFile (b : BankCode) (i : ℕ) (p q : File) : File :=
  joinFile (joinFile (joinFile (file ltr (b.split i)) (leftFile p)) (file ltr b.swap))
    (joinFile (leftFile q) (file ltr b.finish))

private theorem parallelFile_file (b : BankCode) (i : ℕ) (p q : Cmd) :
    parallelFile b i (file ltr p) (file ltr q) = file ltr (b.parallel i p q) := by
  simp [parallelFile,leftFile_file,joinFile_file,BankCode.parallel]

set_option maxHeartbeats 1800000 in
/-- The complete file of a varying command is computable jointly in the arity
and raw opcode list. The only program-family hypotheses are the leaf emitter
and the cut after a varying bank width. -/
theorem effective_family {X : Type} [Primcodable X] (b : BankCode) (zero : Cmd)
    (leaf : X → Op → Cmd) (A : X → ℕ) (ops : X → List Op) (hA : Computable A) (ho : Computable ops)
    (hs : Effective ltr b.split) (hl : Effective ltr (Function.uncurry leaf)) :
    Effective ltr (fun v => command b zero (fun _ => leaf v) (A v) (ops v)) := by
  let build (v : X) := algebra (A v) (file ltr zero) (fun op => file ltr (leaf v op)) joinFile (parallelFile b)
  let S := Shape × File
  have num : Computable (fun v : X => (build v).parse (ops v)) := by
    apply computable_parse build (Shape.empty,file ltr zero) (fun _ => rfl) ?_ ?_ ?_ ops ho
    · exact ((Shape.primrec_leaf.to_comp.comp (hA.comp Computable.fst) Computable.snd).pair hl).to₂
    · let Y := X × S × S
      have p : Computable (fun v : Y => v.2.1) := Computable.fst.comp Computable.snd
      have q : Computable (fun v : Y => v.2.2) := Computable.snd.comp Computable.snd
      have sp := Computable.fst.comp p
      have sq := Computable.fst.comp q
      have test := Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.fst.comp sq))
        (Computable.fst.comp (Computable.fst.comp sp))
      have emit := primrec_joinFile.to_comp.comp (Computable.snd.comp q) (Computable.snd.comp p)
      apply (Computable.to₂ (f := fun v : Y => (build v.1).seq v.2.1 v.2.2))
      apply ((Shape.primrec_seq.to_comp.comp sp sq).pair (Computable.cond test emit (Computable.const (file ltr zero)))).of_eq
      intro v
      simp only [build,algebra,Bool.cond_decide]
    · let Y := X × S × S
      have p : Computable (fun v : Y => v.2.1) := Computable.fst.comp Computable.snd
      have q : Computable (fun v : Y => v.2.2) := Computable.snd.comp Computable.snd
      have sp := Computable.fst.comp p
      have sq := Computable.fst.comp q
      have cut := hs.comp (Computable.fst.comp (Computable.fst.comp sp))
      have first := primrec_joinFile.to_comp.comp cut (computable_leftFile.comp (Computable.snd.comp p))
      have swapped := primrec_joinFile.to_comp.comp first (Computable.const (file ltr b.swap))
      have second := primrec_joinFile.to_comp.comp (computable_leftFile.comp (Computable.snd.comp q)) (Computable.const (file ltr b.finish))
      exact ((Shape.primrec_parallel.to_comp.comp sp sq).pair (primrec_joinFile.to_comp.comp swapped second)).to₂
  apply (Computable.snd.comp num).of_eq
  intro v
  let cv (p : Shape × Cmd) := (p.1,file ltr p.2)
  have same := parse_map (a := algebra (A v) zero (leaf v) Prog.join b.parallel) (b := build v) cv
    rfl (fun _ => rfl) (fun p q => by dsimp [cv,build,algebra]; split <;> simp [joinFile_file])
    (fun p q => by dsimp [cv,build,algebra]; rw [parallelFile_file]) (ops v)
  exact congrArg Prod.snd same.symm

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
