import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.NearSquareRoot.InterchangeROMRoute
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax

/-! # Computable source-row selection and compilation of a literal movement bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM
open IntegerMultiplication IntegerMultiplication.Code LoomRegisters GeneratorSyntax

variable {X M K : Type} [Primcodable X] [Primcodable M] [Primcodable K]

/-- Quoting the branch of a tree parser requires only the file for its node case. -/
noncomputable def nodeFile (c : File) : File :=
  lookFile 0 (Prog.options.map fun a : Option Ltr =>
    joinFile (file ltr (.pop 0)) (if a = some .node then c else file ltr .pass))

theorem nodeFile_file (c : Cmd) :
    nodeFile (file ltr c) = file ltr (splitRoot 0 (fun _ => .pass) c) := by
  rw [splitRoot,← lookFile_file]
  change lookFile 0 _ = lookFile 0 _
  congr 1
  apply List.map_congr_left
  rintro (_ | (b | _ | _)) _
  all_goals simp [joinFile_file]

theorem computable_nodeFile : Computable nodeFile := by
  apply primrec_lookFile.to_comp.comp (Computable.const 0)
  apply computable_options_map Prog.options
  intro a _
  by_cases h : a = some Ltr.node
  · simp only [ite_eq_left h]
    exact primrec_joinFile.to_comp.comp
      (Computable.const (file ltr (.pop 0))) (Computable.id (α:=File))
  · simp only [ite_eq_right h]
    exact Computable.const _

theorem effective_cell {n : X → ℕ} (hn : Computable n) :
    Effective ltr (fun x => cellCommand (n x)) := by
  let step (xs : ℕ × File) := nodeFile (joinFile (file ltr (discard 0)) xs.2)
  have hs : Computable step := computable_nodeFile.comp
    (primrec_joinFile.to_comp.comp (Computable.const _) Computable.snd)
  have run := Computable.nat_rec hn (Computable.const (file ltr (cellCommand 0)))
    (hs.comp (Computable.snd (α:=X))).to₂
  apply run.of_eq
  intro x
  change Nat.rec _ (fun j acc => step (j,acc)) (n x) = file ltr (cellCommand (n x))
  induction n x with
  | zero => rfl
  | succ i ih =>
    simp only [step,ih,joinFile_file,nodeFile_file]
    rfl

theorem effective_underHeader {c : X → Cmd} (hc : Effective ltr c) :
    Effective ltr (fun x => underHeader (c x)) :=
  (computable_nodeFile.comp ((effective_const ltr (move 0 1 2)).join
    (hc.join (effective_const ltr ((move 1 0 2).join (pack 0)))))).of_eq
      (fun _ => nodeFile_file _)

end InterchangeROM

end NearSquareRoot
end Computability
end OAI
