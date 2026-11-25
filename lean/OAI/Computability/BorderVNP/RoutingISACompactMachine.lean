import OAI.Computability.BorderVNP.CellFragments
import OAI.Computability.BorderVNP.CellStackTape
import OAI.Computability.BorderVNP.TeamLink
import OAI.Computability.VPVNP.EvaluatorRadixDivision

/-!
# Executing the sparse cell generator and its emitted signed instructions

The compact input starts on one named stack. A finite deterministic preparation routine
decodes it and generates bytecode privately. The generated bits are reversed onto the
stream port before the fixed interpreter starts. No expanded bytecode is fetched in the
outer RAM burst.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellMacro.Generator VPVNP.RAMTape

/-- Move the generator's reverse-order output onto the emptied row stack. -/
def reverseStream : Fragment IO :=
  Fragment.plain (VPVNP.EvaluatorRadixDivision.reverseOnto IO.out IO.row)

/-- Reversing the completed private stream consumes two stack steps per bit and one exit. -/
theorem reverseStream_run (bits : List Bool) :
    reverseStream.Runs (2*bits.length + 1) (io [] [] bits.reverse) (io bits [] []) := by
  apply Fragment.runs_plain
  simpa [io] using VPVNP.EvaluatorRadixDivision.reverseOnto_runs (src := IO.out) (dst := IO.row)
    (by decide) (io [] [] bits.reverse) (io bits [] []) rfl (by simp [io]) (by
      intro k ho hr
      cases k <;> simp_all [io])

/-- All three deterministic stages share the same row, environment and output stacks. -/
def prepare (decode generate : Fragment IO) : Fragment IO := decode.seq (generate.seq reverseStream)

/-- The exact preparation cost adds decoder and generator steps to the private reverse sweep. -/
theorem prefix_run (decode generate : Fragment IO) {wire payload bits : List Bool} {a b : ℕ}
    (parse : decode.Runs a (io [] wire []) (io payload [] []))
    (expand : generate.Runs b (io payload [] []) (io [] [] bits.reverse)) :
    (prepare decode generate).Runs (a + (b + (2*bits.length+1))) (io [] wire []) (io bits [] []) :=
  Fragment.runs_seq _ _ parse (Fragment.runs_seq _ _ expand (reverseStream_run bits))

/-- Ports of the evaluator after the private generator has returned. -/
def bytePort (prep : Fragment IO) : CellMacro.Port → IO ⊕ prep.Scratch
  | .stream => .inl .row
  | .values => .inl .env
  | .scratch => .inl .out

private theorem bytePort_injective (prep : Fragment IO) : Function.Injective (bytePort prep) := by
  intro x y h; cases x <;> cases y <;> simp_all [bytePort]

/-- Finite controls of the deterministic preparation and the signed evaluator. -/
abbrev Label (prep : Fragment IO) := prep.body.State ⊕ CellMacro.State

/-- Initial Boolean flags and fetch instruction of the signed cell interpreter. -/
def byteStart : CellMacro.State := (⟨true,false⟩,.fetch)

/-- Returning from preparation enters bytecode fetch in the same instruction step. -/
def program (prep : Fragment IO) : StackCode (IO ⊕ prep.Scratch) (Label prep)
  | .inl q => (prep.body.body.code q).rename id (fun r => r.elim (.inr byteStart) Sum.inl)
  | .inr q => (CellMacro.code q).rename (bytePort prep) Sum.inr

/-- Sign at terminal instructions of the actual combined finite table. -/
def negative (prep : Fragment IO) : Label prep → Bool :=
  Sum.elim (fun _ => false) CellMacro.negative

private theorem installed (prep : Fragment IO) (bits : List Bool) :
    installStacks (bytePort prep) (prep.bank (io bits [] [])) (CellMacro.bank bits [] []) =
      prep.bank (io bits [] []) := by
  apply installStacks_eq (bytePort_injective prep)
  intro k; cases k <;> rfl

/-- One complete finite signed table, with a deterministic front end and genuine fresh
choices in its bytecode. Its signed sum on a compact description is the cell value. -/
theorem stack_value (prep : Fragment IO) (wire : List Bool) (ops : List CellMacro.Op)
    {cost clock : ℕ} (compiled : prep.Runs cost (io [] wire []) (io (CellMacro.stream ops) [] []))
    (time : cost + CellMacro.budget ops ≤ clock) :
    StopsWithin (program prep) clock (.inl prep.body.body.entry) (prep.bank (io [] wire [])) ∧
      TeamStack.paths (program prep) (negative prep) clock (.inl prep.body.body.entry)
        (prep.bank (io [] wire [])) = CellMacro.value ops ⟨true,false⟩ [] := by
  let available := clock-cost
  have clockEq : clock = available + cost := by dsimp [available]; omega
  have room : CellMacro.budget ops ≤ available := by dsimp [available]; omega
  have prepRun := TeamLink.routine_id compiled (program prep) Sum.inl (.inr byteStart) (fun _ => rfl)
  have vm := CellMacro.execute ops ⟨true,false⟩ [] available room
  have stop := (stopsWithin_lift (target := program prep) (bytePort prep) (bytePort_injective prep)
    Sum.inr (prep.bank (io (CellMacro.stream ops) [] [])) (fun _ => rfl)
    available byteStart (CellMacro.bank (CellMacro.stream ops) [] [])).2 vm.1
  have count := TeamGuard.paths_lift (target := program prep) (neg := CellMacro.negative)
    (neg' := negative prep) (bytePort prep) (bytePort_injective prep) Sum.inr
    (prep.bank (io (CellMacro.stream ops) [] [])) (fun _ => rfl) (fun _ => rfl) available
    byteStart (CellMacro.bank (CellMacro.stream ops) [] [])
  rw [installed] at stop count
  rw [clockEq, prepRun.stopsWithin_iff, TeamGuard.runs_paths prepRun]
  exact ⟨stop, count.trans vm.2⟩

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
