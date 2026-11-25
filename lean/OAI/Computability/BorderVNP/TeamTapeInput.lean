import OAI.Computability.BorderVNP.TeamTapeInputHeader
import OAI.Computability.VPVNP.RAMTapeInputFields

/-! # Extracting all input-memory bits from a team processor tape

The literal (including the processor's own machine prefix), exterior inputs and any extra
pins initialize successive RAM addresses. Interior routing bits follow them and go to
a separate stack. The final physical padding must be zero. The cut lengths are decoded
from pinned binary public parameters in the literal and the cutter operates on the
original complete tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInput

open VPVNP RAMTape InputReader

/-- After the two public counters have been decoded, separate the whole RAM initialization
stream and the interior routing bits. Finally scan the remaining input as zero padding. -/
def cutData : FiniteRoutine Port :=
  (((FiniteRoutine.ofRoutine (InputReader.readField .header)).followedBy
    (FiniteRoutine.ofRoutine (InputReader.readField .incident))).followedBy
    (FiniteRoutine.ofRoutine InputReader.padding)).onPorts Port.cut

/-- Complete tape splitter, including the physical copy and public parameter reads. -/
def program : FiniteRoutine Port := header.followedBy cutData

/-- Final stacks keep the complete initialized data and the separate routing input, in their
original orders, as well as the peek parser's saved machine prefix and suffix. -/
def loaded (savedPrefix suffix data routing : List Bool) : Stacks Port
  | .peek .prefix => savedPrefix
  | .peek .input => suffix
  | .cut .header => data
  | .cut .incident => routing
  | _ => []

private theorem cut_runs (pref rest data routing : List Bool) (z : ℕ) :
    let raw := data ++ routing ++ List.replicate z false
    cutData.Runs (5*data.length+5*routing.length+2*z+5)
      (prepared raw pref rest data.length routing.length) (loaded pref rest data routing) := by
  intro raw
  let s := prepared raw pref rest data.length routing.length
  let a := fieldResult (s ∘ Port.cut) .header data (routing ++ List.replicate z false)
  let b := fieldResult a .incident routing (List.replicate z false)
  have first := readField_runs (s ∘ Port.cut) .header data (routing ++ List.replicate z false)
    (by simp [s, prepared, raw, List.append_assoc]) rfl rfl
  have second := readField_runs a .incident routing (List.replicate z false) rfl rfl rfl
  have last := padding_runs b z rfl
  let src := ((FiniteRoutine.ofRoutine (InputReader.readField .header)).followedBy
    (FiniteRoutine.ofRoutine (InputReader.readField .incident))).followedBy (FiniteRoutine.ofRoutine InputReader.padding)
  have run : src.Runs ((5*data.length+2)+(5*routing.length+2)+(2*z+1))
      (s ∘ Port.cut) (Function.update b .input []) :=
    (FiniteRoutine.Runs.followedBy (a := FiniteRoutine.ofRoutine (InputReader.readField .header))
      (b := FiniteRoutine.ofRoutine (InputReader.readField .incident)) first second).followedBy last
  change (src.onPorts Port.cut).Runs _ _ _
  rw [show 5*data.length+5*routing.length+2*z+5 = (5*data.length+2)+(5*routing.length+2)+(2*z+1) by omega]
  apply src.runs_onPorts_framed (by decide : Function.Injective Port.cut) run
  · exact fun _ => rfl
  · intro k
    cases k <;> simp [b, a, s, fieldResult, Field.output, Field.counter, prepared, loaded]
  · intro k hk
    rcases k with p | p | _ | _ | _
    · exact (hk p rfl).elim
    · cases p <;> rfl
    all_goals rfl

/-- Physical field order inside a processor's initialized RAM segment. Each exterior
field retains its own bit order; the last list gives the optional extra pins. -/
def inputData (literal : List Bool) (exterior : List (List Bool)) (pins : List Bool) : List Bool :=
  literal ++ exterior.flatten ++ pins

/-- On every data and routing assignment with pinned field lengths, the fixed machine
extracts exactly the four-field layout, checks the canonical trailing zeros, and returns
in time linear in the whole input and in the public width parameters. -/
theorem runs (table mem inc literalRest pins routing : List Bool)
    (exterior : List (List Bool)) (z : ℕ) :
    let pref := UniversalMachine.unary table.length ++ table
    let literal := pref ++ parameters mem inc ++ literalRest
    let data := inputData literal exterior pins
    let raw := data ++ routing ++ List.replicate z false
    let rest := literalRest ++ exterior.flatten ++ pins ++ routing ++ List.replicate z false
    TapeWord.value mem = data.length → TapeWord.value inc = routing.length →
      ∃ t ≤ 5*raw.length + 10*table.length + 12*(data.length+routing.length) +
        9*(mem.length+inc.length) + 2*z + 19,
      program.Runs t (initial raw) (loaded pref rest data routing) := by
  intro pref literal data raw rest hm hi
  obtain ⟨t, ht, run⟩ := header_runs table mem inc rest
  change t ≤ 5*(pref ++ parameters mem inc ++ rest).length + 10*table.length +
    7*(TapeWord.value mem + TapeWord.value inc) + 9*(mem.length+inc.length) + 14 at ht
  have hr : pref ++ parameters mem inc ++ rest = raw := by
    simp [raw, data, inputData, literal, rest, List.append_assoc]
  rw [hr, hm, hi] at ht run
  have cut := cut_runs pref rest data routing z
  exact ⟨_, by omega, run.followedBy cut⟩

end TeamTapeInput

end BorderVNP
end Computability
end OAI
