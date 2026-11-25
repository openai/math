import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingSerializeRowsStates

/-! # Fixed instruction cases and counter destinations of the staged serializer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.SerializeRows

open CommonAlphabet IntegerMultiplication TM Code StagingSerialize
open ChunkControl (Driver)
open StagingProtection (Cell)

def headerMode : Ltr → Fin 14
  | .node => 10
  | .bit false => 11
  | .bit true => 12
  | .sep => 13

def phaseMode {k : ℕ} : Phase k → Fin 14
  | .turn => 0
  | .back => 1
  | .scan => 2
  | .payload false => 3
  | .payload true => 4
  | .returnIn => 5
  | .returnOut => 6
  | .ready => 7
  | .rejected => 8
  | .check _ => 9
  | .header j => headerMode (header k)[j]

/-- The destination field either gives a fixed state or advances one of the
two counters. The header entry is used after the rewind on the input tape. -/
def destination (k q token : ℕ) : ℕ :=
  if token = 9 then
    let j := q-9+1
    if j < 2^k then 9+j else 0
  else if token = 10 then 9+2^k
  else if token = 11 then
    let j := q-(9+2^k)+1
    if j < 2*k+3 then 9+2^k+j else 2
  else token

/-- Enumerate the finitely many letter and head updates. The halt field is 12.
Only the destination field requires further interpretation depending on k. -/
def instruction (d : Driver) (a : CommonAlphabet.Numbering (Cell d)) (m : Fin 14)
    (h : Bool → Cell d) : ℕ × ℕ :=
  let moves := Numbering.bool.arrow (a.prod Numbering.move)
  let keep (t : ℕ) (s o : Move) := (t,(moves.equiv (Expand.pair (h false,s) (h true,o))).val)
  let emit (t : ℕ) (s o : Move) (v : Ltr) := (t,(moves.equiv (Expand.pair (h false,s) (put d v,o))).val)
  match m with
  | 0 => keep 1 .left .stay
  | 1 => if (read d (h false)).isSome then keep 1 .left .stay else keep 10 .right .stay
  | 2 => match read d (h false) with
    | some (.bit b) => emit (if b then 4 else 3) .right .right .node
    | some .sep => emit 2 .right .right (.bit false)
    | some .node => keep 8 .stay .stay
    | none => emit 5 .left .stay (.bit false)
  | 3 => emit 2 .stay .right (.bit false)
  | 4 => emit 2 .stay .right (.bit true)
  | 5 => if (read d (h false)).isSome then keep 5 .left .stay else keep 6 .right .stay
  | 6 => if (read d (h true)).isSome then keep 6 .stay .left else keep 7 .stay .right
  | 7 | 8 => (12,0)
  | 9 => match read d (h false) with
    | some (.bit _) => keep 9 .right .stay
    | _ => keep 8 .stay .stay
  | 10 => emit 11 .stay .right .node
  | 11 => emit 11 .stay .right (.bit false)
  | 12 => emit 11 .stay .right (.bit true)
  | 13 => emit 11 .stay .right .sep

def resolve (k q : ℕ) (ins : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if ins.1 = 12 then none else some (destination k q ins.1,ins.2)

theorem resolves (d : Driver) (a : CommonAlphabet.Numbering (Cell d)) (k : ℕ) (s : Phase k) (h : Bool → Cell d) :
    resolve k (rank s) (instruction d a (phaseMode s) h) =
      (StagingSerialize.rule d k s h).map fun z =>
        (rank z.1,((Numbering.bool.arrow (a.prod Numbering.move)).equiv z.2).val) := by
  cases s with
  | turn | ready | rejected => rfl
  | payload b => cases b <;> rfl
  | back =>
    cases hh : (read d (h false)).isSome <;>
      simp [phaseMode,instruction,StagingSerialize.rule,resolve,destination,hh]
  | returnIn =>
    cases hh : (read d (h false)).isSome <;>
      simp [phaseMode,instruction,StagingSerialize.rule,resolve,destination,hh]
  | returnOut =>
    cases hh : (read d (h true)).isSome <;>
      simp [phaseMode,instruction,StagingSerialize.rule,resolve,destination,hh]
  | scan =>
    rcases hh : read d (h false) with _ | ((_ | _) | _ | _) <;>
      simp [phaseMode,instruction,StagingSerialize.rule,resolve,destination,hh]
  | check j =>
    rcases hh : read d (h false) with _ | ((_ | _) | _ | _) <;>
      simp [phaseMode,instruction,StagingSerialize.rule,resolve,destination,hh]
  | header j =>
    rcases hh : (header k)[j] with (_ | _) | _ | _ <;>
      simp [phaseMode,headerMode,instruction,StagingSerialize.rule,resolve,destination,hh]

end Generator.SerializeRows

end NearSquareRoot
end Computability
end OAI
