import OAI.Computability.VPVNP.AdviceInterpreter
import OAI.Computability.VPVNP.AdviceCircuitCompiler
import OAI.Computability.VPVNP.AdviceReturnBit
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.UniversalCountStack

/-! # Using the circuit-advice interpreter as a counting verifier

Each invocation copies the persistent advice, query, and current witness into
the interpreter's work stacks. After evaluation it transfers just the designated
output to the enumeration flag and empties the valuation stack. This restores
the state required for the next witness without copying the count itself.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AdviceCountAdapter

open UniversalCountStack AdviceCircuit

/-- Ports for the persistent query and advice, the circuit interpreter’s work stacks, and the
scratch stack used to copy its inputs. -/
inductive AuxPort where
  | query | advice | vmStream | vmValues | vmScratch | vmResult | copyTmp
  deriving DecidableEq

instance : Fintype AuxPort := derive_fintype% _

/-- The witness counter’s ports extended by the query, advice, and working stacks for the
Boolean circuit verifier. -/
abbrev Port := UniversalCountStack.Port AuxPort

private def workspace (query advice stream values : List Bool) : Stacks AuxPort
  | .query => query
  | .advice => advice
  | .vmStream => stream
  | .vmValues => values
  | _ => []

/-- Persistent strings with every private work stack empty. -/
def inputs (query advice : List Bool) : Stacks AuxPort := workspace query advice [] []

private def vmPort : AdviceBitLookup.Port → Port
  | .stream => .aux .vmStream
  | .values => .aux .vmValues
  | .scratch => .aux .vmScratch
  | .result => .aux .vmResult

private theorem vmPort_injective : Function.Injective vmPort := by
  intro x y h
  cases x <;> cases y <;> simp_all [vmPort]

private def copy (src dst : Port) : FiniteRoutine Port :=
  SuccessorFields.prependCopy src dst (.aux .copyTmp)

private def pushValue (bit : Bool) : FiniteRoutine Port :=
  FiniteRoutine.ofRoutine (Routine.push (.aux .vmValues) bit)

private def prepare : FiniteRoutine Port :=
  ((((copy (.aux .advice) (.aux .vmStream)).followedBy (copy .choice (.aux .vmValues))).followedBy
    (copy (.aux .query) (.aux .vmValues))).followedBy (pushValue true)).followedBy (pushValue false)

/-- The verifier called by `UniversalCountStack.enumerate`. -/
def verify : FiniteRoutine Port :=
  (prepare.followedBy (AdviceInterpreter.routine.onPorts vmPort)).followedBy
    (AdviceReturnBit.takeTopAndClear (.aux .vmValues) .flag)

private abbrev bankState (q a c t x v flag : List Bool) : Stacks Port :=
  bank (workspace q a x v) c t [] flag

private theorem update_stream (q a c t x v f xs : List Bool) :
    Function.update (bankState q a c t x v f) (.aux .vmStream) xs = bankState q a c t xs v f := by
  funext p
  cases p with
  | aux j => cases j <;> simp [bankState, bank, workspace, Function.update]
  | _ => simp [bankState, bank, Function.update]

private theorem update_values (q a c t x v f xs : List Bool) :
    Function.update (bankState q a c t x v f) (.aux .vmValues) xs = bankState q a c t x xs f := by
  funext p
  cases p with
  | aux j => cases j <;> simp [bankState, bank, workspace, Function.update]
  | _ => simp [bankState, bank, Function.update]

private theorem update_flag (q a c t x v f xs : List Bool) :
    Function.update (bankState q a c t x v f) .flag xs = bankState q a c t x v xs := by
  funext p
  cases p <;> simp [bankState, bank, Function.update]

private theorem prepare_runs (q a c t : List Bool) :
    prepare.Runs (5 * (a.length + c.length + q.length) + 8) (bankState q a c t [] [] [])
      (bankState q a c t a (false :: true :: (q ++ c)) []) := by
  have ha := SuccessorFields.prependCopy_runs (K := Port) (.aux .advice) (.aux .vmStream)
    (.aux .copyTmp) (by decide) (by decide) (by decide) (bankState q a c t [] [] []) rfl
  have hc := SuccessorFields.prependCopy_runs (K := Port) .choice (.aux .vmValues)
    (.aux .copyTmp) (by decide) (by decide) (by decide) (bankState q a c t a [] []) rfl
  have hq := SuccessorFields.prependCopy_runs (K := Port) (.aux .query) (.aux .vmValues)
    (.aux .copyTmp) (by decide) (by decide) (by decide) (bankState q a c t a c []) rfl
  have push (v : List Bool) (b : Bool) : (pushValue b).Runs 1 (bankState q a c t a v [])
      (bankState q a c t a (b :: v) []) := by
    have step := Routine.runs_push (.aux .vmValues : Port) b (bankState q a c t a v [])
    rw [update_values] at step
    exact step
  rw [update_stream] at ha
  rw [update_values] at hc hq
  change (copy (.aux .advice) (.aux .vmStream)).Runs (5 * a.length + 2) _
    (bankState q a c t (a ++ []) [] []) at ha
  change (copy .choice (.aux .vmValues)).Runs (5 * c.length + 2) _
    (bankState q a c t a (c ++ []) []) at hc
  change (copy (.aux .query) (.aux .vmValues)).Runs (5 * q.length + 2) _
    (bankState q a c t a (q ++ c) []) at hq
  rw [List.append_nil] at ha hc
  have result := (((ha.followedBy hc).followedBy hq).followedBy (push _ true)).followedBy (push _ false)
  rw [show 5 * (a.length + c.length + q.length) + 8 =
    (5*a.length + 2) + (5*c.length + 2) + (5*q.length + 2) + 1 + 1 by omega]
  exact result

/-- A successful advice program returns its first valuation bit to the flag,
restoring the complete persistent input and both counter registers. -/
theorem verify_runs (p : List Instruction) (query choice total : List Bool)
    {ok : Bool} {tail : List Bool}
    (hu : run p (false :: true :: (query ++ choice)) = some (ok :: tail)) :
    ∃ ticks ≤ 32 * ((encode p).length + p.length + query.length + choice.length + 1),
      verify.Runs ticks (bank (inputs query (encode p)) choice total [] [])
        (bank (inputs query (encode p)) choice total [] [ok]) := by
  let a := encode p
  let v := false :: true :: (query ++ choice)
  obtain ⟨u, htime, hv⟩ := AdviceInterpreter.routine_runs p v (ok :: tail) hu
  have hvm : (AdviceInterpreter.routine.onPorts vmPort).Runs u
      (bankState query a choice total a v []) (bankState query a choice total [] (ok :: tail) []) := by
    apply FiniteRoutine.runs_onPorts_framed _ vmPort_injective hv
    · intro j; cases j <;> rfl
    · intro j; cases j <;> rfl
    · intro j hj
      cases j with
      | aux i => cases i <;> first | rfl | exact (hj .stream rfl).elim | exact (hj .values rfl).elim
      | _ => rfl
  have hout := AdviceReturnBit.takeTopAndClear_runs (K := Port) (src := .aux .vmValues)
    (dst := .flag) (by decide) (bankState query a choice total [] (ok :: tail) []) ok tail rfl
  rw [update_values, update_flag] at hout
  have hh := ((prepare_runs query a choice total).followedBy hvm).followedBy hout
  refine ⟨_, ?_, hh⟩
  have hlen := AdviceCircuit.length_run hu
  simp only [List.length_cons, List.length_append] at hlen
  dsimp only [a]
  omega

end RAMTape.AdviceCountAdapter

end VPVNP
end Computability
end OAI
