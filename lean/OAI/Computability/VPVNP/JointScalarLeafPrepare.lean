import OAI.Computability.VPVNP.JointScalarLeafPorts
import OAI.Computability.VPVNP.JointScalarRowPrefix

/-!
# Physical preparation and cleanup of a returning signed coefficient query

Copy the exponent payload and blank counters from immutable ports. Prepend
the low row-address bits and the polarity. Switching polarity consumes and
replaces only the first query bit. Cleanup returns the count registers and
the query workspace to empty stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open RAMTape UniversalCountStack SliceArithmetic

/-- Four source–destination pairs that initialize the checker query, witness word and two count
operands. -/
def copies : List (Port × Port) :=
  [(.packed,queryPort),(.blankChoice,choicePort),(.blankTotal,totalPort false),(.blankTotal,totalPort true)]

/-- Copy the packed exponents into the query and the zero templates into the three counter
registers, using the saved-bits stack as scratch. -/
def load : FiniteRoutine Port := CallCopies.copyPlan .saved copies

private theorem copy_ok : CallCopies.Valid Port.saved copies := by decide

private theorem copied (L : Layout) (row packed result : List Bool) :
    CallCopies.copied copies (clean L row packed result) =
      bank L row packed packed (digits L.witnessBits 0) (digits (L.witnessBits+1) 0)
        (digits (L.witnessBits+1) 0) result := by
  funext p
  cases p with
  | count i => cases i with
    | aux j => cases j <;> rfl
    | _ => rfl
  | arithmetic i =>
    rcases i with i|i
    · cases i with
      | divide j => cases j <;> rfl
      | _ => rfl
    · cases i <;> rfl
  | _ => rfl

theorem load_runs (L : Layout) (row packed result : List Bool) (b : ℕ)
    (hpacked : packed.length ≤ b) (hk : L.witnessBits+1 ≤ b) :
    ∃ steps ≤ 4*(5*b+2)+1, load.Runs steps (clean L row packed result)
      (bank L row packed packed (digits L.witnessBits 0) (digits (L.witnessBits+1) 0)
        (digits (L.witnessBits+1) 0) result) := by
  obtain ⟨steps,h,run⟩ := CallCopies.copyPlan_runs Port.saved copies (clean L row packed result) b
    copy_ok rfl (by intro p hp; simp [copies] at hp; rcases hp with rfl|rfl|rfl|rfl <;> rfl)
    (by intro p hp; simp [copies] at hp; rcases hp with rfl|rfl|rfl|rfl
        · exact hpacked
        · change (digits L.witnessBits 0).length ≤ b; simp; omega
        · simpa only [clean,bank,length_digits] using hk
        · simpa only [clean,bank,length_digits] using hk)
  rw [copied] at run
  exact ⟨steps,h,run⟩

/-- Connect the row-prefix routine to the leaf’s row register, width template, query stack and
two scratch stacks. -/
def prefixPorts : RowPrefix.Port → Port
  | .source => .row | .width => .rowWidth | .dst => queryPort | .saved => .saved | .staged => .staged

private theorem prefix_injective : Function.Injective prefixPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [prefixPorts, queryPort]

/-- Prepend the prescribed number of low row-address bits to the query, padding missing high
bits with zero and restoring the row register. -/
def prependRow : FiniteRoutine Port := (RowPrefix.body false).onPorts prefixPorts

theorem prefix_runs (L : Layout) (wr j : ℕ) (hj : j < 2^wr) (packed q choices pos neg result : List Bool) :
    ∃ steps ≤ 9*L.rowBits+3, prependRow.Runs steps
      (bank L (digits wr j) packed q choices pos neg result)
      (bank L (digits wr j) packed (digits L.rowBits j ++ q) choices pos neg result) := by
  obtain ⟨steps,h,r⟩ := RowPrefix.runs false L.rowBits wr j hj q
  refine ⟨steps,h,?_⟩
  apply (RowPrefix.body false).runs_onPorts_framed prefix_injective r
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro i hi
    cases i with
    | count i => cases i with
      | aux j => cases j <;> first | rfl | exact (hi .dst rfl).elim
      | _ => rfl
    | _ => rfl

/-- Prepend the requested polarity bit to the checker query. -/
def pushSign (b : Bool) : FiniteRoutine Port := .ofRoutine (Routine.push queryPort b)

private def popSign : FiniteRoutine Port :=
  .ofRoutine (⟨(), fun _ => .pop queryPort (fun _ => none)⟩ : Routine Port Unit)

/-- Replace the positive query’s leading false bit with true to select the negative count on
the same row and exponents. -/
def switchSign : FiniteRoutine Port := popSign.followedBy (pushSign true)

private theorem update_query (L : Layout) (row packed q choices pos neg result q' : List Bool) :
    Function.update (bank L row packed q choices pos neg result) queryPort q' =
      bank L row packed q' choices pos neg result := by
  funext i
  cases i with
  | count i => cases i with
    | aux j => cases j <;> rfl
    | _ => rfl
  | _ => rfl

theorem pushSign_runs (L : Layout) (row packed q choices pos neg result : List Bool) (b : Bool) :
    (pushSign b).Runs 1 (bank L row packed q choices pos neg result)
      (bank L row packed (b::q) choices pos neg result) := by
  rw [← update_query L row packed q choices pos neg result (b::q)]
  exact Routine.runs_push _ _ _

theorem switchSign_runs (L : Layout) (row packed q choices pos neg result : List Bool) :
    switchSign.Runs 2 (bank L row packed (false::q) choices pos neg result)
      (bank L row packed (true::q) choices pos neg result) := by
  apply FiniteRoutine.Runs.followedBy (m := 1) (n := 1) _ (pushSign_runs ..)
  rw [← update_query L row packed (false::q) choices pos neg result q]
  exact .cons (.pop rfl) (.nil ..)

/-- The query, witness and two count-operand stacks cleared at return. -/
def cleanPorts : List Port := [queryPort,choicePort,totalPort false,totalPort true]
/-- Clear the query, witness and both count operands to return the leaf bank to its clean call
boundary. -/
def cleanup : FiniteRoutine Port := CallClear.cleanup cleanPorts

theorem cleanup_runs (L : Layout) (row packed q choices pos neg result : List Bool) (b : ℕ)
    (hq : q.length ≤ b) (hc : choices.length ≤ b) (hp : pos.length ≤ b) (hn : neg.length ≤ b) :
    ∃ steps ≤ 4*(b+1)+1, cleanup.Runs steps (bank L row packed q choices pos neg result)
      (clean L row packed result) := by
  let s := bank L row packed q choices pos neg result
  obtain ⟨steps,h,run⟩ := CallClear.cleanup_runs cleanPorts s b (by
    intro i hi; simp [cleanPorts] at hi; rcases hi with rfl|rfl|rfl|rfl
    · exact hq
    · exact hc
    · exact hp
    · exact hn)
  have hu : CallClear.erased cleanPorts s = clean L row packed result := by
    funext i
    cases i with
    | count i => cases i with
      | aux j => cases j <;> rfl
      | _ => rfl
    | arithmetic i =>
      rcases i with i|i
      · cases i with
        | divide j => cases j <;> rfl
        | _ => rfl
      · cases i <;> rfl
    | _ => rfl
  exact ⟨steps,h,hu ▸ run⟩

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
