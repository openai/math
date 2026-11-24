import OAI.Computability.VPVNP.MacaulayReadArms
import OAI.Computability.VPVNP.MacaulayPairEntries

/-! # Selecting a matrix entry and reclaiming its temporary buffers

Divisibility selects either the coefficient routine or the zero scalar. On a
powered row, equality selects an advised encoding of zero or one. The bit
selection preserves its full flag word. Both the exponent buffer and flag
are cleared before the next matrix read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open BurstRAM RAMTape UniversalCountStack MacaulayRowDispatch RadicalCertificate.MonomialIndex

variable {K : Type} [DecidableEq K]

private def scalarPort (b : Bool) : Ports K := extra (if b then .oneScalar else .zeroScalar)

/-- Prepend the stored field encoding of zero or one to the reader's result stack according to
the given bit. -/
def emit (bit : Bool) : FiniteRoutine (Ports K) :=
  SuccessorFields.prependCopy (scalarPort bit) .result (extra .temp)

/-- Clear the packed exponents and flag left by the selected monomial scan. -/
def erase (power : Bool) : FiniteRoutine (Ports K) :=
  (SliceArithmetic.CallClear.clear (slot power (.external .packed))).followedBy
    (SliceArithmetic.CallClear.clear (slot power (.external .flag)))

/-- Read the scan flag, emit zero on a failed match or run the supplied coefficient routine on
a match, then clear the scan buffers. -/
def finish (power : Bool) (leaf : FiniteRoutine (Ports K)) : FiniteRoutine (Ports K) :=
  (TagRouter.select (slot power (.external .flag)) 1 (fun bit => if bit = 0 then emit false else leaf)).followedBy
    (erase power)

private theorem putResult {w : ℕ} (rs : Reg → Word w) (s : Stacks (Leaf K)) (old new : List Bool) :
    Function.update (frame rs old s) .result new = frame rs new s := by
  funext z; cases z <;> rfl

private theorem putPacked {w : ℕ} (rs : Reg → Word w) (res : List Bool) (b : Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K) (new : List Bool) :
    Function.update (frame rs res (storage w data pack flag constants aux)) (slot b (.external .packed)) new =
      frame rs res (storage w data (Function.update pack b new) flag constants aux) := by
  funext z
  cases z with
  | row | col | result => rfl
  | aux x =>
    rcases x with q | x
    · cases q <;> rfl
    rcases x with ⟨a,q⟩ | x
    · cases b <;> cases a <;> cases q with
      | external f => cases f <;> rfl
      | internal | scratch => rfl
    · cases x <;> rfl

private theorem putFlag {w : ℕ} (rs : Reg → Word w) (res : List Bool) (b : Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K) (new : List Bool) :
    Function.update (frame rs res (storage w data pack flag constants aux)) (slot b (.external .flag)) new =
      frame rs res (storage w data pack (Function.update flag b new) constants aux) := by
  funext z
  cases z with
  | row | col | result => rfl
  | aux x =>
    rcases x with q | x
    · cases q <;> rfl
    rcases x with ⟨a,q⟩ | x
    · cases b <;> cases a <;> cases q with
      | external f => cases f <;> rfl
      | internal | scratch => rfl
    · cases x <;> rfl

omit [DecidableEq K] in
/-- Bound every physical stack, including registers and the scalar result.
The supplied word bound also covers the immutable degree/ordinal descriptors. -/
theorem frame_bound {w A : ℕ} (rs : Reg → Word w) (res : List Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K)
    (hw : w ≤ A) (hres : res.length ≤ A) (ht : ∀ b, (data b).arity ≤ A)
    (hp : ∀ b, (pack b).length ≤ A) (hf : ∀ b, (flag b).length ≤ A)
    (hc : ∀ b, (constants b).length ≤ A) (haux : ∀ k, (aux k).length ≤ A) :
    ∀ z, (frame rs res (storage w data pack flag constants aux) z).length ≤ A := by
  intro z
  cases z with
  | row | col => simpa [frame, bank] using hw
  | result => exact hres
  | aux z =>
    rcases z with q | z
    · have hl := (RegisterTable.bank_length_le Fin.elim0 (0 : Word w) rs q).trans hw
      cases q with
      | reg i => simp [frame,bank,auxBank]; split_ifs <;> simp [hw]
      | pub | persistent | work | logPort => exact hl
    rcases z with ⟨b,q⟩ | x
    · cases q with
      | external f =>
        have h := PairCall.values_le (data b) (fun _ => []) (pack b) (flag b) hw (ht b) (by simp) (hp b) (hf b) f
        cases f <;> first | exact h | exact Nat.zero_le _
      | internal | scratch => exact Nat.zero_le _
    · cases x with
      | zeroScalar => exact hc false
      | oneScalar => exact hc true
      | temp => exact Nat.zero_le _
      | payload k => exact haux k

theorem emit_runs {w : ℕ} (rs : Reg → Word w) (b : Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K) :
    (emit b).Runs (5*(constants b).length+2) (frame rs [] (storage w data pack flag constants aux))
      (frame rs (constants b) (storage w data pack flag constants aux)) := by
  let st := frame rs [] (storage w data pack flag constants aux)
  have src : st (scalarPort b) = constants b := by cases b <;> rfl
  have read := SuccessorFields.prependCopy_runs (scalarPort b) (.result : Ports K) (extra .temp)
    (by cases b <;> simp [scalarPort, extra]) (by cases b <;> simp [scalarPort, extra]) (by simp [extra]) st rfl
  rw [src, show st .result = [] from rfl, List.append_nil, putResult] at read
  exact read

theorem erase_runs {w : ℕ} (rs : Reg → Word w) (res : List Bool) (b : Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K) :
    (erase b).Runs ((pack b).length+1+((flag b).length+1)) (frame rs res (storage w data pack flag constants aux))
      (frame rs res (storage w data (Function.update pack b []) (Function.update flag b []) constants aux)) := by
  let st := frame rs res (storage w data pack flag constants aux)
  have p := SliceArithmetic.CallClear.clear_runs (slot b (.external .packed)) st
  have f := SliceArithmetic.CallClear.clear_runs (slot b (.external .flag))
    (frame rs res (storage w data (Function.update pack b []) flag constants aux))
  rw [putPacked] at p
  rw [putFlag] at f
  exact p.followedBy f

/-- Run the flag router and reclaim the two buffers. The clock of the long
scalar call is charged once, with its peak cap retained through the tag test. -/
theorem finish_bounded {w S n : ℕ} (rs : Reg → Word w) (b matched : Bool) (data : Bool → PairCall.Inputs)
    (pack flag constants : Bool → List Bool) (aux : Stacks K) (leaf : FiniteRoutine (Ports K))
    (out : List Bool) (rem : Bool → List Bool)
    (hw : 1 ≤ w) (hf : flag b = digits w matched.toNat)
    (call : (if matched then leaf else emit false).BoundedRun S n
      (frame rs [] (storage w data pack flag constants aux)) (frame rs out (storage w data rem flag constants aux)))
    (room : ∀ z, (frame rs out (storage w data rem flag constants aux) z).length +
      ((rem b).length+1+((flag b).length+1)) ≤ S) :
    (finish b leaf).BoundedRun S (2+n+((rem b).length+1+((flag b).length+1)))
      (frame rs [] (storage w data pack flag constants aux))
      (frame rs out (storage w data (Function.update rem b []) (Function.update flag b []) constants aux)) := by
  let start := frame rs [] (storage w data pack flag constants aux)
  let next (i : ℕ) := if i = 0 then emit false else leaf
  have hcall : (next matched.toNat).BoundedRun S n start (frame rs out (storage w data rem flag constants aux)) := by
    cases matched <;> exact call
  have hc := TagRouter.digits_bounded (slot b (.external .flag)) next hw (by cases matched <;> decide : matched.toNat < 2^1)
    start _ hf hcall
  have he := spaceRun_of_steps (erase_runs rs out b data rem flag constants aux) room
  exact hc.followedBy he

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
