import OAI.Computability.VPVNP.MacaulayReadRouter
import OAI.Computability.VPVNP.MacaulayPairCall

/-! # Native exponent scans in the matrix reader

The source and column ordinals are the third and fourth words returned by the
row decoder. The equation and powered-row scans use separate advised radix
bounds. Each scan preserves the decoded words, returning its flag and exponent
buffer to the selected coefficient routine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open BurstRAM RAMTape UniversalCountStack MacaulayRowDispatch
open RadicalCertificate.MonomialIndex

/-- Auxiliary ports for the encodings of zero and one, a temporary copy stack and the
coefficient routine's payload. -/
inductive Extra (K : Type) where
  | zeroScalar | oneScalar | temp | payload (k : K)
  deriving DecidableEq, Fintype

/-- Private ports of the matrix reader. Each of its two monomial scans has a pair-call bank
alongside the shared auxiliary ports. -/
abbrev Leaf (K : Type) := (Bool × PairCall.Port) ⊕ Extra K
set_option synthInstance.maxSize 2500 in
instance {K : Type} [DecidableEq K] : DecidableEq (Leaf K) :=
  inferInstanceAs (DecidableEq ((Bool × PairCall.Port) ⊕ Extra K))

/-- The matrix reader's row, column and result ports together with its decoder, monomial scans
and coefficient payload. -/
abbrev Ports (K : Type) := Bus (Leaf K)

variable {K : Type}

/-- Locate a pair-call stack in the private bank for the ordinary scan or the powered-row scan. -/
def slot (power : Bool) (q : PairCall.Port) : Ports K := .aux (.inr (.inl (power,q)))
/-- Locate a shared auxiliary stack of the coefficient routines on the matrix reader's bus. -/
def extra (x : Extra K) : Ports K := .aux (.inr (.inr x))

/-- Output-field index for a decoded monomial ordinal. The source uses field 2 and the column
uses field 3. -/
def ordinalField (b : Bool) : Fin 6 := if b then 3 else 2

/-- Alias the two ordinal inputs to the decoded words on the physical bus. -/
def pairPorts (power : Bool) : PairCall.Port → Ports K
  | .external (.ordinal b) => route (.reg (outReg (ordinalField b)))
  | q => slot power q

theorem pairPorts_injective (power : Bool) : Function.Injective (pairPorts (K := K) power) := by
  intro a b h
  have left (b : Bool) : route (.reg (outReg (ordinalField b))) = (.aux (.inl (.reg (outReg (ordinalField b)))) : Ports K) := by
    cases b <;> simp [route, ordinalField, inReg, outReg, Dispatch.Code.inReg, Dispatch.Code.outReg]
  let ord (b : Bool) : PairCall.Port := .external (.ordinal b)
  have other (q : PairCall.Port) (h₀ : q ≠ ord false) (h₁ : q ≠ ord true) :
      pairPorts (K := K) power q = slot power q := by
    cases q with
    | external f => cases f with
      | ordinal x => cases x <;> contradiction
      | _ => rfl
    | internal | scratch => rfl
  have h₀ : pairPorts (K := K) power (ord false) = .aux (.inl (.reg (outReg 2))) := left false
  have h₁ : pairPorts (K := K) power (ord true) = .aux (.inl (.reg (outReg 3))) := left true
  have distinct : outReg 2 ≠ outReg 3 := by intro he; have := congrArg Fin.val he; contradiction
  by_cases ha : a = ord false <;> by_cases ha' : a = ord true <;>
    by_cases hb : b = ord false <;> by_cases hb' : b = ord true <;>
    simp_all [slot, Ne.symm distinct]

/-- Storage owned by the matrix reader. Aliased ordinal stacks have no
private copy. The other bank remains intact when a scan updates its buffer. -/
def storage (w : ℕ) (data : Bool → PairCall.Inputs) (packed flag : Bool → List Bool)
    (constants : Bool → List Bool) (payload : Stacks K) : Stacks (Leaf K)
  | .inl (_, .external (.ordinal _)) => []
  | .inl (b,q) => PairCall.publicBank w (data b) (fun _ => []) (packed b) (flag b) q
  | .inr .zeroScalar => constants false
  | .inr .oneScalar => constants true
  | .inr .temp => []
  | .inr (.payload k) => payload k

/-- Fill the pair scan's source and column ordinals from the row decoder's output registers. -/
def addressed {w : ℕ} (rs : Reg → Word w) (d : PairCall.Inputs) : PairCall.Inputs :=
  {d with ordinal := fun b => (rs (outReg (ordinalField b))).val}

theorem pairFrame {w : ℕ} (rs : Reg → Word w) (res : List Bool) (d : Bool → PairCall.Inputs)
    (pack flag : Bool → List Bool) (v : Bool → List Bool) (aux : Stacks K) (b : Bool) (q : PairCall.Port) :
    frame rs res (storage w d pack flag v aux) (pairPorts b q) =
      PairCall.publicBank w (addressed rs (d b)) (fun _ => []) (pack b) (flag b) q := by
  cases q with
  | external x =>
    cases x <;> first | rfl | (rw [pairPorts, frame_route]; simp [addressed, PairCall.publicBank,
      RadicalCertificate.MonomialIndex.CallBank.clean, RadicalCertificate.MonomialIndex.CallBank.frame,
      PairCall.values, digits, ISA.bank])
  | internal | scratch => rfl

private theorem private_preserved {w : ℕ} (rs : Reg → Word w) (res : List Bool) (d : Bool → PairCall.Inputs)
    (pack flag : Bool → List Bool) (v : Bool → List Bool) (aux : Stacks K) (b : Bool) (p' f' : List Bool)
    (z : Ports K) (outside : ∀ q, pairPorts b q ≠ z) :
    frame rs res (storage w d (Function.update pack b p') (Function.update flag b f') v aux) z =
      frame rs res (storage w d pack flag v aux) z := by
  cases z with
  | row | col | result => rfl
  | aux z =>
    rcases z with q | x
    · cases q <;> rfl
    rcases x with ⟨a,q⟩ | y
    · by_cases he : a = b
      · subst a
        cases q with
        | external f => cases f with
          | packed => exact (outside (.external .packed) rfl).elim
          | flag => exact (outside (.external .flag) rfl).elim
          | _ => rfl
        | internal | scratch => rfl
      · cases q with
        | external f => cases f <;> first | rfl | simp [frame, bank, auxBank, storage, he,
            PairCall.publicBank, RadicalCertificate.MonomialIndex.CallBank.clean, RadicalCertificate.MonomialIndex.CallBank.frame, PairCall.values]
        | internal | scratch => rfl
    · cases y <;> rfl

/-- Run either physical pair scan in the full reader. Only its own output
buffer and flag change. All other scratch is restored at the call boundary. -/
theorem scan_bounded [DecidableEq K] {w S n : ℕ} (r : FiniteRoutine PairCall.Port) (b : Bool) (rs : Reg → Word w)
    (res : List Bool) (d : Bool → PairCall.Inputs) (pack flag : Bool → List Bool) (v : Bool → List Bool)
    (aux : Stacks K) (p' f' : List Bool)
    (run : r.BoundedRun S n (PairCall.publicBank w (addressed rs (d b)) (fun _ => []) (pack b) (flag b))
      (PairCall.publicBank w (addressed rs (d b)) (fun _ => []) p' f'))
    (room : ∀ z, (frame rs res (storage w d pack flag v aux) z).length ≤ S) :
    (r.onPorts (pairPorts b)).BoundedRun S n (frame rs res (storage w d pack flag v aux))
      (frame rs res (storage w d (Function.update pack b p') (Function.update flag b f') v aux)) := by
  apply run.framed (pairPorts_injective b) room (pairFrame rs res d pack flag v aux b)
  · intro q
    simpa only [Function.update_self] using pairFrame rs res d (Function.update pack b p') (Function.update flag b f') v aux b q
  · exact private_preserved rs res d pack flag v aux b p' f'

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
