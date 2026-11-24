import OAI.Computability.VPVNP.RAMTapeSortOffsets
import OAI.Computability.VPVNP.RAMTapeSortRowAddress
import OAI.Computability.VPVNP.RAMTapeSortRowPorts

/-!
# Stack assignments inside a sorting layer

The address routine reads the binary index, and the record lookup reads
its unary copy. The partner count and two decision bits go directly from
the address routine to the record routine. Both routines preserve the
site identifier and the stage counters throughout the traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerRows

open BurstRAM RAMSort RAMBoundary

/-- Site address, stage counters, observed wire bits and scratch stacks used when computing the
comparator's partner and orientation. -/
inductive Extra
  | site | phase | stride | observed (axis : SortRowAddress.Axis) | bits | count | rev | tmp
  deriving DecidableEq, Fintype

/-- Combine the record-operation ports with the additional ports for computing a row's address
and partner. -/
abbrev Data := SortRow.Port ⊕ Extra
/-- The layer's data stacks together with the row iterator's binary and unary counters. -/
abbrev Port := Data ⊕ SortOffsets.Port

/-- Connect the record routine's row offset to the iterator's unary counter and its other
operands to the layer data. -/
def rowPorts : SortRow.Port → Port
  | .row => .inr .unary
  | p => .inl (.inl p)

/-- Route the address computation to the iterator's binary row index, preserved site and stage
parameters, and its decision and scratch stacks. -/
def addressPorts : SortRowAddress.Port → Port
  | .row => .inr .index
  | .site => .inl (.inr .site)
  | .index .phase => .inl (.inr .phase)
  | .index .stride => .inl (.inr .stride)
  | .orientation => .inl (.inl .orientation)
  | .offset => .inl (.inl .partner)
  | .localFlag => .inl (.inl .localFlag)
  | .observed a => .inl (.inr (.observed a))
  | .bits => .inl (.inr .bits)
  | .count => .inl (.inr .count)
  | .rev => .inl (.inr .rev)
  | .tmp => .inl (.inr .tmp)

theorem rowPorts_injective : Function.Injective rowPorts := by decide
theorem addressPorts_injective : Function.Injective addressPorts := by decide

/-- The site and stage data shared by consecutive visits. Only the accumulated
output, the two exchange streams, and the list of flags change during a layer. -/
def bank {d : ℕ} (v : Word d) (a j w : ℕ)
    (current next send recv flags : List Bool) : Stacks Data
  | .inl .current => current
  | .inl .next => next
  | .inl .crossSend => send
  | .inl .crossReceive => recv
  | .inl .width => List.replicate w true
  | .inl .flags => flags
  | .inr .site => wordBits v
  | .inr .phase => List.replicate a true
  | .inr .stride => List.replicate j true
  | _ => []

/-- This wire keeps the smaller record precisely when the stride bit and phase bit of its
global wire index agree. -/
def keepMin {h d : ℕ} (s : Stage (h+d)) (v : Word d) (i : Word h) : Bool :=
  let g := v.val * 2^h + i.val
  g.testBit s.stride == g.testBit s.phase

/-- For an in-site stride, toggle its bit in the row index to find the partner. A cross-site
comparator uses the same row at the peer site. -/
def peerIndex {h d : ℕ} (s : Stage (h+d)) (i : Word h) : Word h :=
  if hj : s.stride < h then ⟨partner s.stride i, partner_lt i.isLt hj⟩ else i

/-- The prepared row has its three address outputs installed in the record
routine's input ports, with every other port equal to the callback's entry. -/
def prepared {h d : ℕ} (s : Stage (h+d)) (v : Word d) (i : Word h) (data : Stacks Data) : Stacks Port :=
  let orig := SortOffsets.visit data i
  fun p => match p with
    | .inl (.inl .orientation) => [keepMin s v i]
    | .inl (.inl .localFlag) => [decide (s.stride < h)]
    | .inl (.inl .partner) => List.replicate (peerIndex s i).val true
    | _ => orig p

/-- Running the installed address machine leaves all pending tape streams
available to the record operation on that row. -/
theorem address_run {h d w : ℕ} (s : Stage (h+d)) (v : Word d) (i : Word h)
    (cur next send recv flags : List Bool) :
    let b := bank v s.phase s.stride w cur next send recv flags
    ∃ t ≤ SortRowAddress.budget h d s.phase s.stride,
      (SortRowAddress.routine.onPorts addressPorts).Runs t (SortOffsets.visit b i) (prepared s v i b) := by
  obtain ⟨t,ht,hr⟩ := SortRowAddress.runs i v s.phase s.stride
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ addressPorts_injective hr
  · intro p
    rw [SortRowAddress.initial_port]
    cases p <;> first | rfl | rename_i ax; cases ax <;> rfl
  · intro p
    rw [SortRowAddress.final_port, SortRowAddress.initial_port]
    cases p with
    | index ax => cases ax <;> rfl
    | offset =>
      by_cases hj : s.stride < h <;> simp [prepared, addressPorts, peerIndex, hj]
    | _ => rfl
  · intro p hp
    rcases p with (r | e) | f
    · cases r <;> first | rfl | exact (hp .orientation rfl).elim
                            | exact (hp .offset rfl).elim | exact (hp .localFlag rfl).elim
    · rfl
    · rfl

end RAMTape.SortLayerRows

end VPVNP
end Computability
end OAI
