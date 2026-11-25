import OAI.Computability.BorderVNP.RoutingISATypedTaskBuilder

/-! # Reading a typed initializer row from the actual sorted descriptor return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM

/-- The part of shared memory observed by one row gather. -/
def Layout.Reads (l : Layout) (original mem : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ a, l.inputAt i a → mem a = original a

/-- Computed output fields of a gather, retaining the immutable low register bank. -/
structure Layout.Gathered (l : Layout) (original : ℕ → ℕ) (i j : ℕ) (z : NatState) : Prop where
  /-- The row cursors and base registers. -/
  ready : l.Ready i j z
  /-- Next compact seven-word start. -/
  next : z.reg 20 = l.tasks+7*j
  /-- Public owner used for the native comparison. -/
  owner : z.reg 21 = l.owner original i
  /-- Exact seven words consumed by the packet initializer. -/
  fields : l.owner original i=l.team → [24,25,26,27,28,29,30].map z.reg = l.row original i
  /-- Address of the global owner column. -/
  call : z.reg 30 = l.call i

private theorem observed (l : Layout) (mem : ℕ → ℕ) (i : ℕ) (z : NatState) (hs : l.Reads mem z.mem i) :
    z.mem (l.banks+2*i) = mem (l.banks+2*i) ∧
    z.mem (l.banks+2*i+1) = mem (l.banks+2*i+1) ∧
    z.mem (l.offsets+2*l.cables+i) = mem (l.offsets+2*l.cables+i) ∧
    z.mem (l.sorted+l.padded+i) = mem (l.sorted+l.padded+i) ∧
    z.mem (l.sorted+l.padded+(l.stops+i)) = mem (l.sorted+l.padded+(l.stops+i)) ∧ z.mem (l.tails+i) = mem (l.tails+i) :=
  ⟨hs _ (.inl rfl),hs _ (.inr (.inl rfl)),hs _ (.inr (.inr (.inl rfl))),
    hs _ (.inr (.inr (.inr (.inl rfl)))),hs _ (.inr (.inr (.inr (.inr (.inl rfl))))),hs _ (.inr (.inr (.inr (.inr (.inr rfl)))))⟩

set_option maxHeartbeats 1600000 in
/-- All seven output columns are arithmetic and addressed loads of the current input rows. -/
theorem gather_eval (l : Layout) (mem : ℕ → ℕ) (pub : Arg → ℕ) (i j : ℕ) (z : NatState)
    (hr : l.Ready i j z) (hs : l.Reads mem z.mem i) :
    l.Gathered mem i j (gather.fixedEval pub z) ∧ (gather.fixedEval pub z).mem = z.mem := by
  have hv := hr
  unfold Layout.Ready at hv
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := observed l mem i z hs
  refine ⟨⟨fun r h => (Code.fixedEval_protected gather pub z (by decide) r h).trans (hr r h),?_,?_,?_,?_⟩,?_⟩
  all_goals by_cases own : mem (l.banks+2*i)=l.team <;> simp (config := {decide:=true}) [gather,Code.block,Code.fixedEval,Code.evalNat,own,
    addressOp,hv,Layout.regValue,Layout.owner,Layout.call,Layout.row,h1,h2,h3,h4,h5,h6]

set_option maxHeartbeats 1600000 in
/-- Every actual pointer and intermediate product is within the machine word. -/
theorem gather_safe {w : ℕ} (l : Layout) (mem : ℕ → ℕ) (room : l.Room mem w)
    (pub : Arg → ℕ) (i j : ℕ) (z : NatState) (hi : i < l.cells) (hj : j ≤ i)
    (hr : l.Ready i j z) (hs : l.Reads mem z.mem i) :
    gather.fixedSafe w pub z := by
  unfold Layout.Ready at hr
  obtain ⟨h1,_,h3,h4,h5,h6⟩ := observed l mem i z hs
  obtain ⟨rank0,rank1⟩ := room.ranks i hi
  have := room.frame
  have := room.calls
  have := room.banks
  have := room.tails
  have := room.offsets
  have := room.tasks
  have := room.sorted
  have := room.markers
  have ss := Nat.mul_le_mul_left l.scratchStride hi.le
  have sb := Nat.mul_le_mul_left l.burstStride hi.le
  have := room.scratch
  have := room.bursts
  by_cases own : mem (l.banks+2*i)=l.team
  · have extent := room.external i hi own
    simp (config := {decide:=true}) [gather,Code.block,Code.fixedEval,Code.fixedSafe,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,hr,Layout.regValue,h1,h3,h4,h5,h6,own]
    omega
  · simp (config := {decide:=true}) [gather,Code.block,Code.fixedEval,Code.fixedSafe,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,hr,Layout.regValue,h1,h3,h4,h5,h6,own]
    omega

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
