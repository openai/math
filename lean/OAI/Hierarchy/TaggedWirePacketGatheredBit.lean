import OAI.Hierarchy.TaggedWideChordAperture
import OAI.Hierarchy.TaggedWideActiveBits
import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWirePacketPortBits
import OAI.Hierarchy.TaggedWireAggregatePrefix
import OAI.Hierarchy.TaggedWireShelfReads

namespace OAI
/-! # Read a paid lane directly in the packed active neighbor, with all parallel physical prefixes -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe Tagged CalendarTape
open scoped Classical BigOperators

variable {S n m t D K : ℕ} (edge : Fin m→Chord S) (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (ord : Fin t≃Σi,Fin (route i).length)
local notation "mass" => routeLoad route bits
local notation "alloc" => NativeSlot.allocation route bits ord
local notation "shift" => AggregatePrefix.paidShift route bits ord edge

def bank {s : Fin S} {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (state : (portGraph S).Port s→ℕ→Bool) (role digit : ℕ) :=
  if a:role<D then if b:digit<K then ChordAperture.canonical parts state ⟨role,a⟩ ⟨digit,b⟩ else false else false

theorem bank_digit {s : Fin S} {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (state : (portGraph S).Port s→ℕ→Bool) (cap : ∀p,total p≤K) (p : (portGraph S).Port s)
    (j : Fin (total p)) : bank parts state (index parts (other p)) j.val=state p j.val := by
  obtain ⟨q,eq,own⟩:=found parts p (Nat.zero_lt_of_lt j.isLt)
  rw [←eq]
  simp [bank,q.isLt,j.isLt.trans_le (cap p),ChordAperture.canonical,own,j.isLt]

theorem paid_bit (s : Fin S) {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (cap : ∀p,total p≤K) (state : (portGraph S).Port s→ℕ→Bool) (y : State (installedWidths edge mass) s)
    (width : ∀p : (portGraph S).Port s,installedWidths edge mass p.val.1≤total p)
    (active : ∀p : (portGraph S).Port s,∀d : Fin (installedWidths edge mass p.val.1),state p d.val=(y p).val.testBit d.val)
    (i : Fin n) (j : Fin (bits i)) (q : Fin (route i).length) (b : Bool)
    (here : (rowGraph edge).vertex ((route i).get q) b=s) :
    bank parts state (index parts ((rowGraph edge).vertex ((route i).get q) (!b)))
        (shift ((route i).get q)+NativeSlot.start route bits ord i q+j.val)=
      rowBits edge mass y (PacketTurns.paidPort edge route bits ord i j q b here) := by
  let raw:=PacketTurns.paidPort edge route bits ord i j q b here
  let p:=sourcePort edge mass raw
  let d:=NamedAperture.sourceBit edge mass raw.val.1
  let id:=(route i).get q
  have key : raw.val.1.1=id:=NativeSlot.allocation_edge route bits ord _
  have bit : raw.val.1.2.val=NativeSlot.start route bits ord i q+j.val :=
    NativeSlot.allocation_value route bits ord i q j
  have head : other p=(rowGraph edge).vertex id (!b) := by
    change (portGraph S).vertex (edge raw.val.1.1) (!b)=(rowGraph edge).vertex id (!b)
    rw [key]
    cases b <;> rfl
  have whereAt : d.val=shift id+NativeSlot.start route bits ord i q+j.val := by
    exact (AggregatePrefix.sourceBit_val route bits ord edge raw.val.1.1 raw.val.1.2).trans
      ((congrArg₂ Nat.add (congrArg (AggregatePrefix.paidShift route bits ord edge) key) bit).trans
        (Nat.add_assoc _ _ _).symm)
  have atWidth : d.val<total p:=d.isLt.trans_le (width p)
  rw [←whereAt,←head,show bank parts state (index parts (other p)) d.val=state p d.val from
    bank_digit parts state cap p ⟨d.val,atWidth⟩,active p d,NamedAperture.rowBit_datum]
  rfl

theorem state_cast_val {S : ℕ} {A B : Widths S} (same : A=B) (s : Fin S)
    (z : State A s) (p : (portGraph S).Port s) :
    ((cast (congrArg (fun U=>State U s) same) z) p).val=(z p).val := by subst B;rfl

/-- An actual simultaneous pass exposes its selected packet as the low
digits; all other packet states at this participant have unique values. -/
theorem active_state {r : ℕ} (s : Fin S) (rest : Widths S) (gs : Fin r→Widths S)
    (pick : Fin r) (shape : gs pick=installedWidths edge mass)
    (away : ∀i,i≠pick→Subsingleton (State (gs i) s)) (z : State (rest+∑i,gs i) s)
    (p : (portGraph S).Port s) (j : Fin (installedWidths edge mass p.val.1)) :
    (z p).val.testBit j.val=
      ((cast (congrArg (fun U=>State U s) shape)
        (blockPortState gs s ((splitPortState rest (∑i,gs i) s z).2) pick)) p).val.testBit j.val := by
  rw [state_cast_val shape s _ p]
  exact (PassMatrix.active_digit rest gs pick s away z p (j.cast (congrArg (fun z : Widths S=>z p.val.1) shape).symm)).symm

end Hierarchy.WireTelescope.PacketNeighbor

end
end OAI
