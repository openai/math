import OAI.Hierarchy.DescentResetSignedAll
import OAI.Hierarchy.DescentIssuedOrdinalTarget

namespace OAI
/-! Separate natural bounds for the stamped candidate serial and the local adjustment. -/
noncomputable section
namespace Hierarchy.DescentResetWindowFields
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentNextSignedWindow.Native
open scoped Classical
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] {d k i : ℕ} {bits : P→ℕ}
  {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
local notation "B" => Stage.source A native
local notation "fit" => Stage.measured A native S ready
variable (C : Blocks (Stage.source A native) E) (marked : E→Prop)

omit [Fintype E] in
theorem record_shared_le (h : Stage.Host J V k) (u : Roster.Face A native C h) (neighbor : Fin A.degree) :
    DescentNextSignedWindow.Native.fields (some (record A native S ready C marked h u neighbor)) 5≤(A).cap :=by
  let e:=u.val.1
  let first : Fin (C.count e):=⟨0,u.property.1⟩
  have inParallel : C.order ⟨e,first⟩∈(B).parallel (C.src e) (C.dst e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨C.atSource e first,C.atTarget e first⟩⟩
  exact Nat.le_of_lt ((B).serial_lt fit (C.src e) (C.dst e) _ inParallel)
end Hierarchy.DescentResetWindowFields
end

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentNextSignedWindow
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
variable {H lanes b bitsW : ℕ}
local notation "gg" => S.groupCount (i+1)
local notation "item" => Fin (2*totalLocal B)
local notation "X" => 2^k

theorem candidate_shared_le (names : Host ↪ ℕ) (rack : Option B.next.V)
    (u : Fin gg) (x : Fin X) (a : item) :
    Native.fields (rack.bind (fun r=>candidateRows B names ((u,r),x) a)) 5≤(A).cap :=by
  cases rack with
  | none=>exact Nat.zero_le _
  | some r=>
    change Native.fields (candidateRows B names ((u,r),x) a) 5≤_
    unfold candidateRows Roster.rows
    split
    · exact DescentResetWindowFields.record_shared_le ..
    · exact Nat.zero_le _

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentOperandWidth
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

theorem serial_sum_room {k tail drift degree p : ℕ} {billed shared : ℕ}
    (correction : billed≤publicCap S) (ranked : shared≤publicCap S) :
    billed+shared<2^recordBits G S k tail drift degree p:=by
  have sum : billed+shared≤raw S:=by unfold raw;omega
  have ceiling : raw S≤bound G S drift degree:=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have fits : billed+shared<2^s G S k tail drift degree:=numeric G S (sum.trans ceiling)
  exact fits.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
end Hierarchy.DescentOperandWidth


namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentOperandWidth
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)

theorem serial_space (rest drift degree p : ℕ) :
    2*B.next.placement.cap<2^(recordBits G S k rest drift degree p):=by
  have volume : B.next.placement.cap≤publicCap S :=
    B.next.valid.capacity.trans (Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ B.age) 8))
  simpa only [two_mul] using serial_sum_room G S (k:=k) (tail:=rest)
    (drift:=drift) (degree:=degree) (p:=p) volume volume
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
