import OAI.Hierarchy.DescentOriginalCalendarPacketRead
import OAI.Hierarchy.DescentOperandOriginalFields

namespace OAI
/-! # The original operand row at a named previous host and coarse group -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentSharedBookScan
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "cc" => B.terminals.commonDepth
local notation "r" => (Z).k-cc
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "pad" => input.valid.host
local notation "axis" => congrArg (fun m=>2^(m-cc)) B.keyWidth
variable {M field bw N K Rep hm lb tiny : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K Rep M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (x : OriginalArrays B pad field)
local notation "snapshot" => root_snapshot B pad rc book space mem hdr x
local notation "localStencil" => fun u hi (lo : Block r)=>x.stencil u hi (lo.cast axis)
local notation "localMarks" => fun u hi (lo : Block r)=>x.marks u hi (lo.cast axis)
local notation "rank_" => fun v j=>(ranks (a:=r) (Y:=2^(Z).n) (D:=deg) (book.common rc.projectionEnd H)
  (2^dep) (dep+2) (rc.preparedMid book space mem) v j).val
local notation "order_" => fun (_ : Fin H) hi a b=>GroupStage.previousDigit B.frame.basis
  (B.frame.enough.trans (Nat.sub_le ..)) hi (Fin.cast axis a) (Fin.cast axis b)
local notation "paid" => Recorded.paddedValue (b:=field) cc r
  (PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad) (Recorded.oldDepth B) (Recorded.oldWidth B)

open DescentRotorWindowArchive

def originalFallback (v : Fin H) (hi : Block cc) : Packet deg (2^r) cap (Z).n r field :=
  inputs localStencil x.peers localMarks rank_ v hi

def originalMatrix (v : Fin H) (hi : Block cc) : Fin (DescentRotorWindowArchive.count deg (2^r) cap)→Cell field :=
  RootSources.paddedRow (n:=(Z).n) («r»:=r) localStencil x.peers localMarks rank_ order_ paid v hi

/-- The fallback and matrix packets share the stencil/peer and signed portions
of exactly the same old host and old coarse group. -/
theorem original_shared (v : Fin H) (hi : Block cc) :
    let row:=originalMatrix B rc book space mem x v hi
    let fall:=originalFallback B rc book space mem x v hi
    (∀j,row (ix (.inl (.inl j)))=fall (.inl j)) ∧
      ∀j,row (ix (.inl (.inr j)))=fall (.inr (.inl j)):=by
  constructor <;> intro j <;> simp only [originalMatrix,RootSources.paddedRow,Equiv.symm_apply_apply] <;> rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
