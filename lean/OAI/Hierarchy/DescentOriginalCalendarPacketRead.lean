import OAI.Hierarchy.DescentCalendarMeasuredSender
import OAI.Hierarchy.DescentPhysicalFundedRoots

namespace OAI
/-! # Both original public operand words at a measured calendar address -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentSharedBookScan
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open private packet_preserved
  from OAI.Hierarchy.DescentPhysicalFundedRoots
noncomputable section
set_option hygiene false
set_option quotPrecheck false
set_option maxHeartbeats 380000

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
local notation:max "fallback" v:arg hi:arg => encodePacket (inputs (n:=(Z).n) («r»:=r) (field:=field)
  localStencil x.peers localMarks rank_ v hi)
local notation:max "matrix" v:arg hi:arg => encode field (DescentRotorWindowArchive.count deg (2^r) cap)
  (RootSources.paddedRow (n:=(Z).n) («r»:=r) localStencil x.peers localMarks rank_ order_ paid v hi)

/-- Both whole words use the attained old host and selected coarse group. The fallback and
matrix inputs share the original stencil, peer, signed, and rank fields at the reached key width.
The matrix also reads the predecessor comparison and the directed reservations. -/
theorem original_calendar_words (v : Fin H) (hi : Block cc) :
    (savedInput B pad snapshot v hi).val=(fallback v hi).val ∧
    (encode field _ (calendar_sender_matrix B M field rc book space mem hdr x v hi)).val=(matrix v hi).val :=by
  constructor
  · rw [saved_input_eq,root_snapshot_input]
    exact packet_preserved axis x.stencil x.peers x.marks rank_ v hi
  · rw [calendar_sender_matrix_eq]

/-- Transport two earlier issued cells to the physical old row even when the
operand page uses different field-width indices. -/
theorem original_calendar_packet_read (v : Fin H) (hi : Block cc) {b₀ b₁ : ℕ}
    (oldFallback : Cell b₀) (oldMatrix : Cell b₁)
    (fallbackAt : oldFallback.val=(savedInput B pad snapshot v hi).val)
    (matrixAt : oldMatrix.val=(encode field _ (calendar_sender_matrix B M field rc book space mem hdr x v hi)).val) :
    oldFallback.val=(fallback v hi).val ∧ oldMatrix.val=(matrix v hi).val :=by
  have read:=original_calendar_words B rc book space mem hdr x v hi
  exact ⟨fallbackAt.trans read.1,matrixAt.trans read.2⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
