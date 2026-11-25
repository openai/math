import OAI.Hierarchy.DescentCalendarRetainedSensors
import OAI.Hierarchy.DescentCalendarPrimaryPrimitive
import OAI.Hierarchy.DescentRetainedPacketMask

namespace OAI
/-! # Original measured low word and chronological comparator for the retained primitive -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentRetainedControl DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "m" => S.groupWidth k tail i+k
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "peer" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((id_).trans Fin.valEmbedding))
variable {M field bw N K R hm lb tiny p nbits t : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (src : RootSources deg (2^r) cap)
local notation "paid" => Recorded.paddedValue (b:=field) cc r peer (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "middle" => rc.preparedMid book space mem
local notation "done" => rc.preparedImage book space mem
local notation "rank_" => fun v j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=deg)
  (book.common rc.projectionEnd H) (2^dep) (dep+2) middle v j).val
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth

variable (x : OriginalArrays B pad field)
open DescentRotorWindowArchive
variable (move : DescentRetainedHomeMover.Layout)
local notation "v" => move.transfer
variable (hostAxis:(v).hosts=H) (dimAxis:(v).high+(v).low=m) (cutAxis:(v).cut=cc)
    (degreeAxis:move.degree=deg) (loadAxis:move.cap=cap) (fieldAxis:move.rootField=field)
local notation "lowEq" => congrArg (fun u:ℕ=>2^u) (congrArg₂ Nat.sub dimAxis cutAxis)
local notation "slots" => (lowEq).trans (axis).symm
local notation "highEq" => congrArg (fun u:ℕ=>2^u) cutAxis
local notation "lift" => (show move.control.rootWidth=field*DescentRotorWindowArchive.count deg (2^r) cap from
  congrArg₂ Nat.mul fieldAxis (by change DescentRotorWindowArchive.count move.degree (v).donors move.cap=DescentRotorWindowArchive.count deg (2^r) cap;exact congrArg₂ (fun n c=>DescentRotorWindowArchive.count n (v).donors c) degreeAxis loadAxis |>.trans (congrArg (fun n=>DescentRotorWindowArchive.count deg n cap) slots)))
local notation:max "data" h:arg hi:arg => encode field _ (calendar_sender_matrix B M field rc book space mem hdr x h hi)
def moverWindow (u : Fin (v).hosts) (hi : Fin (v).grouped) : Cell move.control.rootWidth :=
  (data (u.cast hostAxis) (hi.cast highEq)).cast (congrArg (fun j:ℕ=>2^j) (lift).symm)

local notation "observed" => moverWindow B rc book space mem hdr x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
local notation:max "cmp" hi:arg a:arg b:arg => GroupStage.previousDigit B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) hi a b

theorem mover_filter (packet : RootPacket B rc book space mem hdr src x nbits t)
    (short:t≤field) (positive:0<field) (target:ℕ) (u : Fin (v).hosts) (hi : Fin (v).grouped) :
    filter (D:=move.degree) (L:=(v).donors) («cap»:=move.cap) (some target) (observed u hi)=
      vector (fun j=>decide (x.stencil (u.cast hostAxis) (hi.cast highEq) (j.cast lowEq)/2=target))
        (fun j l=>cmp (hi.cast highEq) (j.cast lowEq) (l.cast lowEq)):=by
  have result:=primary_original_mask B rc book space mem hdr src x packet positive short (u.cast hostAxis) (hi.cast highEq) target
  have transported:=primary_mask_cast degreeAxis slots loadAxis fieldAxis (some target) _ _ _ result
  simp only [Fin.cast_cast] at transported
  exact transported

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
