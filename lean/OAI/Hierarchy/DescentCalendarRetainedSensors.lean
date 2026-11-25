import OAI.Hierarchy.DescentCalendarMatrixOrigins
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
local notation:max "rootWord" h:arg hi:arg => encode field _ (calendar_sender_matrix B M field rc book space mem hdr x h hi)
local notation "oldAt" => fun (v : Fin H) (hi : Block cc) (j : Block r)=>x.stencil v hi (j.cast axis)
local notation:max "cmp" hi:arg i:arg j:arg => GroupStage.previousDigit B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) hi
  (Fin.cast axis i) (Fin.cast axis j)

/-- On any actual donor, its very same earlier measured mask carries the short
physical home of the actor at the inverse-GL digit. -/
theorem primary_original_stencil (u : input.V) (hi : Block cc) (lo : Block (m-cc)) :
    x.stencil (id_ u) hi lo/2=
      DescentPlainTerminal.Suffix.Stencil.shapeCode (m-cc) (2^(Z).n)
        (DescentPlainTerminal.Suffix.fieldsRelative cc (Recorded.originalCell (reset:=B) u
          ((rearrange B.frame.basis).symm (join (B.frame.enough.trans (Nat.sub_le ..)) hi lo)))):=by
  rw [x.localRead]
  exact x.shape u hi lo

/-- The actual old root register suffices for every statically scheduled public
target and every donor. Its raw matrix includes empty hosts, quota and signed
fields from the same frozen observation. -/
theorem primary_original_mask (packet : RootPacket B rc book space mem hdr src x nbits t)
    (fieldPos:0<field) (narrow:t≤field) (u : Fin H) (hi : Block cc) (target : ℕ) :
    filter (D:=deg) (L:=2^r) («cap»:=cap) (some target) (rootWord u hi) =
      vector (fun j => decide (oldAt u hi j/2=target)) (fun a b=>cmp hi a b):=by
  rw [calendar_sender_matrix_eq]
  exact padded_selector _ _ _ _ _ _ u hi target fieldPos
    (fun j=>(packet.short u hi (j.cast axis)).trans_le (Nat.pow_le_pow_right (by decide) narrow))

/-- Width casts of a measured root vector preserve its two selected predicates
at each numerical old donor. This lets the retained-field and primitive charts
use their independently chosen pitches and the identical old root packet. -/
theorem primary_mask_cast {D₁ D₂ L₁ L₂ C₁ C₂ F₁ F₂ : ℕ} (degreeEq:D₁=D₂)
    (slots:L₁=L₂) (capEq:C₁=C₂) (field:F₁=F₂) (target : Option ℕ)
    (packet : Cell (F₂*DescentRotorWindowArchive.count D₂ L₂ C₂))
    (keep : Fin L₂→Bool) (prior : Fin L₂→Fin L₂→Bool)
    (ready : filter (D:=D₂) (L:=L₂) («cap»:=C₂) target packet=vector keep prior) :
    filter (D:=D₁) (L:=L₁) («cap»:=C₁) target
      (packet.cast (congrArg (fun n:ℕ=>2^n) (show F₂*DescentRotorWindowArchive.count D₂ L₂ C₂=
        F₁*DescentRotorWindowArchive.count D₁ L₁ C₁ by rw [degreeEq,slots,capEq,field])))=
      vector (fun j=>keep (j.cast slots)) (fun i j=>prior (i.cast slots) (j.cast slots)):=by
  subst D₂;subst L₂;subst C₂;subst F₂
  exact ready

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
