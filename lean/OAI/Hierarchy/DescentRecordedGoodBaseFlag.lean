import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentResetPeerRecordedFlag

namespace OAI
/-! Read the rotor-root mode directly from the reached physical high group. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
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

open DescentRotorRootPresence
private theorem original_basis {oldWidth newWidth : ℕ} (eqn : oldWidth=newWidth) (μ : DescentGL.Layout newWidth) :
    HEq (cast (congrArg DescentGL.Layout eqn.symm) μ) μ := by
  cases eqn
  rfl

variable {x : OriginalArrays B pad field} (packet : RootPacket B rc book space mem hdr src x nbits t)
local notation "axis" => congrArg (fun z=>2^(z-cc)) B.keyWidth

include packet in
/-- The original sampled flag is zero at every good root, including a root carrying no grains. -/
theorem RootPacket.good_base_flag (recorded : B.Recorded p)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (amount : 2^r*full < 2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds)
    (degreePos : 0 < 32*Nat.clog 2 (2*deg)) (g₀ : (Z).placement.Good) :
    x.stencil (id_ (B.frame.host.symm g₀.val.1)) ((Z).rootBlock T (.inl g₀))
      (Fin.cast axis (sample ((Z).goodLabel T g₀))) % 2 = 0 := by
  let u:=B.frame.host.symm g₀.val.1
  let hi:=(Z).rootBlock T (.inl g₀)
  let root:=(Z).goodLabel T g₀
  let μ : DescentGL.Layout (Z).k:=cast (congrArg DescentGL.Layout B.keyWidth.symm) B.frame.basis
  have won : HEq μ B.frame.basis:=original_basis B.keyWidth B.frame.basis
  let oldWord:=fun lo : Block r=>x.stencil (id_ u) hi (Fin.cast axis lo)
  have mode (lo : Block r) : oldWord lo % 2 =
      Bool.toNat (decide ((Z).placement.hub g₀.val.1 ∨ (g₀.val.1,group ((Z).placement.b g₀.val.1)
        (join (((T).commonLow g₀.val.1).trans ((Z).placement.depth _)) hi lo)) ∈ (Z).placement.keys)) := by
    have cell:=congrArg Fin.val (original_column_stamp B x μ won packet.word u hi lo)
    change (oldWord lo : Cell t).val = _ at cell
    have bounded : oldWord lo < 2^t := packet.short (id_ u) hi (lo.cast axis)
    rw [Fin.val_cast_of_lt bounded] at cell
    rw [cell]
    simpa only [u,Equiv.apply_symm_apply] using
      recorded.private_mode μ won level one amount shape active quotaPos degreePos u hi lo
  have hit:=(root_present Z T g₀.val.1 hi root oldWord mode).2 ⟨g₀,rfl,rfl,rfl⟩
  exact (of_decide_eq_true hit).2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
