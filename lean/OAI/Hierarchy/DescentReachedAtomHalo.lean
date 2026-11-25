import OAI.Hierarchy.DescentReachedOrdinaryBook
import OAI.Hierarchy.DescentScannedHost

namespace OAI
/-! # The physically bounded donor rack for the actual reached ordinary book -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "M" => ticket.issued.measured_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => (deg+1)^4*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

def rackName : capV ↪ ℕ :=
  ((Function.Embedding.prodMap (Function.Embedding.refl _) cap.vertex).trans finProdFinEquiv.toEmbedding).trans Fin.valEmbedding

def reachedHalo : Halo C W.graph.Site bound where
  member h:=siteSet (near) (A).pos h.val
  slot h:=(raster (near) (A).pos (A).block cap.valid.coordinates deg (A).stage.degree (rackName (cap:=cap))).slot h.val

theorem reachedHalo_order (v : C) (x y : ↥((reachedHalo ticket).member v)) :
    (reachedHalo ticket).slot v x<(reachedHalo ticket).slot v y ↔ sites x.val<sites y.val := by
  rw [show sites x.val<sites y.val ↔ ((A).siteSlot cap.vertex cap.valid.coordinates x.val).val<
    ((A).siteSlot cap.vertex cap.valid.coordinates y.val).val from DescentPhysicalOrder.physical_lt_iff _ _ _]
  rw [(A).siteSlot_val,(A).siteSlot_val]
  apply (raster_lt (near) (A).pos (A).block cap.valid.coordinates deg (A).stage.degree
    (rackName (cap:=cap)) v.val x y).trans
  simp [rackName,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

set_option maxHeartbeats 1600000 in
theorem reachedHalo_members :
    (∀v : W.graph.Site, v∈(reachedHalo ticket).member (venue (.inl v))) ∧
    (∀i j,W.graph.src ((r).pick (i,0))∈(reachedHalo ticket).member (venue (.inr (i,j)))) := by
  obtain rfl := ticket.sourceRate
  obtain rfl := eq_of_heq ticket.placement
  let T:=(A).stage
  let rr:=BitDescription.scannedRows he T
  let ix:=BitDescription.scanBlocks T rr.μ
  let mass:=W.siteUnits T.hub T.records T.wire 256 T.hist
  let scale:=T.wire*(T.z*G.b)
  let U:=scale*T.cap
  let load:=blockMass W.graph (A).pos ix mass
  let sm:=small_reindexed W.graph (A).pos (A).block mass (A).small (multiplier T.fieldBits rr.μ)
  let sheet:=fun j : Block k=>decide (binaryRow rr.α ((DescentColonies.address k).symm j)+rr.β=0)
  let home:=scanHomeAt he T
  let paint:=scanColorAt he T
  let b:=activeChart ticket
  have hs : 0<scale := Nat.mul_pos (A).wirePos (Nat.mul_pos (A).unitPos G.base_pos)
  have costs:=W.siteUnits_outgoing T.hub T.records T.wire 256 T.hist home scale (fun e h=>by rw [(A).widths e h]; exact le_rfl) (by decide)
  have pairs:=scaled_pair_cap W.graph (A).pos ix mass (near) 20 deg U (A).cap sm W.core sheet scale hs rfl costs
  have coords (v : W.graph.Site) : b.col (home v)=colonyCode W.graph U (near) (gap deg)
      (packExponent 20 deg) load sm (A).pos ix v := by
    rw [eq_of_heq b.native]
    exact occupiedAddress_colonyOf ..
  have aligned (e : W.graph.Edge) : ix (W.graph.src e)=ix (W.graph.dst e) :=
    congrArg (rearrange (multiplier T.fieldBits rr.μ)) ((A).same e)
  let lay := bestLayout (branchWidth G (fun _ : rr.pairs => T.z) (rr.profile c))
  constructor
  · intro v
    exact native_old_member W.graph W.core home paint (A).cap b.col (near) (gap deg) (packExponent 20 deg)
      load sm (A).pos ix _ (A).capPos pairs coords aligned (A).peers b.same lay b.hub _ v
  · intro i j
    exact native_born_member W.graph W.core home paint (A).cap b.col (near) (gap deg) (packExponent 20 deg)
      load sm (A).pos ix _ (A).capPos pairs coords aligned (A).peers b.same lay b.hub _ i j

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
