import OAI.Hierarchy.DescentOriginalSignedPhase
import OAI.Hierarchy.DescentOrdinaryReciprocalHost
import OAI.Hierarchy.DescentDatedSignedMeasuredRun
import OAI.Hierarchy.DescentDatedOriginalMarkIdentity

namespace OAI
/-! The donor board is observed at the original matching date: the selected two colors,
the six birth records, and the original topology are all tied to that same prior stage. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentPacking.PackedMatch
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
attribute [local irreducible] Stage.nativeParts topologyWords Gather.flat terrain spread
  pairNumber slabPacking Stage.slot
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "r" => 2^v.k
local notation "J" => (S).groupCount v.age
local notation "M" => lanes v.payload (v.ticket.installedDonorWidth v.short v.profile)
local notation "H" => v.area.H
local notation "ss" => (phys).signed
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "peers" => rotor A rank
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "K" => 2^(v.k+1)
local notation "s" => shape r D (2*(A).cap) v.profile
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤v.area.H) (R:Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

private def boardTopology {bits : ℕ} (win : Fin J × v.prior.V → Fin r → Cell bits)
    (topo : ℕ) (matched : Memory w) : Prop :=
  let grid:=terrain (short:=v.short) A native S v.prior.valid (cableNames v.k rank) win peers
  let board:=Gather.flat (Gather.descriptorInputs («K»:=K) s (A).cap (spread (grp).toEmbedding hosts grid))
  ∀i : Fin ((K*H)*chunks J M),matched (topo+i.val)=((topologyWords («M»:=M) («H»:=K*H) («G»:=J) s board i).val:Computability.VPVNP.BurstRAM.Word w)

private def boardOffspring (live : 0<M) (births : ℕ) (issued : Memory w) : Prop :=
  ∀c:ScanColonies v.nonnegative T,∀e:Matched traffic (A).cap (thinList home color c) (thickList home color c),
    ∃j:Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (DescentPacking.live traffic))
      (slabPacking traffic (A).cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q:Fin 6,let seat:=slot v.nonnegative A (grp).toEmbedding hosts live c
      let ip:=SixBirths.slot seat.2 j q
      SixBirths.atom (T).z (digit ((s).digit+1) ip.val (issued (births+seat.1.val)).val) ip.val=
        some ((T).z,DescentTerminalEpochFlags.encode ((rr).profile selected ⟨c,e⟩),q.val)

private def boardSource {bits : ℕ} (win : Fin J × v.prior.V → Fin r → Cell bits)
    (live : 0<M) (births : ℕ) (issued : Memory w) : Prop :=
  DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine fmt
    (Stage.nativeParts (short:=v.short) («H»:=H) («G»:=J) A native S v.prior.valid rank win grp hosts live v.profile births issued R (A).hub lay
      (donorNameBits v.stage.k v.stage.Δ) h g)) M m


structure SelectedBoard : Type where
  live : 0<M
  bits : ℕ
  win : Fin J × v.prior.V→Fin r→Cell bits
  named : (A).SiteNamed rank
  small : ∀u,(win ((A).pos u) ((A).block u)).val<2^v.short
  winning : ∀u,(win ((A).pos u) ((A).block u)).val=1+2*heap (addr (home u)).2+(color u).toNat
  degree : D<2^v.short
  ordered : ∀e f,native e<native f ↔ originalId v.world.graph.Edge e<originalId v.world.graph.Edge f
  topo : ℕ
  matched : Memory w
  width : (s).outputBits*M≤w
  topology : boardTopology v oldFit win topo matched
  births : ℕ
  issued : Memory w
  neighbors : ∀z:Fin J×v.prior.V,∀j,R (hosts z.2) j=(peers z j).map (fun h=>hosts h.2)
  offspring : boardOffspring v oldFit selected live births issued
  source : boardSource v oldFit R selected m parts win live births issued

/-- Construct the measured input directly from the winning, topology, birth and
retained-board conjuncts of the original matching date. The host rotor alone
determines the source's neighbor names at every group. -/
def selected_board_of_match (hm:0<M) (win:Fin J×v.prior.V→Fin r→Cell (v.k+3)) (named:(A).SiteNamed rank)
    (field:max (v.k+3) (Nat.clog 2 (D+1))≤v.short)
    (order:∀e f,native e<native f ↔ originalId v.world.graph.Edge e<originalId v.world.graph.Edge f)
    (winner:∀u,(win ((A).pos u) ((A).block u)).val=1+2*heap (addr (home u)).2+(color u).toNat)
    (top births:ℕ) (active:Memory w) (width:(s).outputBits*M≤w)
    (topology:let grid:=terrain (short:=v.short) A native S v.prior.valid (cableNames v.k rank) win peers
              let board:=Gather.flat (Gather.descriptorInputs («K»:=K) s (A).cap (spread (grp).toEmbedding hosts grid))
              ∀i : Fin ((K*H)*chunks J M),active (top+i.val)=((topologyWords («M»:=M) («H»:=K*H) («G»:=J) s board i).val:Computability.VPVNP.BurstRAM.Word w))
    (birth:∀c:ScanColonies v.nonnegative T,∀e:Matched traffic (A).cap (thinList home color c) (thickList home color c),
      ∃j:Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (DescentPacking.live traffic))
        (slabPacking traffic (A).cap (thinList home color c) (thickList home color c)).decisions e).val ∧
        ∀q:Fin 6,let seat:=slot v.nonnegative A (grp).toEmbedding hosts hm c
        let ix:=SixBirths.slot seat.2 j q
        SixBirths.atom (T).z (digit ((s).digit+1) ix.val (active (births+seat.1.val)).val) ix.val=
          some ((T).z,DescentTerminalEpochFlags.encode ((rr).profile selected ⟨c,e⟩),q.val))
    (retained:DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine fmt
      (Stage.nativeParts (short:=v.short) («H»:=H) («G»:=J) A native S v.prior.valid rank win grp hosts hm v.profile births active
        (hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))) (A).hub lay
        (donorNameBits v.stage.k v.stage.Δ) h g)) M m) :
    v.SelectedBoard oldFit (hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding)))
      selected m parts :=by
  refine ⟨hm,v.k+3,win,named,?_,winner,?_,order,top,active,width,topology,births,active,?_,birth,retained⟩
  · intro u
    exact (win ((A).pos u) ((A).block u)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans field))
  · exact (Nat.lt_succ_self D).trans_le ((Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans field)))
  · intro z j
    exact DescentGroupPeerOrder.extended_group A hosts ((hosts).trans Fin.valEmbedding) Fin.valEmbedding z j

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
