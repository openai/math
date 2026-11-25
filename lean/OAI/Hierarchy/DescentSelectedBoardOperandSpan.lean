import OAI.Hierarchy.DescentSelectedBoardPaletteBirth
import OAI.Hierarchy.DescentRegisteredFreshSpan
import OAI.Hierarchy.DescentOrdinaryBornDonor

namespace OAI
/-! The fresh operand span of a matched node in the registered ordinary book. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "J" => (S).groupCount v.age
local notation "H" => v.area.H
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:((T).result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

variable (B:v.SelectedBoard oldFit R selected m parts)


open DescentOrdinaryBorn DescentOrdinaryPaletteBirth DescentPrimitivePalette
variable (choiceEq : HEq selected v.choice)
local notation "same_" => (atSelected v selected choiceEq).link.donorChart.same
local notation "raw" h:arg g:arg => DepotRAM.chip fmt (A).cap v.profile (G).b (phys).materialFormat.slots (B.material h g)
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "q₀" j:arg => (⟨(rr).pick (j,0),(A).quantum_positive _ ((rr).picked (j,0))⟩ : pos_)
local notation "seat_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "bytes" => donorNameBits v.stage.k v.stage.Δ


include choiceEq in
/-- The first edge of a real matched pair supplies the eight counts on this board's original chip. -/
theorem SelectedBoard.span_donor (i : (rr).pairs) :
    let u:=v.world.graph.src ((rr).pick (i,0))
    let donor:=chipDonor fmt (raw (hosts ((A).pos u).2) ((A).pos u).1)
      (finProdFinEquiv ((A).block u,seat_ (q₀ i)))
    donor.first=true ∧ ∀e,(donor.supplyUnits e).val=(((rr).profile selected i).val e).val+(G).k :=by
  have stock:=Stage.issued_birth_donor A native S v.prior.valid rank B.win v.nonnegative grp hosts B.live
    v.prior.valid.coordinates B.named B.small B.winning B.degree B.ordered v.profile B.topo B.matched B.width
    B.topology selected B.births B.issued R B.neighbors (A).hub same_ lay B.offspring (q₀ i)
    (phys).materialFormat.slots bytes v.age i rfl
  exact ⟨stock.1,stock.2.1⟩

local notation "dateRows" => BitDescription.scannedRows v.nonnegative v.stage
local notation "dateSeed" i:arg =>
  (⟨(dateRows).pick (i,0),(A).quantum_positive _ ((dateRows).picked (i,0))⟩ : pos_)


include choiceEq in
theorem SelectedBoard.dated_donor_span (i : (dateRows).pairs) :
    let u:=v.world.graph.src ((dateRows).pick (i,0))
    let donor:=chipDonor fmt (raw (hosts ((A).pos u).2) ((A).pos u).1)
      (finProdFinEquiv ((A).block u,seat_ (dateSeed i)))
    donor.first=true ∧ ∀e,(donor.supplyUnits e).val=(((dateRows).profile v.choice i).val e).val+(G).k :=by
  have stock:=SelectedBoard.span_donor v oldFit R selected m parts B choiceEq
  cases v with
  | mk dim worldBits gadget_ sched_ price_ rate_ eps_ k_ date_ z_ degree_ wire_ hist_ nz nd world_ prior_ he_ stage_ c n_ target_ link old_ reference_ bornBook_
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have chosenEq : selected = c := eq_of_heq choiceEq
    subst selected
    exact stock i

private theorem equal_donor {src dst : DepotRAM.Shape} (eqn : src=dst)
    {a : DepotRAM.Parts src} {b : DepotRAM.Parts dst} (same : HEq a b)
    (x : Fin dst.blocks) (s : Fin dst.cap) (profile demand slots : ℕ) :
    let before:=chipDonor src (DepotRAM.chip src src.cap profile demand slots a)
      (finProdFinEquiv (x.cast (congrArg DepotRAM.Shape.blocks eqn).symm,s.cast (congrArg DepotRAM.Shape.cap eqn).symm))
    let after:=chipDonor dst (DepotRAM.chip dst dst.cap profile demand slots b) (finProdFinEquiv (x,s))
    before.first=after.first ∧ ∀e,(before.supplyUnits e).val=(after.supplyUnits e).val :=by
  subst dst
  obtain rfl:=eq_of_heq same
  exact ⟨rfl,fun _=>rfl⟩

include choiceEq in
/-- The three fields for a genuine fresh node, read from the physical predecessor selected for it.
Arguments beyond the fresh party's inventory read zero. -/
theorem SelectedBoard.native_operand_span (entry : v.ArgumentEntry) (input : entry.InputShape v)
    (floor : ℕ) (mat : entry.Match v floor)
    (parts₀ : Fin entry.clip.venue.hosts→Fin entry.clip.venue.groups→DepotRAM.Parts entry.clip.venue.socket)
    (socket : entry.clip.venue.socket=fmt) (profileEq : entry.clip.venue.profile=v.profile)
    (slotsEq : entry.clip.venue.slots=(phys).materialFormat.slots)
    (blocks : v.bornBook.blocks=entry.clip.venue.socket.blocks) (cap : v.bornBook.cap=entry.clip.venue.socket.cap)
    (names : v.bornBook.names=entry.clip.venue.socket.names) (widths : v.bornBook.widths=entry.clip.venue.socket.widths)
    (wide : 0<v.bornBook.bits) (demand : v.bornBook.demand=(G).b) (scaleAt : v.bornBook.scale=v.stage.z)
    (i : (dateRows).pairs) (party : Fin 6) (h : Fin entry.clip.venue.hosts) (g : Fin entry.clip.venue.groups)
    (mounted : let u:=v.world.graph.src ((dateRows).pick (i,0))
      HEq (parts₀ h g) (B.material (hosts ((A).pos u).2) ((A).pos u).1))
    (arg : Fin v.vector.operands) (f : Fin 3) :
    let u:=v.world.graph.src ((dateRows).pick (i,0))
    let block:=((A).block u).cast ((congrArg DepotRAM.Shape.blocks socket).symm.trans (blocks.symm.trans mat.newBlocks))
    let seat:=(seat_ (dateSeed i)).cast ((congrArg DepotRAM.Shape.cap socket).symm.trans (cap.symm.trans mat.newCap))
    (entry.bornInput v input floor mat parts₀ (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) arg)
      block seat party h g).val =
      if arg.val < DescentFreshRoleFields.arity G v.bornBook.grain v.stage.z ((dateRows).profile v.choice i) party then
        (if f.val=0 then 0 else 1) else 0 :=by
  intro u block seat
  have selectedStock:=SelectedBoard.dated_donor_span v oldFit R selected m parts B choiceEq i
  have eqn:=equal_donor socket mounted ((A).block u) (seat_ (dateSeed i)) v.profile (G).b (phys).materialFormat.slots
  have issued:=entry.born_input_span v input floor mat blocks cap names widths wide demand parts₀ arg block seat party h g
    ((dateRows).profile v.choice i)
  dsimp only at issued
  rw [profileEq,slotsEq] at issued
  have first:=eqn.1.trans selectedStock.1
  have amount (e : Fin 8):=(eqn.2 e).trans (selectedStock.2 e)
  have blockEq : (block.cast mat.newBlocks.symm).cast blocks =
      ((A).block u).cast (congrArg DepotRAM.Shape.blocks socket).symm := Fin.ext rfl
  have seatEq : (seat.cast mat.newCap.symm).cast cap =
      (seat_ (dateSeed i)).cast (congrArg DepotRAM.Shape.cap socket).symm := Fin.ext rfl
  erw [blockEq, seatEq] at issued
  specialize issued (by with_unfolding_all exact first)
    (fun e => by with_unfolding_all exact amount e) f
  simpa only [scaleAt] using issued

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
