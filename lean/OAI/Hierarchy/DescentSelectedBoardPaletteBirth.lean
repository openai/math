import OAI.Hierarchy.DescentDatedSelectedCableKey
import OAI.Hierarchy.DescentIssuedOrdinaryPaletteBirth
import OAI.Hierarchy.DescentOrdinaryPrimitiveWords
import OAI.Hierarchy.DescentSelectedPaletteChipRead

namespace OAI
/-! # Birth palette rows of the actual selected board -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 6000
set_option maxHeartbeats 900000
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
variable (oldFit:Fintype.card v.prior.V≤v.area.H) (R:Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
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
/-- The nonzero birth record at an actual matched pair and party contains that
party's token from the chosen coefficient profile. -/
theorem SelectedBoard.palette_birth (seed Z : ℕ) (op : RotorSpec) (z : ℕ) (under : z≤Z)
    (i : (rr).pairs) (party : Fin 6) :
    let u:=v.world.graph.src ((rr).pick (i,0))
    let atChip:=raw (hosts ((A).pos u).2) ((A).pos u).1
    let donor:=chipDonor fmt atChip (finProdFinEquiv ((A).block u,seat_ (q₀ i)))
    DescentOrdinaryPaletteBirth.word G seed Z op z donor party=
      token G seed Z op (.inr (.inl (⟨z,Nat.lt_succ_of_le under⟩,(rr).profile selected i,party))) :=by
  exact Stage.issued_palette_birth A native S v.prior.valid rank B.win v.nonnegative grp hosts B.live
    v.prior.valid.coordinates B.named B.small B.winning B.degree B.ordered v.profile B.topo B.matched B.width
    B.topology selected B.births B.issued R B.neighbors (A).hub same_ lay B.offspring (q₀ i)
    (phys).materialFormat.slots bytes v.age i rfl seed Z op z under party

include choiceEq in
/-- Specialization to the actual stage quantum recorded in the primitive archive. -/
theorem SelectedBoard.palette_party (seed Z : ℕ) (op : RotorSpec) (under : (T).z≤Z) (i : (rr).pairs) (party : Fin 6) :
    let u:=v.world.graph.src ((rr).pick (i,0))
    let donor:=chipDonor fmt (raw (hosts ((A).pos u).2) ((A).pos u).1)
      (finProdFinEquiv ((A).block u,seat_ (q₀ i)))
    DescentOrdinaryPaletteBirth.word G seed Z op (T).z donor party=
      token G seed Z op (bornLabel (s:=seed) op (c:=selected) under i party) :=by
  exact SelectedBoard.palette_birth v oldFit R selected m parts B choiceEq seed Z op (T).z under i party

local notation "dateRows" => BitDescription.scannedRows v.nonnegative v.stage
local notation "dateSeed" i:arg =>
  (⟨(dateRows).pick (i,0),(A).quantum_positive _ ((dateRows).picked (i,0))⟩ : pos_)

include choiceEq in
/-- The archived profile on the dated ticket is the one read from this board's
issued matcher. The original incoming site is indexed at the first picked edge. -/
theorem SelectedBoard.dated_palette_party (seed Z : ℕ) (op : RotorSpec) (under : v.stage.z≤Z)
    (i : (dateRows).pairs) (party : Fin 6) :
    let u:=v.world.graph.src ((dateRows).pick (i,0))
    let donor:=chipDonor fmt (raw (hosts ((A).pos u).2) ((A).pos u).1)
      (finProdFinEquiv ((A).block u,seat_ (dateSeed i)))
    DescentOrdinaryPaletteBirth.word G seed Z op v.stage.z donor party=
      token G seed Z op (bornLabel (s:=seed) op (c:=v.choice) under i party) :=by
  have issued:=SelectedBoard.palette_party v oldFit R selected m parts B choiceEq seed Z op
  cases v with
  | mk dim worldBits gadget_ sched_ price_ rate_ eps_ k_ date_ z_ degree_ wire_ hist_ nz nd world_ prior_ he_ stage_ c n_ target_ link old_ reference_ bornBook_
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have chosenEq : selected = c := eq_of_heq choiceEq
    subst selected
    exact issued under i party

include choiceEq in
/-- Word-level read on the mounted register file. The caller supplies the original
packed material at this physical row; all encodings of its site, party, and
matched donor are evaluated here. -/
theorem SelectedBoard.native_palette_party (entry : ArgumentEntry v) (birth : entry.BirthShape v)
    (parts₀ : Fin entry.clip.venue.hosts→Fin entry.clip.venue.groups→DepotRAM.Parts entry.clip.venue.socket)
    (socket : entry.clip.venue.socket=fmt) (profileEq : entry.clip.venue.profile=v.profile)
    (slotsEq : entry.clip.venue.slots=(phys).materialFormat.slots)
    (blocks : v.bornBook.blocks=(fmt).blocks) (cap : v.bornBook.cap=(fmt).cap)
    (names : v.bornBook.names=(fmt).names) (widths : v.bornBook.widths=(fmt).widths)
    (seed Z : ℕ) (op : RotorSpec) (under : v.stage.z≤Z) (i : (dateRows).pairs) (party : Fin 6)
    (h : Fin v.bornBook.hosts) (g : Fin v.bornBook.groups)
    (mounted : let u:=v.world.graph.src ((dateRows).pick (i,0))
      HEq (parts₀ (h.cast birth.hosts) (g.cast birth.groups)) (B.material (hosts ((A).pos u).2) ((A).pos u).1)) :
    let u:=v.world.graph.src ((dateRows).pick (i,0))
    let xt:=finProdFinEquiv (((A).block u).cast blocks.symm,(seat_ (dateSeed i)).cast cap.symm)
    DescentOrdinaryPaletteBirth.word G seed Z op v.stage.z
      (chipDonor v.bornBook.format (entry.nativeChips v birth parts₀ h g) xt) party=
      token G seed Z op (bornLabel (s:=seed) op (c:=v.choice) under i party) :=by
  let u:=v.world.graph.src ((dateRows).pick (i,0))
  have read:=ArgumentEntry.native_chip_material v entry birth parts₀ h g fmt
    (B.material (hosts ((A).pos u).2) ((A).pos u).1) v.profile (phys).materialFormat.slots socket profileEq slotsEq mounted
  have eqn:=DescentOrdinaryPaletteBirth.word_of_chip G seed Z op v.stage.z v.bornBook fmt blocks cap names widths
    (entry.nativeChips v birth parts₀ h g) _ read (((A).block u).cast blocks.symm) ((seat_ (dateSeed i)).cast cap.symm) party
  exact eqn.trans (SelectedBoard.dated_palette_party v oldFit R selected m parts B choiceEq seed Z op under i party)

include choiceEq in
/-- Every padded host and seat is covered. An empty seat or a port without a
matched birth returns zero, and an occupied birth returns its actual party. -/
theorem SelectedBoard.palette_rows (h : Fin H) (g : Fin J) (x : Fin (2^v.k)) (t : Fin (A).cap)
    (seed Z : ℕ) (op : RotorSpec) (z : ℕ) (under : z≤Z) (party : Fin 6) :
    let address:=(h,finProdFinEquiv (finProdFinEquiv (g,x),t))
    let owners:=DescentRawCablePanel.oldSlot A S v.prior.valid native hosts grp
    let pair:=if hit : ∃q,owners q=address then DescentRawCablePanel.first (rr).pick hit.choose.val else none
    DescentOrdinaryPaletteBirth.word G seed Z op z (chipDonor fmt (raw h g) (finProdFinEquiv (x,t))) party=
      pair.elim 0 (fun i=>token G seed Z op (.inr (.inl (⟨z,Nat.lt_succ_of_le under⟩,(rr).profile selected i,party)))) :=by
  exact Stage.issued_palette_rows A native S v.prior.valid rank B.win v.nonnegative grp hosts B.live
    v.prior.valid.coordinates B.named B.small B.winning B.degree B.ordered v.profile B.topo B.matched B.width
    B.topology selected B.births B.issued R B.neighbors (A).hub same_ lay B.offspring (phys).materialFormat.slots bytes
    v.age h g x t seed Z op z under party

include choiceEq in
/-- The complete table against the original dated choice, including every
absent donor and every unused seat in a padded host. -/
theorem SelectedBoard.dated_palette_rows (h : Fin H) (g : Fin J) (x : Fin (2^v.k)) (t : Fin (A).cap)
    (seed Z : ℕ) (op : RotorSpec) (under : v.stage.z≤Z) (party : Fin 6) :
    let address:=(h,finProdFinEquiv (finProdFinEquiv (g,x),t))
    let owners:=DescentRawCablePanel.oldSlot A S v.prior.valid native hosts grp
    let pair:=if hit : ∃q,owners q=address then DescentRawCablePanel.first (dateRows).pick hit.choose.val else none
    DescentOrdinaryPaletteBirth.word G seed Z op v.stage.z (chipDonor fmt (raw h g) (finProdFinEquiv (x,t))) party=
      pair.elim 0 (fun i=>token G seed Z op (bornLabel (s:=seed) op (c:=v.choice) under i party)) :=by
  have issued:=SelectedBoard.palette_rows v oldFit R selected m parts B choiceEq h g x t seed Z op
  cases v with
  | mk dim worldBits gadget_ sched_ price_ rate_ eps_ k_ date_ z_ degree_ wire_ hist_ nz nd world_ prior_ he_ stage_ c n_ target_ link old_ reference_ bornBook_
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have chosenEq : selected = c := eq_of_heq choiceEq
    subst selected
    exact issued _ under party

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
