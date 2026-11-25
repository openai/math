import OAI.Hierarchy.DescentReachedScalarDonor
import OAI.Hierarchy.DescentScalarBookReshape
import OAI.Hierarchy.DescentReachedActorLocation
import OAI.Hierarchy.DescentPackedChildNeighborIssued

namespace OAI
/-! # A reached vertex reads its actual compacted donor book after regrouping -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames
open DescentSIMDLookup DescentScalarBookReshape Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
/-- The actual native output row uses exactly the group, block and full host
address carried by the winner's two merged venue coordinates. -/
local notation "oldH" => Fintype.card cap.V
local notation "oldG" => S.groupCount i
local notation "newG" => S.groupCount (i+1)
local notation "H'" => Fintype.card target.V
local notation "step" => 2^k
local notation "slots" => 2^(packExponent 20 cap.placement.degree)+2
local notation "pitch" => (2^(k+1)-1)*slots
variable (age : i<S.length) (radix : S.radix=2^k)
local notation "digits" => S.groupDigits age radix

include ticket in
private theorem host_count : H'=oldH*pitch :=by rw [ticket.hostCount];ring

def hostIndex : Fin H'≃Fin (oldH*pitch) :=finCongr (host_count ticket)

def oldInput {b : ℕ} (values : Fin pitch→Fin oldH→Fin oldG→Cell b) (l : Fin pitch) (h : Fin oldH) (g : Fin (newG*step)) :=
  values l h ((digits).symm (finProdFinEquiv.symm g))

variable (v : n.result.graph.Site) (x : ((ticket.advance arch).bit.recipe v).Node)
set_option quotPrecheck false
local notation "venue_" => currentLabel ticket arch v x
local notation "key" => (splitKey (venue_).val).2
local notation "priorGroup" => (splitKey (venue_).val).1
local notation "pos" => target.placement.pos v
local notation "bl" => target.placement.block v

theorem venue_valid : key∈keys k slots :=by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  have mem := (currentLabel ticket arch v x).property
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp mem
  have legal := (Classical.choose_spec (ticket.issued.common_chart he cap.placement.stage c
    ((BitDescription.scannedRows he cap.placement.stage).state c))).1.1 a
  have actual : (currentLabel ticket arch v x).val ∈ keys k slots := by
    rw [← ha]
    exact merged_mem_keys _ _ _ _ legal
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp actual).2⟩

def localIndex : Fin pitch:=DescentPackedChildNeighbor.lowDigit (⟨key,venue_valid ticket arch v x⟩ : ↥(keys k slots))

theorem older_location :
    finProdFinEquiv.symm (hostIndex ticket (target.vertex (pos).2))=(cap.vertex (key).1,localIndex ticket arch v x) ∧
    (digits).symm ((pos).1,bl)=priorGroup :=by
  have loc:=reached_location ticket arch age radix v x
  refine ⟨?_,(digits).symm_apply_eq.mpr loc.1⟩
  apply finProdFinEquiv.symm_apply_eq.mpr
  apply Fin.ext
  change (target.vertex (pos).2).val=_
  rw [loc.2,finProdFinEquiv_apply_val]
  change ((cap.vertex (key).1).val*(2^(k+1)-1)+nodeNumber (key).2.1.1 (key).2.1.2)*slots+(key).2.2 =
    (nodeNumber (key).2.1.1 (key).2.1.2*slots+(key).2.2)+pitch*(cap.vertex (key).1).val
  ring

theorem selected_book {b : ℕ} (f : Fin pitch→Fin oldH→Fin oldG→Cell b) :
    DescentScalarBookReshape.book (oldInput age radix f) bl (hostIndex ticket (target.vertex (pos).2)) (pos).1=
      f (localIndex ticket arch v x) (cap.vertex (key).1) priorGroup :=by
  obtain ⟨where_,batch_⟩:=older_location ticket arch age radix v x
  simp only [DescentScalarBookReshape.book,oldInput,where_,Equiv.symm_apply_apply,batch_]

/-- Addresses under the host-cardinality equality are numerical identities,
so the global reshape supplies precisely the per-block raster for `printed_field`. -/
theorem transferred {M w b : ℕ} (f : Fin pitch→Fin oldH→Fin oldG→Cell b) (out : ℕ) (mem : Memory w)
    (read : ∀j(p : Row (oldH*pitch) newG M),mem (dest oldH pitch newG M out j+(row (oldH*pitch) newG M p).val)=((data (DescentScalarBookReshape.book (oldInput age radix f) j) p).val:Computability.VPVNP.BurstRAM.Word w)) :
    ∀j(p : Row H' newG M),mem (dest oldH pitch newG M out j+(row H' newG M p).val)=
      ((data (fun h g=>DescentScalarBookReshape.book (oldInput age radix f) j (hostIndex ticket h) g) p).val:Computability.VPVNP.BurstRAM.Word w) :=by
  intro j p
  let a:Row (oldH*pitch) newG M:=(hostIndex ticket p.1,p.2)
  have same:(row H' newG M p).val=(row (oldH*pitch) newG M a).val:=by simp [row,a,hostIndex,finProdFinEquiv_apply_val]
  rw [same,read];rfl

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
