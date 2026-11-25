import OAI.Hierarchy.DescentReachedScalarReshape
import OAI.Hierarchy.DescentIssuedDonors

namespace OAI
/-! # The old rack and compact local ordinal of the actual successor host -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentKernelHistory DescentCompiler DescentStageEdgeReceipt DescentLocalArchiveOrder
open DescentHostDegree DescentHostDirectory DescentOrdinaryLocalBirth DescentNetworkPartition
open DescentCableDonorNames Computability.BorderVNP.Crossing DescentSharedCableNames
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target)
local notation "slots" => 2^(packExponent 20 cap.placement.degree)+2
local notation "pitch" => (2^(k+1)-1)*slots
local notation "padded" => 2^(k+1)*slots
variable {H : ℕ} (fit : Fintype.card cap.V≤H)

private theorem pitch_le : pitch≤padded := Nat.mul_le_mul_right _ (Nat.sub_le ..)

/-- The native mixed-radix row of the target, padded to the word-address fields of the parent filter. -/
def parentVenue : target.V↪Fin H×Fin padded :=
  let pair : target.V↪Fin (Fintype.card cap.V)×Fin pitch :=
    (target.vertex.trans (hostIndex ticket).toEmbedding).trans finProdFinEquiv.symm.toEmbedding
  pair.trans ((Fin.castLEEmb fit).prodMap (Fin.castLEEmb (pitch_le (k:=k) (cap:=cap))))

theorem parentVenue_ordinal (v : target.V) : (target.vertex v).val =
    (ticket.parentVenue fit v).1.val*pitch+(ticket.parentVenue fit v).2.val :=by
  let a:=hostIndex ticket (target.vertex v)
  let b : Fin (Fintype.card cap.V)×Fin pitch:=finProdFinEquiv.symm a
  have read:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply a)
  change (target.vertex v).val=b.1.val*pitch+b.2.val
  change (finProdFinEquiv b).val=(target.vertex v).val at read
  rw [finProdFinEquiv_apply_val] at read
  exact read.symm.trans ((Nat.add_comm _ _).trans
    (congrArg (fun t => t + b.2.val) (Nat.mul_comm _ _)))

theorem parentVenue_low (v : target.V) : (ticket.parentVenue fit v).2.val<pitch :=
  (finProdFinEquiv.symm (hostIndex ticket (target.vertex v))).2.isLt

theorem parentVenue_of_ordinal (v : target.V) (h : cap.V) (l : ℕ) (small : l<pitch)
    (atRow : (target.vertex v).val=(cap.vertex h).val*pitch+l) :
    (ticket.parentVenue fit v).1=(cap.vertex h).castLE fit ∧ (ticket.parentVenue fit v).2.val=l :=by
  let b : Fin (Fintype.card cap.V)×Fin pitch:=(cap.vertex h,⟨l,small⟩)
  have stored : hostIndex ticket (target.vertex v)=finProdFinEquiv b :=by
    apply Fin.ext
    rw [finProdFinEquiv_apply_val]
    change (target.vertex v).val = l + pitch * (cap.vertex h).val
    exact atRow.trans ((congrArg (fun t => t + l) (Nat.mul_comm _ _)).trans
      (Nat.add_comm _ _))
  have pair:=congrArg finProdFinEquiv.symm stored
  rw [Equiv.symm_apply_apply] at pair
  change ((finProdFinEquiv.symm (hostIndex ticket (target.vertex v))).1.castLE fit=_) ∧
    (finProdFinEquiv.symm (hostIndex ticket (target.vertex v))).2.val=_
  rw [pair]
  exact ⟨rfl,rfl⟩

local notation "rr" => BitDescription.scannedRows he T
local notation "layout" => bestLayout (branchWidth G (fun _ : (rr).pairs=>T.z) ((rr).profile c))
local notation "place" => GadgetNetwork.newSite W.graph (rr).pick (layout) (rr).pack

/-- The original row address of any raw endpoint, including endpoints with an empty recipe. -/
def rawParentKey (x : (rawGraph he T c).Site) :=
  let b:=activeChart ticket
  splitKey (mergeHub b.hub k (gainExponent 20 cap.placement.degree) (b.key he T c ((place) x)))

theorem rawParentKey_donor (x : (rawGraph he T c).Site) :
    ticket.rawParentKey x=splitKey (mergeHub ticket.donorHub T.k (gainExponent 20 T.Δ)
      (ticket.donorKey ((place) x))) :=by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  rfl

theorem parentVenue_raw_location (age : i<S.length) (radix : S.radix=2^k)
    (x : (rawGraph he T c).Site) :
    let key:=ticket.rawParentKey x
    let w:=n.destination (rawInput he T c ((rr).state c) x)
    let p:=ticket.parentVenue fit (target.placement.pos w).2
    ((target.placement.pos w).1,target.placement.block w)=S.groupDigits age radix key.1 ∧
      p.1=(cap.vertex key.2.1).castLE fit ∧ p.2.val=SiteDecode.localNumber k slots key.2 :=by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  obtain ⟨_,_,chart,positions,ordinal⟩:=ticket.venueRows
  let rc:=BitDescription.scannedRows he cap.placement.stage
  let b:=activeChart ticket
  have address:=positions (rc.state c) b x
  dsimp only at address ⊢
  refine ⟨address.1,ticket.parentVenue_of_ordinal fit _ _ _ ?_ ?_⟩
  · have legal:=(Classical.choose_spec (ticket.issued.common_chart he cap.placement.stage c (rc.state c))).1.1
    have merged:=merged_mem_keys b.hub k (gainExponent 20 cap.placement.degree) (2^(packExponent 20 cap.placement.degree)+2)
      (legal (GadgetNetwork.newSite W.graph rc.pick (bestLayout (branchWidth G (fun _ : rc.pairs=>cap.placement.stage.z) (rc.profile c))) rc.pack x))
    have keyValid : (ticket.rawParentKey x).2 ∈ keys k (2^(packExponent 20 cap.placement.degree)+2) :=
      Finset.mem_product.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp merged).2⟩
    simpa [DescentPackedChildNeighbor.lowDigit,SiteDecode.localNumber,packedNumber] using
      (DescentPackedChildNeighbor.lowDigit ⟨(ticket.rawParentKey x).2,keyValid⟩).isLt
  · rw [ordinal,address.2]
    simp [rawParentKey,SiteDecode.localNumber,packedNumber,Nat.add_mul,Nat.mul_assoc]; ring

/-- At every true site, both endpoints decode the key of the same original recipe node. -/
theorem parentVenue_location (arch : Archive W) (age : i<S.length) (radix : S.radix=2^k)
    (v : n.result.graph.Site) (x : ((ticket.advance arch).bit.recipe v).Node) :
    let key:=(splitKey (currentLabel ticket arch v x).val).2
    let pair:=ticket.parentVenue fit (target.placement.pos v).2
    pair.1=(cap.vertex key.1).castLE fit ∧ pair.2.val=SiteDecode.localNumber k slots key :=by
  have atRow:=(older_location ticket arch age radix v x).1
  change ((finProdFinEquiv.symm (hostIndex ticket (target.vertex (target.placement.pos v).2))).1.castLE fit = _) ∧
    (finProdFinEquiv.symm (hostIndex ticket (target.vertex (target.placement.pos v).2))).2.val=_
  rw [atRow]
  exact ⟨rfl,by simp [localIndex,DescentPackedChildNeighbor.lowDigit,SiteDecode.localNumber,packedNumber]⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
