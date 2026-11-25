import OAI.Hierarchy.DescentIssuedChartAgreement
import OAI.Hierarchy.DescentReachedPrivateBasis
import OAI.Hierarchy.DescentReachedAtomHalo

namespace OAI
/-! Every surviving scalar reads its true originating site in the same physical donor raster as the private-word decoder. -/
namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition DescentOrdinaryDonorHalo
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "next" => (ticket.advance arch).bit
local notation "raw" => rawNodeSite (he:=he) (T:=T) (c:=c) arch
local notation "group" => GadgetNetwork.newSite W.graph (r).pick
  (bestLayout (branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c))) (r).pack
local notation "chart" => privateChart ticket arch hp one pin sh unit
local notation "book" => privateBooks ticket arch hp one pin sh unit
local notation "privateHalo" => chartHalo (cap:=cap) (c:=c) chart

theorem pointer_site (v:n.result.graph.Site) (j:((next).recipe v).Node) :
    ((book).home v).val=(currentLabel ticket arch v j).val := by
  let source:=roots ticket arch ⟨v,j⟩
  have ownerRead : n.destination (rawInput he T c ((r).state c) (raw source))=v :=
    roots_owner ticket arch ⟨v,j⟩
  have actual:=private_site ticket arch hp one pin sh unit (raw source)
  rw [ownerRead] at actual
  exact (congrArg Subtype.val actual).trans
    (IssuedDonorChart.same_address he T c chart (activeChart ticket) T.k (gainExponent 20 T.Δ)
      (group (raw source)))

theorem pointer_member (v:n.result.graph.Site) (j:((next).recipe v).Node) (x:W.graph.Site) :
    x∈(privateHalo).member ((book).home v) ↔ x∈(reachedHalo ticket).member (currentLabel ticket arch v j) := by
  change x∈siteSet _ _ ((book).home v).val ↔ x∈siteSet _ _ (currentLabel ticket arch v j).val
  rw [pointer_site ticket arch hp one pin sh unit v j]

theorem pointer_slot (v:n.result.graph.Site) (j:((next).recipe v).Node) (x:W.graph.Site)
    (mem:x∈(privateHalo).member ((book).home v)) :
    (privateHalo).slot ((book).home v) ⟨x,mem⟩=
      (reachedHalo ticket).slot (currentLabel ticket arch v j) ⟨x,(pointer_member ticket arch hp one pin sh unit v j x).mp mem⟩ := by
  let A:=cap.placement
  let ras:=raster (groupedNear A.near) A.pos A.block cap.valid.coordinates A.degree
    A.stage.degree (rackName (cap:=cap))
  have congruent : ∀(l t : _) (h : l=t) (u : x∈siteSet (groupedNear A.near) A.pos l)
      (s : x∈siteSet (groupedNear A.near) A.pos t),ras.slot l ⟨x,u⟩=ras.slot t ⟨x,s⟩ := by
    rintro l _ rfl _ _
    rfl
  exact congruent _ _ (pointer_site ticket arch hp one pin sh unit v j) _ _

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
