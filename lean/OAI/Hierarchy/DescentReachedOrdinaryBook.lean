import OAI.Hierarchy.DescentIssuedCommonChart
import OAI.Hierarchy.DescentOrdinaryRosterEquiv

namespace OAI
/-! # The true native local scalar book of an ordinary successor -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames
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
local notation "M" => ticket.issued.common_chart he T c ((r).state c)

def activeChart : IssuedDonorChart he T capV := Classical.choose M
local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun v : (sel).graph.Site=>(by simp : ‖x₁ v‖≤1)
local notation "ok₂" => fun v : C=>(by simp : ‖x₂ v‖≤1)
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "first" => quotientBits stepGraph group x₁ ok₁ base
local notation "second" => quotientBits (quotient stepGraph group x₁ ok₁) addr x₂ ok₂ first
local notation "rawSite" => rawNodeSite (he:=he) (T:=T) (c:=c) arch

def currentLabel (v : n.result.graph.Site) (x : ((next).recipe v).Node) : C := venue (rawSite ((roots ticket arch) ⟨v,x⟩))

theorem current_members (v : n.result.graph.Site) (x : ((next).recipe v).Node)
    (s : NodeOrder.All arch.bit ⊕ (r).pairs×Fin 6) :
    owner (n:=n) arch s=v ↔ venue (rawSite s)=currentLabel ticket arch v x := by
  let w := roots ticket arch ⟨v,x⟩
  have atSite : owner (n:=n) arch w=v := roots_owner ticket arch ⟨v,x⟩
  calc
    _ ↔ owner (n:=n) arch s = owner (n:=n) arch w := ⟨fun h=>h.trans atSite.symm, fun h=>h.trans atSite⟩
    _ ↔ _ := by
      have same := (Classical.choose_spec M).1.2 (rawSite s) (rawSite w)
      exact ⟨fun h => Subtype.ext (same.mp h), fun h => same.mpr (congrArg Subtype.val h)⟩

def printed (v : n.result.graph.Site) (x : ((next).recipe v).Node) :
    ((next).recipe v).Node ≃ (second (currentLabel ticket arch v x)).Node :=
  ((fiber ticket arch v).trans ((Equiv.refl _).subtypeEquiv (fun s => by
      cases s with
      | inl z => exact current_members ticket arch v x (.inl z)
      | inr z => exact current_members ticket arch v x (.inr z)))).trans
    (coefficientFiber arch.bit (r).pick units stageLimit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ _).symm

theorem printed_origin (v : n.result.graph.Site) (x y : ((next).recipe v).Node) :
    (coefficientFiber arch.bit (r).pick units stageLimit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ _
      (printed ticket arch v x y)).val=roots ticket arch ⟨v,y⟩ := by
  simp [printed,fiber]
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "sites" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "used" => fun j : (r).pairs=>(r).picked (j,0)
theorem actual_ordinal {D₁ K : ℕ} (halo : Halo C W.graph.Site D₁)
    (oldHome : ∀v : W.graph.Site,v∈halo.member (venue (.inl v)))
    (birthHome : ∀j role,W.graph.src ((r).pick (j,0))∈halo.member (venue (.inr (j,role))))
    (prior : Local arch.bit) (oldRank : ∀v,(arch.bit.recipe v).Node ↪ Fin K)
    (ordered : ∀c (x y : ↥(halo.member c)),halo.slot c x<halo.slot c y ↔ sites x.val<sites y.val)
    (oldRead : ∀v x,(oldRank v x).val=(prior v x).val)

    (v : n.result.graph.Site) (x : ((next).recipe v).Node) :
    (compact cap.placement native S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr
      x₁ x₂ ok₁ ok₂ halo oldHome birthHome oldRank (currentLabel ticket arch v x) (printed ticket arch v x x)).val=(advance ticket arch prior v x).val := by
  let label := currentLabel ticket arch v x
  let equiv := printed ticket arch v x
  let src:=fun y : ((next).recipe v).Node=>roots ticket arch ⟨v,y⟩
  let out:=fun y : (second label).Node=>
    origin arch.bit (r).pick units stageLimit ((r).profile c) group addr label
      (roster arch.bit (r).pick units stageLimit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ label y)
  have read (y : ((next).recipe v).Node) : out (printed ticket arch v x y)=src y :=
    (coefficientFiber_read arch.bit (r).pick units stageLimit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ label (equiv y)).symm.trans
      (printed_origin ticket arch v x y)
  have compactRank := compact_source_read cap.placement native S cap.valid arch.bit (r).pick units stageLimit
    ((r).profile c) used group addr x₁ x₂ ok₁ ok₂ halo oldHome birthHome oldRank sites prior ordered oldRead
    label (equiv x)
  have compare := equal_prefix equiv src out
    (donorKey cap.placement native S cap.valid arch.bit prior (r).pick used sites) read x
  exact compactRank.trans (compare.symm.trans (advance_read ticket arch prior v x).symm)

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
