import OAI.Hierarchy.ProbeFixedUniformPurchaseField
import OAI.Hierarchy.ProbeFixedPaidOperandWork

namespace OAI
/-! # Instruction work of both dated link headers on the actual wide chart -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open ReportSockets StripChart StripDirectory CatalogueRows BoughtSockets
open PostResources
open scoped Classical
open private primaryWork wide_primary_work from OAI.Hierarchy.ProbeFixedPaidOperandWork
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private theorem diagnostic_link_work (b : CatalogueRows.Board) (x : Expr) (base c e : ℕ)
    (core : b.core.All (fun t=>t.work≤c)) (edge : x.work≤e) :
    LinkCaps (diagnosticLink b x base) (4*(c*(e+1))+1) := by
  obtain ⟨group,left,right,length,_⟩:=core
  have replace (t : Expr) (ht : t.work≤c) : (t.atRow x).work≤c*(e+1) :=
    (substitute_work t x).trans (Nat.mul_le_mul ht (Nat.add_le_add_right edge 1))
  have l:=replace _ left
  have r:=replace _ right
  refine ⟨(replace _ group).trans (by omega),?_,?_,(replace _ length).trans (by omega)⟩
  · change _+_+_+_+1≤_
    omega
  · change _+_+_+_+1≤_
    omega

private def coreWordWork : ℕ := 246+26*ReportSockets.copies k v.wideJobs

private theorem core_work (h width : ℕ) :
    (v.widePlacement h width).catalogue.core.All (fun e=>e.work≤v.coreWordWork) := by
  let K:=WideMemory.K h v.W
  let H:=WideMemory.H h v.W k v.wideJobs
  let G:=(WideMemory.dir h v.W k v.wideJobs).groups
  let R:=WideMemory.R v.sampler h v.W k
  let c:=CoreCatalogue.sourceAt h v.W k v.wideJobs R K G H (CoreCatalogue.pointBits h v.W)
  have total : c.group.work+c.left.work+c.right.work+c.lengthCode.work+c.menu.work=v.coreWordWork :=
    CoreCatalogue.source_work ..
  change c.group.work≤_ ∧ c.left.work≤_ ∧ c.right.work≤_ ∧ c.lengthCode.work≤_ ∧ c.menu.work≤_
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

local notation "P" h:arg width:arg => v.widePlacement h width
set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
private theorem regular_work (h width r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank) (a : Attempt) :
    LinkCaps (repair (v.nativeChart (P h width) h width r banks src tab dst owners) a).link
      (4*(v.coreWordWork*(primaryWork v+1))+1) := by
  let b:=(P h width).catalogue
  let g:=(P h width).routes
  let s:=v.located (v.seed (P h width) h width) (P h width) width
  let N:=Stages h (2^v.W)
  have wc:=v.core_work h width
  have wp := wide_primary_work v h width a
  cases a with
  | outer phase trial =>
    let role : PayloadRole N k:=.catalyst (PayloadStrip.first N 0) ⟨0,s.positive⟩
    apply diagnostic_link_work b _ _ _ _ wc
    change ((payloadPortsAt s v.mesh g).primary b ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))).work≤_
    rw [Equiv.symm_apply_apply]
    exact wp role
  | inner phase trial j tick =>
    let role : PurchasedRole v.depth k:=.catalyst (ChainStrip.inlet v.depth 0) ⟨0,s.positive⟩
    apply diagnostic_link_work b _ _ _ _ wc
    change ((boughtPortsAt s v.mesh b g phase trial).primary b
      ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))).work≤_
    rw [Equiv.symm_apply_apply]
    exact wp role

private theorem widen {l : Link} {U K : ℕ} (h : LinkCaps l U) (hK : U≤K) :
    LinkCaps l K := ⟨h.group.trans hK,h.endpoint.trans hK,h.opposite.trans hK,h.length.trans hK⟩

/-- The bound is independent of all dates, settlement banks, height and width. -/
theorem wide_post_links : ∃U : ℕ,∀h width r (banks : RouteSettlement.Banks) src tab dst
    (owners : Bank) (a : Attempt),
    let C:=v.nativeChart (P h width) h width r banks src tab dst owners
    let B:=repair C a
    LinkCaps B.link U ∧ LinkCaps B.purchaseLink U ∧ B.purchaseMenu.work≤U := by
  obtain ⟨u,purchases⟩:=v.wide_purchase_field_work
  let c:=4*(v.coreWordWork*(primaryWork v+1))+1
  refine ⟨max c u,?_⟩
  intro h width r banks src tab dst owners a
  have regular:=v.regular_work h width r banks src tab dst owners a
  obtain ⟨bought,menu⟩:=purchases h width a
  exact ⟨widen regular (le_max_left ..),widen bought (le_max_right ..),menu.trans (le_max_right ..)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
