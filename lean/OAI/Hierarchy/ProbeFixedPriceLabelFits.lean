import OAI.Hierarchy.ProtocolRAMStripTreeFinalFits
import OAI.Hierarchy.ProbeFixedDiagnosticOriginal
import OAI.Hierarchy.ProbeFixedOriginalSocketBounds
import OAI.Hierarchy.ProbeFixedPaidEconomicRows

namespace OAI
/-! # Source bounds for the actual attempt's archived length label -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe CoreBoard PurchaseFrozen BoughtSockets
open CatalogueRows StripDirectory StripChart PortPadding StockCommit
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "s" => v.located (v.seed P z width) P width
local notation "B" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "T" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "W" => wordBits z (2^v.W) copies
local notation "bs" => withPorts s v.mesh P.catalogue P.routes
local notation "N" => Stages z (2^v.W)
local notation "keys" => P.routes.directory.keysBase

private theorem native_header_bound (a : Attempt) : (StripChart.header F B a).stop≤(A).first :=
  (congrArg PortHeader.stop (shape_header F B v.mesh A P.joint.initial a).1).symm.le.trans
    (v.stock_occurrence_end P z width a)

private theorem header_stop_mono (early late : PortHeader) (start : early.start≤late.start)
    (count : early.count=late.count) : early.stop≤late.stop := by
  change early.start+2*ProtocolRAMPurchaseSampler.span early.count+
      ProtocolRAMPurchaseSampler.span (2*early.count)+ProtocolRAMPurchaseSampler.span (2*early.count) ≤
    late.start+2*ProtocolRAMPurchaseSampler.span late.count+
      ProtocolRAMPurchaseSampler.span (2*late.count)+ProtocolRAMPurchaseSampler.span (2*late.count)
  rw [count]
  omega

theorem chronological_header_bound (a : Attempt) :
    (StripChart.header F bs a).stop≤(A).first := by
  have start : (StripChart.header F bs a).start=0 := by cases a <;> rfl
  have count : (StripChart.header F bs a).count=(StripChart.header F B a).count := by
    cases a <;> rfl
  exact (header_stop_mono _ (StripChart.header F B a) (start.le.trans (Nat.zero_le _)) count).trans
    (native_header_bound v P z width a)

private theorem retained_fits {letters : ℕ} (chartBoards : Boards z (2^v.W) k letters v.depth)
    (a : Attempt) (limit : ℕ) (word : limit<2^W) (cut : (A).base v.mesh (.attempt a)≤limit)
    (head : (StripChart.header F chartBoards a).stop≤(A).first)
    (priced : ∀p t,(StripChart.build F chartBoards (.outer p t) 0).pricedArea.stop≤
      (A).base v.mesh (.attempt (.outer p t))+(A).stride) :
    (retainedAt F chartBoards a).Fits W limit := by
  have low : (A).first≤limit:=(Nat.le_add_right ..).trans cut
  have hdr:=(StripChart.header F chartBoards a).input_ends (head.trans low)
  have ball:=(StripChart.header F chartBoards a).ballTerm.fits_of_inputEnd hdr.1 word
  cases a with
  | outer p t => trivial
  | inner p t j u =>
    let parent:=Attempt.outer p t
    let kid:=Attempt.inner p t j u
    have ord : position v.mesh (.attempt parent)+1≤position v.mesh (.attempt kid) := by
      change trialBase v.mesh p t+1≤trialBase v.mesh p t+1+j*sliceSize v.mesh+u
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    have prior := Nat.add_le_add_left (Nat.mul_le_mul_right (A).stride ord) (A).first
    rw [Nat.add_mul,Nat.one_mul,← Nat.add_assoc] at prior
    let src:=StripChart.build F chartBoards parent 0
    have span:= (src.paddedSocketColumns.1.trans (priced p t)).trans (prior.trans cut)
    change (Expr.lookup ⟨src.board.purchaseOut,ProtocolRAMPurchaseSampler.bits src.market.rows⟩
      (StripChart.header F chartBoards kid).ballTerm).Fits W limit
    exact ⟨⟨Nat.two_pow_pos _,((Nat.le_add_left _ _).trans span).trans_lt word,span⟩,ball⟩

theorem chronological_keep (a : Attempt) (limit : ℕ) (word : limit<2^W)
    (cut : (A).base v.mesh (.attempt a)≤limit) : (retainedAt F bs a).Fits W limit := by
  apply retained_fits v P z width bs a limit word cut (v.chronological_header_bound P z width a)
  intro phase trial
  let ev:=Attempt.outer phase trial
  have same:=capacity F s ev 0 (resolvedStock v.mesh A P.joint.initial (StripChart.build F s) ev)
  exact (congrArg Area.stop same).le.trans
    (Slab.fit (v.slab (v.seed P z width) P width) (v.sized (v.seed P z width) width) F v.mesh P.joint.initial ev)

theorem chronological_ports (a : Attempt) (limit : ℕ) (word : limit<2^W)
    (cut : (A).base v.mesh (.attempt a)≤limit)
    (core : P.routes.core+CoreLookup.words v.sampler z (2^v.W) k≤limit)
    (cols : P.routes.column+ColumnROM.words z (2^v.W) k≤limit)
    (atlas : ColumnROM.Cover z v.W P.routes.directory.remapBase P.routes.directory.sitesBase P.routes.directory.superBase
      P.routes.oldGroups P.routes.bins P.routes.height limit)
    (head : (stratumHeader z (2^v.W) k v.sampler.degree v.depth keys).stop≤limit) :
    DatePortFits s v.mesh P.catalogue P.routes W limit a := by
  have sampler : (s).sampler=v.sampler := rfl
  cases a with
  | outer p t =>
    intro r
    have fits:=payload_fits_local P.catalogue P.routes.directory v.sampler P.routes.core P.routes.column v.depth
      P.routes.oldGroups P.routes.bins P.routes.height word core cols atlas ((Fintype.equivFin _) r)
    unfold payloadPortsAt
    rw [sampler]
    simpa only [payloadEdge,Equiv.symm_apply_apply] using fits
  | inner p t j u =>
    let sh:=((s).outer p t).market.shelf
    have area:=(v.catalyst_bought_bank_room P z width p t j u).1
    have bound (i : Key z (2^v.W) k) : (sh.L v.sampler v.depth i).endAddress≤limit := by
      let bank:=flagBank sh v.sampler z (2^v.W) k v.depth
      have block : (sh.L v.sampler v.depth i).endAddress≤bank.base :=
        (sh.end_le v.sampler v.depth i Nat.one_le_two_pow).trans
          ((sh.final_after v.sampler v.depth i).trans (Nat.le_add_right ..))
      exact block.trans ((Nat.le_add_right ..).trans (area.trans cut))
    intro r
    have fits:=purchase_fits_local P.catalogue P.routes.directory sh (birth v.mesh p t) v.sampler P.routes.core
      P.routes.column v.depth P.routes.oldGroups P.routes.bins P.routes.height word core cols atlas head bound
      ((Fintype.equivFin _) r)
    have key : (s).stratumHeader p t = keys := rfl
    unfold boughtPortsAt
    rw [sampler,key]
    simpa only [purchaseEdge,Equiv.symm_apply_apply] using fits

theorem native_price_role (a : Attempt) (limit : ℕ) (word : limit<2^W)
    (cut : (A).base v.mesh (.attempt a)≤limit) :
    (StripChart.header F B a).fieldTerm.Fits W limit :=
  (StripChart.header F B a).fieldTerm.fits_of_inputEnd
    ((StripChart.header F B a).input_ends ((native_header_bound v P z width a).trans
      ((Nat.le_add_right ..).trans cut))).2.1 word

theorem native_price_tags (a : Attempt) (limit : ℕ) (word : limit<2^W)
    (cut : (A).base v.mesh (.attempt a)≤limit)
    (ports : DatePortFits s v.mesh P.catalogue P.routes W limit a) :
    ∀i,(StripChart.id F B P.catalogue a i).Fits W limit := by
  have head:=native_header_bound v P z width a
  have low : (A).first≤limit:=(Nat.le_add_right ..).trans cut
  have ball:=(StripChart.header F B a).ballTerm.fits_of_inputEnd
    ((StripChart.header F B a).input_ends (head.trans low)).1 word
  have keep := retained_fits v P z width B a limit word cut head (fun phase trial=>by
    let ev:=Attempt.outer phase trial
    have same:=capacity F B ev 0 (resolvedStock v.mesh A P.joint.initial (StripChart.build F B) ev)
    exact (congrArg Area.stop same).le.trans (v.attempt_room P z width ev))
  intro i
  have source : (rawEdge B P.catalogue.rows a i).Fits W limit := by
    have padded {n d : ℕ} (term : Fin n → Expr) (bounded : ∀j,(term j).Fits W limit)
        (slot : Fin d) : (extend term (.lit P.catalogue.rows) slot).Fits W limit := by
      unfold extend
      split
      · exact bounded _
      · trivial
    cases a with
    | outer p t =>
      change (extend (payloadEdge (payloadPortsAt s v.mesh P.routes) P.catalogue) (.lit P.catalogue.rows) i).Fits W limit
      exact padded _ (fun j=>ports ((Fintype.equivFin (PayloadRole N k)).symm j)) i
    | inner p t j u =>
      change (extend (purchaseEdge (boughtPortsAt s v.mesh P.catalogue P.routes p t) P.catalogue) (.lit P.catalogue.rows) i).Fits W limit
      exact padded _ (fun h=>ports ((Fintype.equivFin (PurchasedRole v.depth k)).symm h)) i
  have hit:=fits_atRow _ _ source ball
  exact ⟨trivial,hit,trivial,hit,hit,trivial,⟨keep,trivial,trivial,hit⟩,trivial⟩

theorem price_label_fits {K G H R idBase : ℕ} (joint : JointHeader.Board)
    (origin : Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank) (a : Attempt) :
    let dir:=Public.join origin v.sampler z v.W k v.depth K G H R
    let b:=liveBoard dir v.sampler z v.W k v.depth R K G H (CoreCatalogue.pointBits z v.W) idBase
    let P':=v.catalystPlacement z K G H R joint b origin
    let g:=v.stamp P' z width r banks src tab dst owners a
    CoreRoute.stop v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel) v.depth K G H R≤joint.initial →
      g.out<2^W → ((g.geometry 5).atRow g.edge).Fits W g.out := by
  intro dir b P' g alloc word
  let A':=v.privateArena P' z width
  have cut : A'.base v.mesh (.attempt a)≤g.out:=v.stock_label P' z width a
  have low : A'.first≤g.out:=(Nat.le_add_right ..).trans cut
  have top:=alloc.trans ((v.catalyst_initial_le_first P' z width).trans low)
  obtain ⟨core,indices,columns,atlas,keysBound⟩:=v.diagnostic_original z K G H R idBase origin g.out top word
  have base:=v.chronological_ports P' z width a g.out word cut indices columns atlas keysBound
  have tags:=v.native_price_tags P' z width a g.out word cut base
  have role:=v.native_price_role P' z width a g.out word cut
  have ordinal : g.edge.Fits W g.out:=⟨choose_fits_bound _ _ _ _ tags role,trivial⟩
  have fee : (g.geometry 5).Fits W g.out:=b.select_fits _ _ core.2.2.2.1 trivial
  exact fits_atRow _ _ fee ordinal

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
