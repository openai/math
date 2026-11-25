import OAI.Hierarchy.DescentDatedSignedSelectedBoard
import OAI.Hierarchy.DescentActualPublicOperand

namespace OAI
/-! Pointwise public pointer at the authentic registered ordinary source and its retained W. -/
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
set_option hygiene false
set_option pp.maxSteps 300
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
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

open DescentHaloPackedRebase DescentSharedCableNames
variable (B:v.SelectedBoard oldFit R selected m parts)
variable (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ v.withIssuedSigned.signed.hosts)
variable (age:v.age<v.schedule.length) (radix:v.schedule.radix=2^v.k)
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
local notation "host" => v.target.vertex.trans (Fin.castLEEmb wide)
local notation "chart" => v.issuedSignedChart
local notation "pitch" => (phys).materialPitch
local notation "paths" => (ss).reach
local notation "space" => v.signedLayout.field_room.1
local notation "oldStates" => B.material

private theorem board_capacity {degree_ sites_ newTickets oldTickets leaves_ width_ : ℕ} (eqn : oldTickets = newTickets)
    (paid : Fused.capacity degree_ sites_ oldTickets leaves_ ≤ 2^width_) : Fused.capacity degree_ sites_ newTickets leaves_ ≤ 2^width_ := eqn ▸ paid

private theorem board_path_width : paths<2^(ss).fieldBits :=by
  change breadth D<2^(ss).fieldBits
  have cap : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  unfold Fused.capacity at cap
  omega

private theorem board_ticket_width : (ss).tickets≤2^(ss).fieldBits := v.signedLayout.field_room.2.2.2.1

private theorem board_ticket_count : (ss).tickets=(paths+1)*DepotRAM.Material.roles fmt :=
  congrArg (fun x=>(paths+1)*x) (chart).seats
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
open DescentBundleHistory DescentPackedOperand DescentOperandStateBanks Computability.BorderVNP.Crossing
local notation "info" => v.selectedModelPresentation oldFit R selected m parts B choiceEq wide age radix reciprocal
local notation "mod₀" => (info).model
local notation "world₁" => ((mod₀).named v.nonnegative T selected v.prior.order).result
variable {p kinds : ℕ} (arch : Archive v.world) (hp : 0<p) (one : 1≤kinds) (pin : ∀x,p∣v.bits x)
    (sh : WorldShape p kinds arch.bit) (stageDiv : p∣(T).z)
local notation "Use" => OrdinaryModel.PublicUse v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh stageDiv
local notation "node" => OrdinaryModel.PublicNode v.nonnegative T selected v.prior.order mod₀ arch
local notation "slotIndex" => OrdinaryModel.PublicArg v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh stageDiv
local notation "observed" => OrdinaryModel.publicOperand v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh stageDiv

/-- The actual matched path and donor role in the selected board, with its
registered successor receiver, group and core mark. -/
def selectedLocator (use : OrdinaryModel.PublicUse v.nonnegative (v.prior.placement.stage) selected
    v.prior.order (info).model arch hp one pin sh stageDiv) (side : Bool) : Option SignedDrawing.Slot :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap ≤ 2^(ss).fieldBits := space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wireSpace hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload socketUnit profile seats =>
    have sourceRateEq := link.sourceRate
    rcases sourceRateEq with rfl
    have stageEq := eq_of_heq link.placement
    rcases stageEq with rfl
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof:=picked.choose_spec
    let normalized:=selectedProof.2.2
    let drawing:=OrdinaryLink.actualModelDrawing link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (board_capacity ids capacity)
    exact drawing.locate (use.parent _ _ _ prior.order model arch hp one pin sh stageDiv) side

local notation "whereAt" => v.selectedLocator oldFit R selected m parts B choiceEq wide age radix reciprocal arch hp one pin sh stageDiv

private def cableRoomTests (cap degree fieldBits : ℕ) (result : ℕ → Prop) : Prop :=
  ∀ {wordBits : ℕ} (_wireFit : cap ≤ 2^fieldBits) (_peerFit : degree ≤ 2^fieldBits)
    (_wireWide : cap ≤ 2^(wordBits+2)) (_peerWide : degree ≤ 2^(wordBits+2)), result wordBits

open Lean Meta Elab Term in
local elab "registeredCableLaw% " origin:term:max result:term:max cap:term:max degree:term:max fieldBits:term:max : term => do
  let receipt ← instantiateMVars (← elabTerm origin none)
  let answer ← instantiateMVars (← elabTerm result none)
  let capTerm ← elabTermEnsuringType cap (mkConst ``Nat)
  let degreeTerm ← elabTermEnsuringType degree (mkConst ``Nat)
  let widthTerm ← elabTermEnsuringType fieldBits (mkConst ``Nat)
  let source ← inferType receipt
  withTransparency .default <| forallBoundedTelescope source (some 6) fun xs _ => do
    unless xs.size == 6 do throwError "expected the six parameters of the public cable-origin law"
    let resultAt := mkAppN answer (xs.extract 0 5)
    let rooms := mkAppN (mkConst ``cableRoomTests) #[capTerm, degreeTerm, widthTerm, resultAt]
    let binders ← mkForallFVars xs rooms
    let rec coordinate (names : List Name) (e : Lean.Expr) : Lean.Expr :=
      match names, e with
      | n :: rest, .forallE _ ty body bi => .forallE n ty (coordinate rest body) bi
      | _, body => body
    return coordinate [`x, `j, `edge, `lo, `fit, `hit] binders


section
variable (presented : ModelPresentation v selected)
set_option hygiene false in
local notation "abstractUse" => OrdinaryModel.PublicUse v.nonnegative (v.prior.placement.stage) selected v.prior.order presented.model arch hp one pin sh stageDiv
set_option hygiene false in
local notation "abstractNode" => OrdinaryModel.PublicNode v.nonnegative (v.prior.placement.stage) selected v.prior.order presented.model arch
set_option hygiene false in
local notation "abstractArg" => OrdinaryModel.PublicArg v.nonnegative (v.prior.placement.stage) selected v.prior.order presented.model arch hp one pin sh stageDiv
set_option hygiene false in
local notation "abstractWorld" => (presented.model.named v.nonnegative (v.prior.placement.stage) selected v.prior.order).result
private abbrev selectedCableResult (lookup : abstractUse → Bool → Option SignedDrawing.Slot)
    (x : abstractNode) (j : abstractArg x) (edge : Incident (abstractWorld).graph x.1) (lo : ℕ)
    (fit : (lo+1)*p≤(abstractWorld).graph.width edge.val) (wordBits : ℕ) : Prop :=
    ∃use : abstractUse,use.node=x ∧ HEq use.arg j ∧ ∀bitsIn cut : Cell (wordBits+2),bitsIn.val=use.chunk→cut.val=(T).z/p→
      ∃entry : SignedDrawing.Slot,lookup use (decide ((abstractWorld).graph.src edge.val≠x.1))=some entry ∧
      let field:=presented.numbers entry.block entry.role entry.host entry.group
      Pointer.ofKey 0 (resolve (Public.fragment entry.marked field.1 field.2 bitsIn cut))=
        v.target.firstCable hp (Reached.originalSite presented.same x.1) (Reached.originalIncident presented.same x.1 edge)
          lo (Reached.original_fit presented.same x.1 edge lo fit)

private def SelectedFirstCableLaw (lookup : abstractUse → Bool → Option SignedDrawing.Slot) : Prop :=
  registeredCableLaw%
    (OrdinaryModel.public_origin v.nonnegative (v.prior.placement.stage) selected v.prior.order
      presented.model arch hp one pin sh stageDiv)
    (@selectedCableResult F P _ v selected p kinds arch hp one pin sh stageDiv presented lookup)
    (v.target.placement.cap) (v.target.placement.degree) (v.withIssuedSigned.signed.fieldBits)

end

section
attribute [local irreducible] selectedModelPresentation selectedLocator
private abbrev selected_lookup_on_physical_presentation :
    OrdinaryModel.PublicUse v.nonnegative v.prior.placement.stage selected v.prior.order
      (v.selectedModelPresentation oldFit R selected m parts B choiceEq wide age radix reciprocal).model
      arch hp one pin sh stageDiv → Bool → Option SignedDrawing.Slot :=
  v.selectedLocator oldFit R selected m parts B choiceEq wide age radix reciprocal arch hp one pin sh stageDiv
end

section
attribute [local irreducible] selectedModelPresentation selectedLocator
include stageDiv in
private abbrev physicalFirstCableLaw : Prop :=
  SelectedFirstCableLaw (v:=v) (selected:=selected) (presented:=(info)) (arch:=arch)
    (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (stageDiv:=stageDiv)
    (v.selected_lookup_on_physical_presentation oldFit R selected m parts B choiceEq wide age radix reciprocal arch hp one pin sh stageDiv)
end
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
include stageDiv in
theorem selected_firstCable :
    physicalFirstCableLaw (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts)
      (B:=B) (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix) (reciprocal:=reciprocal)
      (arch:=arch) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (stageDiv:=stageDiv) :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity:Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wire hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload socketUnit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof := picked.choose_spec
    let normalized:=selectedProof.2.2
    let numberedSection := OrdinaryLink.numbered_firstCable (prior:=prior) link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (board_capacity ids capacity)
      arch hp one pin sh stageDiv
    run_tac Lean.Elab.Tactic.withMainContext do
      let some sectionProof := (← Lean.getLCtx).findFromUserName? `numberedSection
        | throwError "numbered cable section is missing"
      (← Lean.Elab.Tactic.getMainGoal).assign sectionProof.toExpr
      Lean.Elab.Tactic.replaceMainGoal []


local notation "rawWire" => DescentRawCablePanel.Live A (rr).pick
local notation "fromDonor" e:arg => v.world.graph.src (anchor (rr).pick (e).val)
local notation "zAt" e:arg => DescentRawCablePanel.shortSlot A S v.prior.valid native hosts (rr).pick e

/-- The old anchor slot and role physically emitted on that normalized source
identify the exact deduplicated W row at the surviving receiver. -/
theorem selected_donated_role (use : OrdinaryModel.PublicUse v.nonnegative (v.prior.placement.stage) selected v.prior.order (info).model arch hp one pin sh stageDiv) (side : Bool) (raw : rawWire) (wire : raw.val=use.cable.val)
    (entry : SignedDrawing.Slot) (located : whereAt use side=some entry)
    (query : Fin (ss).hosts) (sameHost : entry.host=query.val) (receiver : Fin H)
    (accepted : DepotRAM.Material.Route.receiver H pitch query=some receiver) (p : Fin (breadth D))
    (visits : Gather.select (Gather.reaching R) receiver p=some (hosts ((A).pos (fromDonor raw)).2)) :
    entry.role=(finProdFinEquiv (p,(zAt raw).2)).val :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap ≤ 2^(ss).fieldBits := space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wireSpace hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload socketUnit profile seats =>
    have sourceRateEq := link.sourceRate
    rcases sourceRateEq with rfl
    have stageEq := eq_of_heq link.placement
    rcases stageEq with rfl
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof:=picked.choose_spec
    let normalized:=selectedProof.2.2
    exact OrdinaryLink.actual_donated_role link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (board_capacity ids capacity)
      arch hp one pin sh stageDiv use side raw wire entry located query sameHost receiver accepted p visits

theorem selected_donated_receiver (use : OrdinaryModel.PublicUse v.nonnegative (v.prior.placement.stage) selected v.prior.order (info).model arch hp one pin sh stageDiv) (edge : Incident (world₁).graph use.node.1) (lo : ℕ)
    (within : (lo+1)*p≤(world₁).graph.width edge.val) (hit : observed use.node use.arg=.inl ⟨.inl edge,lo,within⟩)
    (entry : SignedDrawing.Slot) (located : whereAt use (decide ((world₁).graph.src edge.val≠use.node.1))=some entry) :
    let x:=Reached.originalSite (info).same use.node.1
    entry.host=(v.target.vertex (v.target.placement.pos x).2).val ∧
    entry.group=(v.target.placement.pos x).1.val ∧ entry.block=(v.target.placement.block x).val :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap ≤ 2^(ss).fieldBits := space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wireSpace hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload socketUnit profile seats =>
    have sourceRateEq := link.sourceRate
    rcases sourceRateEq with rfl
    have stageEq := eq_of_heq link.placement
    rcases stageEq with rfl
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof:=picked.choose_spec
    let normalized:=selectedProof.2.2
    let receipt := OrdinaryLink.actual_donated_receiver (prior:=prior) link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (board_capacity ids capacity)
      arch hp one pin sh stageDiv
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let ctx ← Lean.getLCtx
      let getLocal (key : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
        let some decl := ctx.findFromUserName? key | throwError "missing local {key} in concrete receiver"
        pure decl.toExpr
      let declaration ← getLocal `receipt
      let values ← #[`use, `edge, `lo, `within, `hit, `entry, `located].mapM getLocal
      goal.assign (Lean.mkAppN declaration values)
      Lean.Elab.Tactic.replaceMainGoal []

theorem selected_donated_mark (use : OrdinaryModel.PublicUse v.nonnegative (v.prior.placement.stage) selected v.prior.order (info).model arch hp one pin sh stageDiv) (side : Bool) (entry : SignedDrawing.Slot) (found : whereAt use side=some entry) :
    entry.marked=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role use.cable.val)
      (decide (anchor (rr).pick use.cable.val∈v.world.core)) :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap ≤ 2^(ss).fieldBits := space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wireSpace hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload socketUnit profile seats =>
    have sourceRateEq := link.sourceRate
    rcases sourceRateEq with rfl
    have stageEq := eq_of_heq link.placement
    rcases stageEq with rfl
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof:=picked.choose_spec
    let normalized:=selectedProof.2.2
    exact OrdinaryLink.actual_donated_mark link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (board_capacity ids capacity)
      arch hp one pin sh stageDiv use side entry found

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_donated_mark"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_donated_role"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_donated_receiver"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_firstCable"

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
