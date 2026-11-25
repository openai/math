import OAI.Hierarchy.DescentRegisteredOldCableOrigin
import OAI.Hierarchy.DescentDatedOriginalOldSocket
import OAI.Hierarchy.DescentDepotReceiver
import OAI.Hierarchy.DescentIssuedChartAgreement
import OAI.Hierarchy.DescentReachedScalarReshape

namespace OAI
/-! The registered node and the selected end of its original cable use the same physical group and receiver. -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentCompiler DescentStageEdgeReceipt
open DescentHostDirectory DescentHostDegree DescentPackedOperand DescentNetworkPartition
open Computability.BorderVNP.Crossing DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {c : (cap.placement.stage.result he).Choice}
    {n : Normalize ((cap.placement.stage.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he cap.placement.stage c n target) (arch : Archive W)

local notation "A" => cap.placement
local notation "T" => cap.placement.stage
local notation "r" => BitDescription.scannedRows he T
local notation "units" => fun _:(r).pairs=>(T).z
local notation "room" => fun _:(r).pairs=>le_refl (T).z
local notation "prof" => (r).profile c
local notation "lay" => bestLayout (branchWidth G units prof)
local notation "group" => GadgetNetwork.newSite W.graph (r).pick lay (r).pack
local notation "own₀" => (activeChart ticket).key he T c
local notation "M" => rawGraph he T c
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick units room prof
local notation "next" => (ticket.advance arch).bit
private abbrev receiverRawSite (x : NodeOrder.All next) : (M).Site :=
  ((names).symm (roots ticket arch x)).1

private abbrev receiverCoordinate (x : NodeOrder.All next) : Fin (S.groupCount i) × cap.V :=
  (currentLabel ticket arch x.1 x.2).val.1

local notation "rawSite₀" x:arg => receiverRawSite ticket arch x
local notation "here" x:arg => receiverCoordinate ticket arch x

/-- On a self-loop the physical selector reads the source end. -/
def inputTarget (x:NodeOrder.All next) (e:Incident (M) (rawSite₀ x)) : Bool :=
  decide ((M).src e.val≠rawSite₀ x)

private theorem selected_incident_endpoint {α : Type} [DecidableEq α] {a b v : α}
    (hit : a = v ∨ b = v) : (if decide (a ≠ v) then b else a) = v := by
  by_cases h : a = v
  · simp [h]
  · simpa [h] using hit.resolve_left h

theorem input_endpoint (x:NodeOrder.All next) (e:Incident (M) (rawSite₀ x)) :
    (if inputTarget ticket arch x e then (M).dst e.val else (M).src e.val)=rawSite₀ x :=by
  exact selected_incident_endpoint e.property

private theorem raw_named_site (y : NodeOrder.All arch.bit ⊕ (r).pairs × Fin 6) :
    rawNodeSite (he:=he) («T»:=T) (c:=c) arch y = ((names).symm y).1 := by
  rcases y with ⟨u, a⟩ | ⟨t, s⟩ <;> rfl

private theorem mergeHub_receiver {α : Type} (hub : α → Bool)
    (a b : ℕ) (v : DescentHostDirectory.Key α) : (mergeHub hub a b v).1 = v.1 := by
  unfold mergeHub
  split <;> rfl

private theorem map_endpoint {α β : Type} (f : α → β) (side : Bool) (src dst v : α)
    (endpoint : (if side then dst else src) = v) :
    f v = (if side then f dst else f src) := by
  cases side <;> exact congrArg f endpoint.symm

theorem original_receiver (same:∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e))
    (x:NodeOrder.All next) (e:Incident (M) (rawSite₀ x)) :
    let owned:=StarKeys.nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) (T).cap
      (nativeAddress he T) same lay
    let side:=inputTarget ticket arch x e
    here x=(if side then owned (group ((M).dst e.val)) else owned (group ((M).src e.val))).1 :=by
  intro owned side
  have physical := raw_named_site (cap:=cap) (he:=he) (c:=c) arch (roots ticket arch x)
  have first : here x = ((own₀) (group (rawSite₀ x))).1 :=
    (mergeHub_receiver (activeChart ticket).hub (T).k (gainExponent 20 (T).Δ)
      ((own₀) (group (rawNodeSite (he:=he) («T»:=T) (c:=c) arch (roots ticket arch x))))).trans
      (congrArg (fun u : (M).Site => ((own₀) (group u)).1) physical)
  have chart := DFunLike.congr_fun (IssuedDonorChart.native_key he T c (activeChart ticket) same) (group (rawSite₀ x))
  have selected := map_endpoint (fun u : (M).Site => owned (group u)) side
    ((M).src e.val) ((M).dst e.val) (rawSite₀ x) (input_endpoint ticket arch x e)
  exact first.trans ((congrArg Prod.fst chart).trans (congrArg Prod.fst selected))

theorem old_cable_group (v:W.graph.Site) (wire:Incident W.graph v)
    (positive:0<(A).grainCount wire.val) (parent:DescentSharedCableNames.Stage.Positive A)
    (mode:Fin 3) (role:Fin 11) (picked:CablePort A he ⟨wire.val,positive⟩ mode parent role) :
    ((A).pos v).1=((A).pos (W.graph.src parent.val)).1 :=by
  exact (old_socket_coordinates A v wire).1.trans (congrArg Prod.fst (CablePort.same_position A he picked))

local notation "pitch" => (2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2)
local notation "sitePos" x:arg => target.placement.pos (x:NodeOrder.All next).1
private abbrev receiverFlatHost (x : NodeOrder.All next) : Fin (Fintype.card cap.V * pitch) :=
  hostIndex ticket (target.vertex (sitePos x).2)

local notation "flatHost" x:arg => receiverFlatHost ticket arch x

/-- The old group and host use two different quotient operations in the actual receiver. -/
theorem input_location (age:i<S.length) (radix:S.radix=2^k) (x:NodeOrder.All next) :
    (flatHost x).val/pitch=(cap.vertex (here x).2).val ∧
    (finProdFinEquiv ((sitePos x).1,target.placement.block x.1)).val=(here x).1.val:=by
  obtain ⟨pair,groupId⟩:=older_location ticket arch age radix x.1 x.2
  exact ⟨congrArg (fun t=>t.1.val) pair,congrArg Fin.val groupId⟩

theorem registered_receiver_at (age:i<S.length) (radix:S.radix=2^k) (x:NodeOrder.All next)
    {K H:ℕ} (h:Fin K) (wide:Fintype.card cap.V≤H) (hostWord:h.val=(flatHost x).val) :
    DescentRawCablePanel.DepotRAM.Material.Route.receiver H pitch h=
      some ((cap.vertex (here x).2).castLE wide):=by
  have older:= (input_location ticket arch age radix x).1
  rw [←hostWord] at older
  have positive:0<pitch:=(Nat.zero_le _).trans_lt (localIndex ticket arch x.1 x.2).isLt
  have inRange:h.val/pitch<H:=older.trans_lt ((cap.vertex (here x).2).isLt.trans_le wide)
  rw [DescentRawCablePanel.DepotRAM.Material.Route.receiver,dite_eq_left ⟨positive,inRange⟩]
  exact congrArg some (Fin.ext older)

theorem registered_cohort_at (age:i<S.length) (radix:S.radix=2^k) (x:NodeOrder.All next)
    {G₁ B₁:ℕ} (g₁:Fin G₁) (b₁:Fin B₁) (blockCount:B₁=2^k)
    (groupWord:g₁.val=(sitePos x).1.val) (blockWord:b₁.val=(target.placement.block x.1).val) :
    (finProdFinEquiv (g₁,b₁)).val=(here x).1.val:=by
  rw [←(input_location ticket arch age radix x).2]
  simp only [finProdFinEquiv_apply_val,blockCount,groupWord,blockWord]

theorem registered_endpoint_receiver (same:∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e))
    (age:i<S.length) (radix:S.radix=2^k) (x:NodeOrder.All next) (wire:Incident (M) (rawSite₀ x))
    {L H:ℕ} (h:Fin L) (wide:Fintype.card cap.V≤H) (word:h.val=(flatHost x).val) :
    let owned:=StarKeys.nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) (T).cap
      (nativeAddress he T) same lay
    let side:=inputTarget ticket arch x wire
    DescentRawCablePanel.DepotRAM.Material.Route.receiver H pitch h=
      some ((cap.vertex ((if side then owned (group ((M).dst wire.val))
        else owned (group ((M).src wire.val))).1).2).castLE wide):=by
  intro owned side
  have endpoint := original_receiver ticket arch same x wire
  exact (registered_receiver_at ticket arch age radix x h wide word).trans
    (congrArg (fun y : Fin (S.groupCount i) × cap.V => some ((cap.vertex y.2).castLE wide)) endpoint)

theorem registered_old_cohort (age:i<S.length) (radix:S.radix=2^k) (x:NodeOrder.All next)
    {G₁ B₁:ℕ} (g₁:Fin G₁) (b₁:Fin B₁) (blockCount:B₁=2^k)
    (groupWord:g₁.val=(sitePos x).1.val) (blockWord:b₁.val=(target.placement.block x.1).val)
    (v:W.graph.Site) (prior:((A).pos v).1=(here x).1) (e:Incident W.graph v)
    (positive:0<(A).grainCount e.val) (parent:DescentSharedCableNames.Stage.Positive A)
    (mode:Fin 3) (role:Fin 11) (port:CablePort A he ⟨e.val,positive⟩ mode parent role) :
    (finProdFinEquiv (g₁,b₁)).val=((A).pos (W.graph.src parent.val)).1.val:=by
  exact (registered_cohort_at ticket arch age radix x g₁ b₁ blockCount groupWord blockWord).trans
    (congrArg Fin.val (prior.symm.trans (old_cable_group (cap:=cap) v e positive parent mode role port)))

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
