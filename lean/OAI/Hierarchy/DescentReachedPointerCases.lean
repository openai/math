import OAI.Hierarchy.DescentOrdinaryNativePrivateKeys
import OAI.Hierarchy.DescentReachedSourceOperand
import OAI.Hierarchy.DescentOrdinaryIssuedPointers

namespace OAI
/-! Exhaustive classification of the native ordinary operand job at every actual reached scalar. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.GadgetNetwork DescentKernelHistory
open DescentNetworkPartition DescentHostDirectory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P I V T : Type} [Field F] [Fintype I] [DecidableEq T] {d p R Z : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} (B : BitDescription W)
    (G : PoweredGadget F) (pick : I × Fin 2 ↪ W.graph.Edge)
    (z : I → ℕ) (hz : ∀ i, 0 < z i) (fit : ∀ i j, W.graph.width (pick (i,j)) = z i * G.b)
    (room : ∀ i, z i ≤ Z) (pack : W.graph.Site → V) (prof : I → Profile G.C)
    (hp : 0 < p) (one : 1 ≤ R) (pin : ∀ a, p ∣ bits a) (sh : WorldShape p R B)
    (whole : ∀ i, p ∣ z i)
local notation "sel" => W.selected G pick z hz fit pack prof
local notation "net" => physical W.graph pick (branchWidth G z prof)
local notation "grp" => newSite W.graph pick (bestLayout (branchWidth G z prof)) pack
local notation "oldBits" => physicalBits G W.toWorld pick z room prof B.recipe
local notation "oldShape" => physicalShape W B G pick z room prof hp sh.sites sh.edges pin whole
variable (key : (W.selected G pick z hz fit pack prof).graph.Site → Key T) (flag : T → Bool) (k g : ℕ)
local notation "addr" => MarkedWorld.address sel key flag k g
local notation "reclaimed" => ↥(MarkedWorld.reclaimed sel key flag k g)
local notation "x₁" => fun _ : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : reclaimed => (0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun t : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (by simp : ‖x₁ t‖ ≤ 1)
local notation "ok₂" => fun t : reclaimed => (by simp : ‖x₂ t‖ ≤ 1)
local notation "lastWorld" => (sel).coalesced key flag k g

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false


local notation "readValue" => selectedSourceArgument B G pick z hz fit room pack prof hp pin sh whole key flag k g

include one in
theorem selectedSource_public_cases (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2))
    (pub : ∃ b, readValue src i = .inl b) {Result : Prop}
    (survivor : ∀ (e : Incident net src.1) (chunk : ℕ) (len : (chunk+1)*p ≤ (net).width e.val),
      addr (grp ((net).src e.val)) ≠ addr (grp ((net).dst e.val)) →
      ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inl e,chunk,len⟩ → Result)
    (pinRead : ∀ (a : Attached net src.1) (chunk : ℕ) (len : (chunk+1)*p ≤ bits a.val),
      ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inr a,chunk,len⟩ → Result) : Result := by
  obtain ⟨b,actual⟩ := pub
  unfold selectedSourceArgument at actual
  cases raw : ((oldShape src.1).recipe hp).operand src.2 i with
  | inr u =>
    let prior : ((oldShape src.1).recipe hp).UsedWord := ⟨u,⟨src.2,i,raw⟩⟩
    obtain ⟨t,closed,_⟩ := selected_coalesced_inherited B G pick z hz fit room pack prof hp one pin sh whole
      key flag k g src.1 prior
    rw [raw] at actual
    cases actual.symm.trans closed
  | inl b =>
    rcases b with ⟨e|a,chunk,len⟩
    · by_cases same : addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val))
      · by_cases early : grp ((net).src e.val) = grp ((net).dst e.val)
        · obtain ⟨t,closed,_⟩ := selected_coalesced_first B G pick z hz fit room pack prof hp one pin sh whole
            key flag k g src.1 e chunk len early
          rw [raw] at actual
          cases actual.symm.trans closed
        · obtain ⟨t,closed,_⟩ := selected_coalesced_second B G pick z hz fit room pack prof hp one pin sh whole
            key flag k g src.1 e chunk len early same
          rw [raw] at actual
          cases actual.symm.trans closed
      · exact survivor e chunk len same raw
    · exact pinRead a chunk len raw

theorem selectedSource_surviving (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2))
    (e : Incident net src.1) (chunk : ℕ) (len : (chunk+1)*p ≤ (net).width e.val)
    (openAt : addr (grp ((net).src e.val)) ≠ addr (grp ((net).dst e.val)))
    (raw : ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inl e,chunk,len⟩) :
    ∃ b, readValue src i = .inl b := by
  unfold selectedSourceArgument
  rw [raw]
  have moved := free_word net grp x₁ ok₁ oldBits hp addr x₂ ok₂ src.1 e chunk len openAt
  exact ⟨_,moved⟩

theorem selectedSource_private_cases (src : NodeOrder.Global (N:=net) oldBits)
    (i : Fin (((oldShape src.1).recipe hp).arity src.2))
    (closed : (∃ b, readValue src i = .inl b) → False) {Result : Prop}
    (carried : ∀ h : ((oldShape src.1).recipe hp).UsedWord,
      ((oldShape src.1).recipe hp).operand src.2 i = .inr h.val → Result)
    (capture : ∀ (e : Incident net src.1) (chunk : ℕ) (len : (chunk+1)*p ≤ (net).width e.val),
      addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val)) →
      ((oldShape src.1).recipe hp).operand src.2 i = .inl ⟨.inl e,chunk,len⟩ → Result) : Result := by
  cases raw : ((oldShape src.1).recipe hp).operand src.2 i with
  | inr u => exact carried ⟨u,⟨src.2,i,raw⟩⟩ raw
  | inl b =>
    rcases b with ⟨e|a,chunk,len⟩
    · by_cases same : addr (grp ((net).src e.val)) = addr (grp ((net).dst e.val))
      · exact capture e chunk len same raw
      · exact (closed (selectedSource_surviving B G pick z hz fit room pack prof hp pin sh whole
          key flag k g src i e chunk len same raw)).elim
    · apply False.elim (closed ?_)
      unfold selectedSourceArgument
      rw [raw]
      let atLast : Attached (lastWorld).graph (addr (grp src.1)) := ⟨a.val,congrArg (addr ∘ grp) a.property⟩
      exact ⟨⟨.inr atLast,chunk,len⟩,rfl⟩
end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentLocalArchiveOrder
open DescentPackedOperand DescentOrdinaryNativeNames
open scoped Classical
noncomputable section

theorem observedCaptureKey {original together finalHome : Prop}
    [Decidable original] [Decidable together] [Decidable finalHome]
    (owners : original ↔ together) (arrived : finalHome)
    (native : ℕ ↪ ℕ) (site donor label k : ℕ) (read : native site = donor) (key fall : Key)
    (seen : key = if decide original then Key.first donor 0 label k
       else if !decide original && decide finalHome then Key.second donor 0 label k else fall) :
    key = captures native ((if decide (¬together) then Key.second else Key.first) site 0 label k) := by
  rw [captured_root, read]
  by_cases early : together
  · simpa [early,owners.mpr early] using seen
  · have late : ¬ original := fun h => early (owners.mp h)
    simpa [early,late,arrived] using seen
end
end Hierarchy.DescentLocalArchiveOrder

namespace Hierarchy.DescentOrdinaryNativeNames
open DescentHostDirectory DescentOrdinaryDonorHalo DescentHaloCompilation DescentColonies
open scoped Classical
noncomputable section

theorem captureReceipt_at {U J V : Type} [Fintype U] [DecidableEq J] [DecidableEq V] {H D k : ℕ}
    (near : V → Finset V) (name : V ↪ Fin H) (roster : Fin H → Fin D → Option (Fin H))
    (listed : ∀ u v, v ∈ near u → ∃ j, roster (name u) j = some (name v))
    (pos : U → J × V) (blk : U → Block k) (unique : Function.Injective fun u => (pos u, blk u))
    {a b : Key (J × V)} (common : a.1 = b.1) (u : U) (receipt : ℕ → Prop)
    (seen : ∃ m : u ∈ siteSet (groupedNear near) pos a, receipt (((shared near name roster listed pos blk unique).slot a) ⟨u,m⟩).val) :
    ∃ m : u ∈ siteSet (groupedNear near) pos b, receipt (((shared near name roster listed pos blk unique).slot b) ⟨u,m⟩).val := by
  rcases a with ⟨a,aa⟩
  rcases b with ⟨b,bb⟩
  cases common
  exact seen
end
end Hierarchy.DescentOrdinaryNativeNames

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
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
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "selectedShape" => sh.selected hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
local notation "cut" => (ticket.quantum.symm ▸ ticket.cuts)
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "chart" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ))
local notation "pre" => (selectedShape).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local instance pointerCasesMergedFintype : Fintype (DescentSixParty.Merged W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack) :=
  DescentSixParty.mergedFinite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun x : (sel).graph.Site=> (by simp : ‖x₁ x‖≤1)
local notation "ok₂" => fun x : C=> (by simp : ‖x₂ x‖≤1)
local notation "M" => rawGraph he T c
local notation "base" => physicalBits G W.toWorld (r).pick uni room prof arch.bit.recipe
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "selectedDesc" => arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof
local notation "quot" => (sel).graph
local notation "r₁" => (selectedDesc).recipe
local notation "q₂" => ((sel).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)).graph
local notation "r₂" => ((selectedDesc).coalesced ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)).recipe
local notation "firstRead" => nextArg M group x₁ ok₁ base hp
local notation "secondRead" => fun v : (M).Site => nextArg quot addr x₂ ok₂ r₁ hp (group v)
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" => operandSource ticket arch
local notation "wireFits" => physical_multiple W G (r).pick uni prof sh.edges whole
local notation "values" => (Σ t,BlockRef p (boundaryWidth q₂ t)⊕Private (r₂ t) p)
private abbrev pointerPeer :=
  ∀ h : C, DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) (r).pick uni prof loc h → ℕ

variable {K:ℕ} (slots:∀v,DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp)↪Fin K)
    (peer : pointerPeer ticket arch hp one pin sh unit)

local notation "halo" => chartHalo (cap:=cap) (c:=c) chart
local notation "reaches" => chartHalo_members ticket chart
local notation "oldHidden" => fun v : (M).Site => ((baseShape v).recipe hp).UsedWord
local notation "oldCode" => DescentPrivateRawLabels.carried (W:=W) (G:=G) (p:=p) arch.bit (r).pick uni room prof hp sh.sites
  sh.edges pin whole group addr halo (reaches).2.1 slots
local notation "keyAt" => reachedPrivateKey ticket arch hp one pin sh unit slots peer

local notation:max "srcArg" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2
  (sourceIndex ticket arch hp one pin sh unit x j)
local notation:max "sourceSite" x:arg => (source x).1
local notation:max "wireAt" x:arg => Incident (M) (sourceSite x)
local notation:max "equalHome" e:arg => loc ((M).src (e).val)=loc ((M).dst (e).val)

def captureLabel (v:(M).Site) (e:Incident (M) v) (k:ℕ) (full:(k+1)*p≤(M).width e.val)
    (same:loc ((M).src e.val)=loc ((M).dst e.val)) : Key :=
  let ext:=e.property.elim (congrArg (loc)) (fun t=>same.trans (congrArg (loc) t))
  let t:DescentPrivateRawLabels.LocalWire (W:=W) (G:=G) (p:=p) (r).pick uni prof loc (loc v):=⟨⟨e.val,⟨k,(Nat.le_div_iff_mul_le hp).mpr full⟩⟩,ext⟩
  (if decide (group ((M).src e.val)≠group ((M).dst e.val)) then Key.second else Key.first)
    (DescentPrivateRawLabels.root (W:=W) (G:=G) (p:=p) (r).pick uni prof loc halo (reaches).1 t).val (peer _ t)
    (11*(DescentPrivateRawLabels.old cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid
      (r).pick uni pos (r).fit prof loc hp t).val+(DescentCableDonorNames.role e.val).val) k

def carriedLabel (v:(M).Site) (h:oldHidden v) : Key :=
  let donor:=DescentPrivateRawLabels.carried (W:=W) (G:=G) (p:=p) (c:=loc v)
    arch.bit (r).pick uni room prof hp sh.sites sh.edges pin whole group addr halo (reaches).2.1
    slots ⟨⟨v,h⟩,rfl⟩
  Key.carried donor.1.val donor.2.val

variable (native:ℕ↪ℕ) (x:NodeOrder.All (ticket.advance arch).bit)
    (j:Fin ((((afterOrdinary hp one pin ticket arch sh unit).sites x.1).recipe hp).arity x.2)) (key:Key)
local notation:max "privateCode" h:arg => carriedLabel ticket arch hp one pin sh unit slots (sourceSite x) h
local notation:max "captureCode" e:arg k:arg length:arg same:arg => captureLabel ticket arch hp one pin sh unit peer (sourceSite x) e k length same

section ArgumentResponses
attribute [local irreducible] captureLabel carriedLabel sourceIndex operandSource afterOrdinary
/-- These are the four lower numerical responses at the original location
of a single scalar, prior to applying either of its quotient maps. -/
structure InputResponse : Prop where
  inherited : ∀h:oldHidden (sourceSite x),srcArg x j=.inr h.val→key=privateCode h
  captured : ∀(e:wireAt x) k (length:(k+1)*p≤(M).width e.val) (same:equalHome e),
    srcArg x j=.inl ⟨.inl e,k,length⟩→key=DescentOrdinaryNativeNames.captures native (captureCode e k length same)
  survivor : ∀(e:wireAt x) k (length:(k+1)*p≤(M).width e.val),
    ¬(equalHome e)→srcArg x j=.inl ⟨.inl e,k,length⟩→∃near serial within,key=Key.cable near serial within
  pin : ∀(z:Attached (M) (sourceSite x)) k (length:(k+1)*p≤bits z.val),
    srcArg x j=.inl ⟨.inr z,k,length⟩→∃index,key=Key.pin index k

variable (issued:InputResponse ticket arch hp one pin sh unit slots peer native x j key)

set_option maxHeartbeats 240000 in
include issued in
theorem hidden_response (h:(((after).sites x.1).recipe hp).UsedWord)
    (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inr h.val) :
    key=DescentOrdinaryNativeNames.captures native (keyAt x.1 h) := by
  apply selectedSource_private_cases arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp pin sh whole
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
    (source x) (sourceIndex ticket arch hp one pin sh unit x j)
  · rintro ⟨b,actual⟩
    obtain ⟨_,found⟩ := public_of_source ticket arch hp one pin sh unit x j actual
    cases found.symm.trans hit
  · intro prior original
    have code := carried_private ticket arch hp one pin sh unit slots peer x j h hit prior original
    apply (issued.inherited prior original).trans
    rw [code]
    unfold carriedLabel selectedInheritedKey
    rfl
  · intro e k len same original
    have code := captured_private ticket arch hp one pin sh unit slots peer x j h hit e k len original same
    apply (issued.captured e k len same original).trans
    rw [code]
    unfold captureLabel
    rfl

include issued in
theorem public_response {b₀} (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inl b₀) :
    3≤key.fields 0 := by
  apply selectedSource_public_cases arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ) (source x)
    (sourceIndex ticket arch hp one pin sh unit x j) (public_source ticket arch hp one pin sh unit x j hit)
  · intro e k len diff raw
    obtain ⟨near,serial,within,eqn⟩ := issued.survivor e k len diff raw
    rw [eqn]
    exact Nat.le_refl 3
  · intro pinRef k len raw
    obtain ⟨index,eqn⟩ := issued.pin pinRef k len raw
    rw [eqn]
    exact Nat.le_succ 3

end ArgumentResponses

section NativeDonors
open DescentOrdinaryNativeNames DescentHaloCompilation
variable {H degree:ℕ} (name:cap.V↪Fin H) (roster:Fin H→Fin degree→Option (Fin H))
    (listed:∀a t,t∈cap.placement.near a→∃i,roster (name a) i=some (name t))
local notation "A" => cap.placement
local notation "arena" => DescentOrdinaryNativeNames.measured (A).near name roster listed (A).pos (A).block cap.valid.coordinates
  (fun c:C=>c.val) halo (fun _=>rfl)

def receivedRoot (v:n.result.graph.Site):ℕ↪ℕ:=arena ((bk).home v)

theorem source_home (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2)) :
    (bk).home x.1=loc (source x).1 :=
  congrArg Sigma.fst (source_read ticket arch hp one pin sh unit x j).choose_spec.2

private theorem measured_receiver {U J V C₀ : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    {H D k B : ℕ} (near : V → Finset V) (name : V ↪ Fin H) (roster : Fin H → Fin D → Option (Fin H))
    (listed : ∀ u v, v ∈ near u → ∃ j, roster (name u) j = some (name v))
    (position : U → J × V) (block : U → DescentColonies.Block k)
    (unique : Function.Injective fun u => (position u, block u))
    (location : C₀ → DescentHostDirectory.Key (J × V)) (resident : DescentCableDonorNames.Halo C₀ U B)
    (members : ∀ c, resident.member c = DescentOrdinaryDonorHalo.siteSet (groupedNear near) position (location c))
    (spot : C₀) (row : DescentHostDirectory.Key (J × V)) (rack : (location spot).1 = row.1)
    (u : U) (presence : u ∈ resident.member spot) (read : ℕ ↪ ℕ)
    (eqRead : read = measured near name roster listed position block unique location resident members spot) :
    ∃ mem : u ∈ DescentOrdinaryDonorHalo.siteSet (groupedNear near) position row,
      read ((resident.slot spot) ⟨u,presence⟩).val =
        ((shared near name roster listed position block unique).slot row ⟨u,mem⟩).val := by
  have origin := Eq.mp (congrArg (fun s : Finset U => u ∈ s) (members spot)) presence
  have target : u ∈ DescentOrdinaryDonorHalo.siteSet (groupedNear near) position row := by
    change u ∈ Finset.univ.filter (fun site => position site ∈ DescentOrdinaryDonorHalo.around (groupedNear near) 4 row.1)
    change u ∈ Finset.univ.filter (fun site => position site ∈ DescentOrdinaryDonorHalo.around (groupedNear near) 4 (location spot).1) at origin
    simpa only [rack] using origin
  refine ⟨target,?_⟩
  rw [eqRead]
  exact (measured_at near name roster listed position block unique location resident members spot u presence).trans
    (same_receiver near name roster listed position block unique rack u _ target)

private theorem merged_receiver {L : Type} (flag : L → Bool) (bits gain : ℕ)
    (home : DescentHostDirectory.Key L) :
    (DescentHostDirectory.mergeHub flag bits gain home).1 = home.1 := by
  unfold DescentHostDirectory.mergeHub
  split <;> rfl

private def donorRack (site : C) : Fin (S.groupCount i) × cap.V := site.val.1

private theorem donorRack_at (v : (M).Site) :
    donorRack ticket arch hp one pin sh unit (loc v) = ((chart).key he T c (group v)).1 :=
  merged_receiver (chart).hub T.k (gainExponent 20 T.Δ) ((chart).key he T c (group v))

attribute [local irreducible] privateChart privateBooks operandSource DescentOrdinaryNativeNames.measured in
theorem received_root_value (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e:Incident (M) (sourceSite x)) (same:equalHome e) :
    let v:=sourceSite x
    let nbr:=((chart).key he T c) (group ((M).src e.val))
    let donor:=W.graph.src (DescentCableDonorNames.anchor (r).pick e.val)
    let whereFrom:=e.property.elim (congrArg (loc)) (fun t=>same.trans (congrArg (loc) t))
    let presence:donor∈(halo).member (loc v):=whereFrom ▸ (reaches).1 e.val
    ∃mem:donor∈DescentOrdinaryDonorHalo.siteSet (DescentHostDirectory.groupedNear (A).near) (A).pos nbr,
      receivedRoot ticket arch hp one pin sh unit name roster listed x.1 (((halo).slot (loc v)) ⟨donor,presence⟩).val=
        ((shared (A).near name roster listed (A).pos (A).block cap.valid.coordinates).slot nbr ⟨donor,mem⟩).val :=by
  intro v nbr donor whereFrom presence
  have rack : donorRack ticket arch hp one pin sh unit (loc v) = nbr.1 :=
    (congrArg (donorRack ticket arch hp one pin sh unit) whereFrom.symm).trans
      (donorRack_at ticket arch hp one pin sh unit ((M).src e.val))
  have read : receivedRoot ticket arch hp one pin sh unit name roster listed x.1 = arena (loc v) :=
    congrArg (fun site : C => arena site) (source_home ticket arch hp one pin sh unit x j)
  exact measured_receiver (A).near name roster listed (A).pos (A).block cap.valid.coordinates
    (fun site : C => site.val) halo (fun _ => rfl) (loc v) nbr rack donor presence _ read

local notation "oldName" => (DescentPacking.originalId ((T.result he).state c).graph.Site) ∘ rawInput he T c ((r).state c)
local notation "newName" => rawOwner he T c n ((r).state c) (DescentPacking.originalId _)

theorem source_owners (v w:(M).Site) :
    (oldName v=oldName w ↔ group v=group w) ∧ (newName v=newName w ↔ loc v=loc w) :=by
  constructor
  · exact (DescentPacking.originalId ((T.result he).state c).graph.Site).injective.eq_iff.trans
      (Equiv.cast (congrArg (fun b : MarkedWorld F d P bits => b.graph.Site) ((r).state c).symm)).injective.eq_iff
  · have namesEq : (newName v = newName w) ↔
        n.destination (rawInput he T c ((r).state c) v) = n.destination (rawInput he T c ((r).state c) w) :=
      (DescentPacking.originalId n.result.graph.Site).injective.eq_iff
    let chosen := (IssuedRows.common_chart he T c ticket.issued ((r).state c)).choose
    let addressAt (receiptChart : IssuedDonorChart he T (Fin (S.groupCount i) × cap.V)) (u : (M).Site) :=
      mergeHub receiptChart.hub T.k (gainExponent 20 T.Δ) (receiptChart.key he T c (group u))
    have atSite (u : (M).Site) : (loc u).val = addressAt chosen u := by
      rfl
    have same : n.destination (rawInput he T c ((r).state c) v) = n.destination (rawInput he T c ((r).state c) w) ↔
        addressAt chosen v = addressAt chosen w :=
      (IssuedRows.common_chart he T c ticket.issued ((r).state c)).choose_spec.1.2 v w
    refine namesEq.trans (same.trans ?_)
    exact (show (addressAt chosen v = addressAt chosen w) ↔ (loc v).val = (loc w).val by rw [atSite v,atSite w]).trans
      (Subtype.ext_iff (a1:=loc v) (a2:=loc w)).symm

theorem observed_capture (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e:Incident (M) (sourceSite x)) (k:ℕ) (length:(k+1)*p≤(M).width e.val)
    (same:equalHome e) (key fall:Key)
    (seen:let site:=W.graph.src (DescentCableDonorNames.anchor (r).pick e.val)
      let nbr:=((chart).key he T c) (group ((M).src e.val))
      let live:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
        (⟨e.val,k,((Nat.le_div_iff_mul_le hp).mpr length)⟩:WireWord (M) p)
      let old:=DescentSharedCableNames.Stage.outgoing cap.placement (cap.order.trans Fin.valEmbedding) S
        cap.valid ⟨DescentCableDonorNames.anchor (r).pick e.val,live⟩
      ∃mem:site∈DescentOrdinaryDonorHalo.siteSet (DescentHostDirectory.groupedNear (A).near) (A).pos nbr,
        let donor:=((shared (A).near name roster listed (A).pos (A).block cap.valid.coordinates).slot nbr ⟨site,mem⟩).val
        let label:=11*old.val+(DescentCableDonorNames.role e.val).val
        let first:=decide (oldName ((M).src e.val)=oldName ((M).dst e.val))
        let final_:=decide (newName ((M).src e.val)=newName ((M).dst e.val))
        key=if first then Key.first donor 0 label k else if !first && final_ then Key.second donor 0 label k else fall) :
    key=DescentOrdinaryNativeNames.captures (receivedRoot ticket arch hp one pin sh unit name roster listed x.1)
      (captureLabel ticket arch hp one pin sh unit (fun _ _=>0) (sourceSite x) e k length same) :=by
  obtain ⟨mem,actual⟩ := seen
  obtain ⟨_,read⟩ := received_root_value ticket arch hp one pin sh unit name roster listed x j e same
  have owners := source_owners ticket arch hp one pin sh unit ((M).src e.val) ((M).dst e.val)
  unfold captureLabel
  exact observedCaptureKey owners.1 (owners.2.mpr same)
    (receivedRoot ticket arch hp one pin sh unit name roster listed x.1)
    _ _ _ k read key fall actual

theorem observed_capture_at (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e:Incident (M) (sourceSite x)) (k:ℕ) (length:(k+1)*p≤(M).width e.val)
    (same:equalHome e) (key fall:Key)
    (physical:DescentHostDirectory.Key (Fin (S.groupCount i)×cap.V))
    (aligned:physical.1=(((chart).key he T c) (group ((M).src e.val))).1)
    (seen:let site:=W.graph.src (DescentCableDonorNames.anchor (r).pick e.val)
      let nbr:=physical
      let live:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
        (⟨e.val,k,((Nat.le_div_iff_mul_le hp).mpr length)⟩:WireWord (M) p)
      let old:=DescentSharedCableNames.Stage.outgoing cap.placement (cap.order.trans Fin.valEmbedding) S
        cap.valid ⟨DescentCableDonorNames.anchor (r).pick e.val,live⟩
      ∃mem:site∈DescentOrdinaryDonorHalo.siteSet (DescentHostDirectory.groupedNear (A).near) (A).pos nbr,
        let donor:=((shared (A).near name roster listed (A).pos (A).block cap.valid.coordinates).slot nbr ⟨site,mem⟩).val
        let label:=11*old.val+(DescentCableDonorNames.role e.val).val
        let first:=decide (oldName ((M).src e.val)=oldName ((M).dst e.val))
        let final_:=decide (newName ((M).src e.val)=newName ((M).dst e.val))
        key=if first then Key.first donor 0 label k else if !first && final_ then Key.second donor 0 label k else fall) :
    key=DescentOrdinaryNativeNames.captures (receivedRoot ticket arch hp one pin sh unit name roster listed x.1)
      (captureLabel ticket arch hp one pin sh unit (fun _ _=>0) (sourceSite x) e k length same) :=by
  apply observed_capture ticket arch hp one pin sh unit name roster listed x j e k length same key fall
  let site := W.graph.src (DescentCableDonorNames.anchor (r).pick e.val)
  let receipt (donor : ℕ) : Prop :=
    let live:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
      (⟨e.val,k,((Nat.le_div_iff_mul_le hp).mpr length)⟩:WireWord (M) p)
    let old:=DescentSharedCableNames.Stage.outgoing cap.placement (cap.order.trans Fin.valEmbedding) S
      cap.valid ⟨DescentCableDonorNames.anchor (r).pick e.val,live⟩
    let label:=11*old.val+(DescentCableDonorNames.role e.val).val
    let first:=decide (oldName ((M).src e.val)=oldName ((M).dst e.val))
    let final_:=decide (newName ((M).src e.val)=newName ((M).dst e.val))
    key=if first then Key.first donor 0 label k else if !first && final_ then Key.second donor 0 label k else fall
  exact captureReceipt_at (A).near name roster listed (A).pos (A).block cap.valid.coordinates aligned site receipt seen

end NativeDonors

/-- Lower ticket jobs on the actual selected rectangular node/argument grid
supply the private equivalence and the public constructor tag simultaneously. -/
theorem site_keys (v:n.result.graph.Site) (cpu:Chronology.PhysicalOrdinary F P)
    (jobs:Fin cpu.resolver.jobs→DescentDatedPriorOperand.Source cpu.resolver)
    (block:Fin cpu.resolver.blocks) (shop:Fin cpu.resolver.hosts) (groupIndex:Fin cpu.resolver.groups)
    (node:(((after).sites v).recipe hp).Node↪Fin cpu.resolver.nodes)
    (arity:∀u,(((after).sites v).recipe hp).arity u≤cpu.resolver.operands)
    (received:∀s:DescentLocalPrivateNames.Slot (((after).sites v).recipe hp),
      InputResponse ticket arch hp one pin sh unit slots peer native ⟨v,s.1⟩ s.2
        (resolve (cpu.issuedFragment jobs block shop groupIndex (cpu.finalChart.mouths _ node arity s)))) :
    cpu.SourceKeys jobs block shop groupIndex (((after).sites v).recipe hp) node arity
      ((reachedPrivateKey ticket arch hp one pin sh unit slots peer v).trans (DescentOrdinaryNativeNames.captures native)) :=by
  refine ⟨?_,fun h=>?_,?_⟩
  · rintro ⟨u,j⟩ h observed
    exact hidden_response ticket arch hp one pin sh unit slots peer native ⟨v,u⟩ j _ (received ⟨u,j⟩) h
      ((DescentLocalPrivateNames.read_some _ u j h).mp observed)
  · change (DescentOrdinaryNativeNames.captures native (keyAt v h)).fields 0 < 3
    rw [DescentOrdinaryNativeNames.capture_fields]
    exact private_tag ticket arch hp one pin sh unit slots peer v h
  · rintro ⟨u,j⟩ gone
    cases found:(((after).sites v).recipe hp).operand u j with
    | inl b=>exact public_response ticket arch hp one pin sh unit slots peer native ⟨v,u⟩ j _ (received ⟨u,j⟩) found
    | inr t=>
      let used:(((after).sites v).recipe hp).UsedWord:=⟨t,⟨u,j,found⟩⟩
      have h:=(DescentLocalPrivateNames.read_some _ u j used).mpr found
      rw [gone] at h
      contradiction

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
