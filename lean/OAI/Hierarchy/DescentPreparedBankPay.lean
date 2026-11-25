import OAI.Hierarchy.DescentPaidResetBankSites
import OAI.Hierarchy.DescentPaidResetRecorded
import OAI.Hierarchy.DescentFallbackMeasuredWindow
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # The paid count at a bank actor from the retained original root-gather word -/
namespace Hierarchy.DescentPaidResidentCount.Reset.BankIssue
open DescentSixParty DescentChosenRouter DescentMixedRouter DescentPackedPrivateMenu DescentPackedFallbackTree
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentRotorRootPresence
open DescentResetCableSlots DescentResetHostSize DescentGL DescentColonies
open DescentSharedCableNames.Stage DescentTreePrefixIntervals DescentRouterSlots
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {n h r ht slots levels L degree cap field : ℕ}

def goodInput (n packet f ht slots levels : ℕ) (ticket : Code r) (word : Cell (field*3)) :=
  let x:=(encode field 3).symm word
  DescentIssuedGoodHeaders.key n packet f ht slots levels ticket
    (fun q=>match q with | .inl i=>if i=0 then x 0 else x 1 | .inr _=>x 2)

def treeInput (s : Bool) (ticket : Code r×Option (Fin (2^n)))
    (word : Cell (field*DescentFallbackPeriod.inputCount degree L cap n r)) :
    Key (n:=n) r ht (L*(2*cap)) levels :=
  DescentFallbackPeriod.key s ticket (DescentFallbackPeriod.packet word)

theorem treeInput_read (s : Bool) (ticket : Code r×Option (Fin (2^n)))
    (v : DescentFallbackPeriod.Packet degree L cap n r field) :
    treeInput (ht:=ht) (levels:=levels) s ticket (DescentFallbackPeriod.encodePacket v)=
      DescentFallbackPeriod.key s ticket v := by simp only [treeInput,DescentFallbackPeriod.packet_encode]

theorem treeInput_amount_levels (G : NonlinearExpanders.Graph n h) (C packet batches a b : ℕ) (who : Site G ht)
    (s : Bool) (ticket : Code r×Option (Fin (2^n))) (x : Cell (field*DescentFallbackPeriod.inputCount degree L cap n r)) :
    amount G C packet batches who (treeInput (levels:=a) s ticket x)=
      amount G C packet batches who (treeInput (levels:=b) s ticket x) := by
  unfold treeInput DescentFallbackPeriod.key
  split
  · split <;> rfl
  · rfl

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)
local notation "depth" => T.commonDepth
local notation "r_" => Z.k-depth
local notation "R" => Z.placement

theorem goodInput_key (unit : 0<Z.unit) (f count : ℕ) (s : Bool) (g : (R).Good)
    (v : Z.V) (hi : Block depth) (t : Code r_) (old : Block r_→ℕ)
    (x : Fin 3→Cell field) (depthAt : (x 1).val=(R).b v-depth+1)
    (sampled : (x 2).val%2=old (sample t)%2)
    (mode : ∀i,old i%2=Bool.toNat (decide ((R).hub v ∨
      (v,group ((R).b v) (DescentIssuedFallbackPanel.join ((T.commonLow v).trans ((R).depth v)) hi i))∈(R).keys)))
    (home : Z.rootVertex T (.inl g)=v) (loc : Z.rootBlock T (.inl g)=hi) (tag : Z.goodLabel T g=t)
    (calendar : (Z.circuit s g).layers=DescentRecordedRotorLayers.layers Z.n Z.width f (x 0).val) :
    goodInput Z.n Z.width f Ht count Z.layerBits t (encode field 3 x)=Z.rotorKey T unit count s g := by
  have present_ := (DescentIssuedGoodHeaders.root_fields Z T v hi t old mode (x 1).val (x 2).val depthAt sampled).mpr
    ⟨g,home,loc,tag⟩
  simp only [goodInput,Equiv.symm_apply_apply]
  unfold DescentIssuedGoodHeaders.key
  simp only [Fin.isValue, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ite_false, ite_true]
  rw [ite_eq_left present_]
  unfold ResetInput.rotorKey
  apply congrArg some
  apply congrArg Sum.inl
  apply Prod.ext
  · exact congrArg (DescentResetCableSlots.interval _) tag.symm
  · apply Fin.ext
    change DescentRecordedRotorLayers.layers Z.n Z.width f (x 0).val % 2^Z.layerBits = (Z.circuit s g).layers
    rw [←calendar,Nat.mod_eq_of_lt (Z.layers_fit unit s g)]

theorem goodInput_absent (f count : ℕ) (v : Z.V) (hi : Block depth) (t : Code r_)
    (old : Block r_→ℕ) (x : Fin 3→Cell field) (depthAt : (x 1).val=(R).b v-depth+1)
    (sampled : (x 2).val%2=old (sample t)%2)
    (mode : ∀i,old i%2=Bool.toNat (decide ((R).hub v ∨
      (v,group ((R).b v) (DescentIssuedFallbackPanel.join ((T.commonLow v).trans ((R).depth v)) hi i))∈(R).keys)))
    (empty : ¬∃g : (R).Good,Z.rootVertex T (.inl g)=v ∧ Z.rootBlock T (.inl g)=hi ∧ Z.goodLabel T g=t) :
    goodInput Z.n Z.width f Ht count levels t (encode field 3 x)=none := by
  have no_ := mt (DescentIssuedGoodHeaders.root_fields Z T v hi t old mode (x 1).val (x 2).val depthAt sampled).mp empty
  simp only [goodInput,Equiv.symm_apply_apply]
  unfold DescentIssuedGoodHeaders.key
  simp only [Fin.isValue, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ite_false, ite_eq_right no_]

variable {N : ℕ} (ids : A.graph.Edge↪Fin N) (batch p : ℕ) (hp : 0<p) (scale : Z.unit=batch*p)
local notation "sel" => selected (R) Z.graph Z.positive Z.pay Z.circuit
set_option quotPrecheck false in
local notation "dev" => device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d)

def goodRotorSite (s : Bool) (g : (R).Good) (actor : (dev (sel s (.inl g))).Site) :
    (DescentCommonPalette.rotor Z.graph).Site :=
  let layers := selectedRotorLayers (R) Z.graph Z.positive Z.pay Z.circuit s g
  (DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm actor

theorem good_card (s : Bool) (g : (R).Good) (actor : (dev (sel s (.inl g))).Site) (count : ℕ)
    (unit : 0<Z.unit) :
    amount Z.graph C Z.width batch (.rotor (goodRotorSite Z s g actor)) (Z.rotorKey T unit count s g)=
      Fintype.card (Z.laneRecipe ids batch p hp scale ⟨(s,.inl g),actor⟩).Node := by
  change _=Fintype.card (Z.laneProgram ids batch p hp scale ⟨(s,.inl g),actor⟩).Node
  symm
  refine (DescentBatchedBank.sized_funds Z.graph Z.positive Z.unit batch p hp scale
    (R).contact (R).input (R).site (R).owner (R).align ids d sel ⟨(s,.inl g),actor⟩).trans ?_
  let layers := selectedRotorLayers (R) Z.graph Z.positive Z.pay Z.circuit s g
  let bare := (DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm actor
  change Rotor.funded Z.graph C Z.width batch layers bare =
    Rotor.funded Z.graph C Z.width batch (Z.circuit s g).layers bare
  exact congrArg (fun l => Rotor.funded Z.graph C Z.width batch l bare)
    (selectedRotorLayers_eq (R) Z.graph Z.positive Z.pay Z.circuit s g)


end
end Hierarchy.DescentPaidResidentCount.Reset.BankIssue

namespace Hierarchy.DescentPaidResidentCount.Reset
open BankIssue DescentRotorRootPresence DescentResetHostSize DescentColonies DescentPacking.PackedMatch.Local.Gather DescentSIMDLookup
open DescentSixParty DescentCompiler DescentKernelHistory DescentHostDirectory
open DescentResetTrunks DescentStageEdgeReceipt DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
variable {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl) (issued : b.Recorded p)
local notation "key" => (DescentOrderedReset.grains W b.count b.order)
local notation "vertex" => (b.frame.host.symm.toEmbedding.trans cap.vertex)
local notation "rank" => ((b.reset.rawHostRank b.terminals vertex).trans Fin.valEmbedding)
local notation "rows" => (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) rank)
local notation "ps" => (DescentPhysicalOrder.rename (b.raw.siteFrom rows b.valid.coordinates))
local notation "rawId" => ((b.reset.nativeResetEdges b.terminals vertex key).order.trans Fin.valEmbedding)
local notation "pe" => (DescentPhysicalOrder.rename (DescentResetLocalOrder.allCode b.raw rawId S
  b.valid (b.raw.siteFrom rows b.valid.coordinates)))

local notation "bank" => b.reset.laneRecipe key (b.reset.unit/p) p issued.positive (Nat.div_mul_cancel issued.divides).symm
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "R" => b.reset.placement
local notation "depth" => b.terminals.commonDepth
local notation "res" => b.reset.k-depth
local notation "Dvc" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit (R).contact (R).input (R).site (R).owner (R).align (D:=d)
local notation "Sel" => DescentChosenRouter.selected (R) (Z).graph (Z).positive (Z).pay (Z).circuit

/-- Occupancy of a real bank actor already certifies that its good root exists. Its
number of paid operations then depends only on the common previously recorded capacity. -/
theorem middle_good_fixed (s : Bool) (g₀ : (R).Good) (actor : (Dvc (Sel s (.inl g₀))).Site) :
    Rotor.funded (Z).graph C (Z).width ((Z).unit/p)
      (DescentRecordedRotorLayers.layers (Z).n (Z).width f cap.placement.cap) (goodRotorSite (Z) s g₀ actor)=
      payee b issued (.inr ⟨(s,.inl g₀),actor⟩) := by
  have unit : 0<(Z).unit:=by rw [b.unit,←cap.grain];exact Nat.mul_pos cap.placement.unitPos G.base_pos
  have calendar:=(DescentRecordedRotorLayers.from_prior_cap b issued s g₀ cap.placement.cap rfl).1
  rw [←calendar]
  exact good_card (Z) T key ((Z).unit/p) p issued.positive (Nat.div_mul_cancel issued.divides).symm s g₀ actor 0 unit

/-- The original middle word for a rotor root holds exactly three fields. Its old
capacity picks the real recorded circuit layer count. -/
theorem middle_good_paid {field : ℕ} (count : ℕ) (s : Bool) (g₀ : (R).Good)
    (actor : (Dvc (Sel s (.inl g₀))).Site) (t : Code res) (x : Fin 3→Cell field)
    (priorCap : (x 0).val=cap.placement.cap) (old : Block res→ℕ)
    (depthAt : (x 1).val=(R).b ((Z).rootVertex T (.inl g₀))-depth+1)
    (sampled : (x 2).val%2=old (sample t)%2)
    (mode : ∀a,old a%2=Bool.toNat (decide ((R).hub ((Z).rootVertex T (.inl g₀)) ∨
      (((Z).rootVertex T (.inl g₀)),DescentColonies.group ((R).b ((Z).rootVertex T (.inl g₀)))
        (DescentIssuedFallbackPanel.join (((T).commonLow ((Z).rootVertex T (.inl g₀))).trans ((R).depth ((Z).rootVertex T (.inl g₀)))) ((Z).rootBlock T (.inl g₀)) a))∈(R).keys)))
    (tag : (Z).goodLabel T g₀=t) :
    amount (Z).graph C (Z).width ((Z).unit/p) (.rotor (goodRotorSite (Z) s g₀ actor))
      (goodInput (Z).n (Z).width f (GroupStage.depthBound D n f g) count (Z).layerBits t (encode field 3 x))=
      payee b issued (.inr ⟨(s,.inl g₀),actor⟩) := by
  have unit : 0<(Z).unit:=by rw [b.unit,←cap.grain];exact Nat.mul_pos cap.placement.unitPos G.base_pos
  have layers:=(DescentRecordedRotorLayers.from_prior_cap b issued s g₀ (x 0).val priorCap).1
  rw [goodInput_key (Z) T unit f count s g₀ _ _ t old x depthAt sampled mode rfl rfl tag layers]
  exact good_card (Z) T key ((Z).unit/p) p issued.positive (Nat.div_mul_cancel issued.divides).symm s g₀ actor count unit

end
end Hierarchy.DescentPaidResidentCount.Reset

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "here" => donor digits frm.basis fit
local notation "ord" => frm.host.symm.toEmbedding.trans vertex
local notation "amountFit" => (2^Ht:ℕ)
local notation "Δ" => A.degree
local notation "short" => fun t : Z.Fallback=>shortName c (T.code t)
local notation "shape" => chartShape A S ready Z T
local notation "hostAt" => fun t : Z.Fallback=>frm.host.symm (Prod.fst (T.code t))
local notation "rootAt" => selectedRoot A S ready Z T
local notation "arr" => leafPanel A S ready digits native Z T frm
variable (n f B wire K : ℕ) (wt : V→Block m→ℕ) (flow : V→V→Block m→ℝ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near n f B wire K flow A.degree wt)
variable (bank : DescentSharedBookScan.Chart) (source : Memory w) (target : ℕ)
variable (header : fixed bank (Z.k-T.commonDepth) (2^Z.n) A.degree H source)
    (safe : Room bank (Z.k-T.commonDepth) (2^Z.n) A.degree H w target)
variable (table : DescentNativeFallbackShapes.Stored bank.shapes (Z.k-T.commonDepth) (32*Nat.clog 2 (2*A.degree)) g f
    (2^Z.n) (2^Ht) source)
variable (old : ∀ (u : V) (j : Fin A.degree),source (bank.neighbors.base+((vertex u).val*A.degree+j.val))=
    (hostDigit vertex (hostRoster A (vertex.trans Fin.valEmbedding) u j):Word w))
variable (hub : ∀u,source (bank.isHub.base+(vertex u).val)=((A.hub u).toNat:Word w))
variable (ww : 0<w) (bitsFit : Ht+2≤w)
variable (avail : ∀t : Z.Fallback,∀i z,z∈DescentFallbackLeafScan.localShape (Z.k-T.commonDepth)
    (32*Nat.clog 2 (2*A.degree)) g f (shortName T.commonDepth (T.code t)).2 i→shapeNumber z+1<2^w)
variable (encoded : ∀t : Z.Fallback,shapeNumber (shortName T.commonDepth (T.code t)).2<2^w)
local notation "rank" => ranks (a:=r) («Y»:=Y) («D»:=Δ) bank amountFit (Ht+2) source
variable (word : Host J V k→ℕ) (room : ∀u,word u+1<2^field)
variable (onWire : ∀s (e : Grain A),word (home A (endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (endSite A s e)))
variable (signBits : DescentSignedCableCodec.width A.degree A.cap≤field) (countBits : Ht+2≤field)
local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
variable (allSites : ∀ (v : V) (hi : Block T.commonDepth) (lo : Fin (2^(m-T.commonDepth))),
    word (donor digits frm.basis (frm.enough.trans (Nat.sub_le ..)) v hi lo)/2 =
      Stencil.shapeCode (m-T.commonDepth) (2^Z.n) (fieldsRelative T.commonDepth
        (DescentPlainTerminal.endpoint A.near (fun u => Z.placement.b (frm.host u))
          frm.basis wt f (32*Nat.clog 2 (2*A.degree)) B g (2^Z.n) roster.2.2.2.2.2.choose
          (fun u j => (frm.host u,j) ∈ Z.placement.keys) A.hub v
          ((rearrange frm.basis).symm (join (frm.enough.trans (Nat.sub_le ..)) hi lo)))))

open DescentPaidResidentCount.Reset.BankIssue DescentPaidResidentCount.Reset DescentMixedRouter
local notation "cfg" => DescentChosenRouter.selected Z.placement Z.graph Z.positive Z.pay Z.circuit
set_option quotPrecheck false in
local notation "net" => device Z.graph Z.positive Z.unit Z.placement.contact Z.placement.input Z.placement.site
  Z.placement.owner Z.placement.align (D:=d)
set_option quotPrecheck false in
local notation:max "ticket" t:arg => (Z.fallLabel T t,(T.code t).2.2)

include roster safe header table old hub ww bitsFit avail encoded allSites room onWire signBits countBits in
theorem middle_tree_card {N : ℕ} (key : (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)).graph.Edge↪Fin N)
    (batches p : ℕ) (hp : 0<p) (unit : 0<Z.unit) (scale : Z.unit=batches*p)
    (side : Bool) (t : Z.Fallback) (actor : (net (cfg side (.inr t))).Site) :
    amount Z.graph C Z.width batches (fundedSite A S ready Z T side (.inr t) actor)
      (treeInput (levels:=0) side (ticket t) (DescentFallbackPeriod.encodePacket (win (hostAt t) (rootAt t))))=
      Fintype.card (Z.laneRecipe key batches p hp scale ⟨(side,.inr t),actor⟩).Node := by
  have measured:=fallback_key A S ready digits native Z T frm groupKey vertex n f B wire K wt flow roster
    bank source target header safe table old hub ww bitsFit avail encoded word room onWire signBits countBits allSites side t
  have fund:=bank_paid A S ready digits native Z T frm key batches p hp unit scale ord side (.inr t) actor
  rw [Z.rootsOf_read] at fund
  rw [treeInput_amount_levels Z.graph C Z.width batches 0 Z.layerBits,treeInput_read,measured]
  exact fund.symm

include roster safe header table old hub ww bitsFit avail encoded allSites room onWire signBits countBits in
omit header safe table old hub ww bitsFit avail encoded onWire signBits countBits in
theorem middle_tree_empty (side : Bool) (t : Code r×Option (Fin Y)) (v : V) (hi : Block c)
    (absent : Z.atRoot T ord (vertex v,hi,.inr t)=none)
    (batches : ℕ) (role : Site Z.graph Ht) :
    amount Z.graph C Z.width batches role (treeInput (levels:=0) side t (DescentFallbackPeriod.encodePacket (win v hi)))=0 := by
  rw [treeInput_amount_levels Z.graph C Z.width batches 0 Z.layerBits,treeInput_read]
  have empty:=fallback_ghost A S ready digits native Z T frm groupKey vertex n f B wire K wt flow roster bank source word room allSites side t v hi absent
  rw [empty]
  rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
