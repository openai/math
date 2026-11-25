import OAI.Hierarchy.DescentPreparedBankPay

namespace OAI
/-! # Closing measured fallback populations across the preceding stage's actual grain and width equalities -/
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
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
local notation "D" => 32*Nat.clog 2 (2*A.degree)
local notation "hs" => hostRoster A ids
local notation "wireWord" => peerShapeWord A S ready digits Z T frm

/-- The original measured inputs to a fallback root, before its population is computed. -/
structure TreeInputSnapshot where
  n : ℕ
  f : ℕ
  B : ℕ
  wire : ℕ
  K : ℕ
  wt : V→Block m→ℕ
  flow : V→V→Block m→ℝ
  roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near n f B wire K flow A.degree wt
  bits : ℕ
  chart : DescentSharedBookScan.Chart
  memory : Memory bits
  target : ℕ
  header : fixed chart r Y Δ H memory
  safe : Room chart r Y Δ H bits target
  table : DescentNativeFallbackShapes.Stored chart.shapes r D g f Y amountFit memory
  old : ∀(u : V) (j : Fin A.degree),memory (chart.neighbors.base+((vertex u).val*Δ+j.val))=(hostDigit vertex (hs u j):Word bits)
  hubs : ∀u,memory (chart.isHub.base+(vertex u).val)=((A.hub u).toNat:Word bits)
  positive : 0<bits
  heightFits : Ht+2≤bits
  available : ∀t : Z.Fallback,∀i z,z∈DescentFallbackLeafScan.localShape r D g f (short t).2 i→shapeNumber z+1<2^bits
  encoded : ∀t : Z.Fallback,shapeNumber (short t).2<2^bits
  word : Host J V k→ℕ
  wordFits : ∀u,word u+1<2^field
  onWire : ∀s (e : Grain A),word (home A (endSite A s e))=wireWord s (home A (endSite A s e))
  signedFits : DescentSignedCableCodec.width A.degree A.cap≤field
  countFits : Ht+2≤field
  allSites : ∀(v : V) (hi : Block T.commonDepth) (lo : Fin (2^(m-T.commonDepth))),word (here v hi lo)/2=
    Stencil.shapeCode (m-c) Y (fieldsRelative c ((DescentPlainTerminal.endpoint A.near
      (fun v=>Z.placement.b (frm.host v)) frm.basis wt f D B g Y roster.2.2.2.2.2.choose
      (fun v j=>(frm.host v,j)∈Z.placement.keys) A.hub) v ((rearrange frm.basis).symm (join fit hi lo))))

set_option quotPrecheck false
local notation "SnapshotAt" => TreeInputSnapshot (field:=field) A S ready digits Z T frm vertex
def treeMiddle (a : SnapshotAt) (t : Z.Fallback) :=
  let rank:=ranks (a:=r) («Y»:=Y) («D»:=Δ) a.chart amountFit (Ht+2) a.memory
  DescentFallbackPeriod.encodePacket
    (fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex a.word rank ((hostAt) t) (rootAt t))

open DescentPaidResidentCount.Reset DescentPaidResidentCount.Reset.BankIssue DescentMixedRouter
local notation "cfg" => DescentChosenRouter.selected Z.placement Z.graph Z.positive Z.pay Z.circuit
local notation "net" => device Z.graph Z.positive Z.unit Z.placement.contact Z.placement.input Z.placement.site
  Z.placement.owner Z.placement.align («D»:=d)

theorem treeMiddle_card (a : SnapshotAt) {N : ℕ} (ids₀ : (Wold).graph.Edge↪Fin N) (batches p : ℕ)
    (hp : 0<p) (positive : 0<Z.unit) (scale : Z.unit=batches*p) (side : Bool) (t : Z.Fallback)
    (actor : (net (cfg side (.inr t))).Site) :
    amount Z.graph C Z.width batches (fundedSite A S ready Z T side (.inr t) actor)
      (treeInput (levels:=0) side (Z.fallLabel T t,(T.code t).2.2)
        (treeMiddle A S ready digits native Z T frm groupKey vertex a t))=
      Fintype.card (Z.laneRecipe ids₀ batches p hp scale ⟨(side,.inr t),actor⟩).Node :=
  middle_tree_card A S ready digits native Z T frm groupKey vertex a.n a.f a.B a.wire a.K a.wt a.flow a.roster
    a.chart a.memory a.target a.header a.safe a.table a.old a.hubs a.positive a.heightFits a.available a.encoded
    a.word a.wordFits a.onWire a.signedFits a.countFits a.allSites ids₀ batches p hp positive scale side t actor

/-- A read of the actual gathered register, indexed by the granular world and source frame.
Its sole constructor computes the whole encoded packet from the signed window and measured
root/leaf ranks. Payload counts and eventual device costs do not occur in the receipt. -/
inductive TreeMiddleRead (h C Ht g field : ℕ) :
    (zz ww : ℕ)→(ct : W.graph.Edge→ℕ)→(cut : ∀e,W.graph.width e=ct e*(zz*G.b))→
    (R : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht)→(T₀ : R.Terminals)→
    (R.SourceFrame T₀ (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)→
    R.Fallback→Cell (field*DescentFallbackPeriod.inputCount Δ (2^(m-T₀.commonDepth)) A.cap R.n (R.k-T₀.commonDepth))→Prop
  | observed (R : ResetInput (Wold) (q*A.wire) ε h C Ht) (T₀ : R.Terminals)
      (frame : R.SourceFrame T₀ (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
      (t : R.Fallback) (observedInput : TreeInputSnapshot (field:=field) A S ready digits R T₀ frame vertex) :
      TreeMiddleRead h C Ht g field A.z A.wire A.grainCount (A.grainCount_fit S ready) R T₀ frame t
        (treeMiddle A S ready digits native R T₀ frame groupKey vertex observedInput t)

  | padded {H' : ℕ} (room : H≤H') (R : ResetInput (Wold) (q*A.wire) ε h C Ht) (T₀ : R.Terminals)
      (frame : R.SourceFrame T₀ (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
      (t : R.Fallback) (snap : TreeInputSnapshot (field:=field) A S ready digits R T₀ frame
        (vertex.trans (Fin.castLEEmb room))) :
      TreeMiddleRead h C Ht g field A.z A.wire A.grainCount (A.grainCount_fit S ready) R T₀ frame t
        (treeMiddle A S ready digits native R T₀ frame groupKey (vertex.trans (Fin.castLEEmb room)) snap t)

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentKernelHistory DescentCompiler DescentSIMDLookup DescentHostDirectory DescentResetTrunks
open DescentPackedFallbackTree DescentMixedRouter DescentChosenRouter BankIssue DescentColonies
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age m h C Ht g field H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S age)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groupCode : J↪ℕ) (vertex : V↪Fin H)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
    {R : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht} {T : R.Terminals}
    {frm : R.SourceFrame T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g}
local notation "sel" => selected R.placement R.graph R.positive R.pay R.circuit
local notation "deviceAt" => device R.graph R.positive R.unit R.placement.contact R.placement.input
  R.placement.site R.placement.owner R.placement.align («D»:=d)
local notation "WordAt" => Cell (field*DescentFallbackPeriod.inputCount A.degree (2^(m-T.commonDepth))
  A.cap R.n (R.k-T.commonDepth))

/-- The transported grain count and wire price index all arguments together, including
the measured input word and the true fallback population. -/
theorem treeRead_paid {t : R.Fallback} {word : WordAt}
    (actual : GroupStage.TreeMiddleRead A S ready digits native groupCode vertex h C Ht g field zz ww ct cut R T frm t word)
    {N : ℕ} (ids : (W.granular ct (zz*G.b) cut).graph.Edge↪Fin N) (batches p : ℕ)
    (hp : 0<p) (positive : 0<R.unit) (scale : R.unit=batches*p) (side : Bool)
    (actor : (deviceAt (sel side (.inr t))).Site) :
    amount R.graph C R.width batches (.tree ⟨actor.1.val,lt_of_lt_of_le actor.1.isLt (Nat.succ_le_succ (T.bookHeight side t))⟩ actor.2)
      (treeInput (levels:=0) side (R.fallLabel T t,(T.code t).2.2) word)=
      Fintype.card (R.laneRecipe ids batches p hp scale ⟨(side,.inr t),actor⟩).Node := by
  cases actual with
  | observed Z T₀ frame t snap =>
    exact GroupStage.treeMiddle_card A S ready digits native Z T₀ frame groupCode vertex snap
      ids batches p hp positive scale side t actor
  | padded room Z T₀ frame t snap =>
    exact GroupStage.treeMiddle_card A S ready digits native Z T₀ frame groupCode (vertex.trans (Fin.castLEEmb room)) snap
      ids batches p hp positive scale side t actor

end
end Hierarchy.DescentPaidResidentCount.Reset

namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentKernelHistory DescentCompiler DescentSIMDLookup DescentHostDirectory DescentResetTrunks
open DescentMixedRouter DescentChosenRouter BankIssue
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false

private def moveInputs {E : Type} {ok : ℕ→(E→ℕ)→Prop} {x y x₀ y₀ : ℕ} {ct ct₀ : E→ℕ}
    {F : (z w : ℕ)→(c : E→ℕ)→ ok z c→Sort*}
    (eqZ : x₀=x) (eqW : y₀=y) (eqC : ct₀=ct) (old : ∀h,F x₀ y₀ ct₀ h) (cert : ok x ct) : F x y ct cert := by
  subst x;subst y;subst ct;exact old cert

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
    {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset cap ctl)
local notation "A" => cap.placement
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "dep" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "oldKey" => b.order.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "sel" => selected (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => device (Z).graph (Z).positive (Z).unit (Z).placement.contact (Z).placement.input
  (Z).placement.site (Z).placement.owner (Z).placement.align («D»:=d)
local notation "Raw" field => Cell (field*DescentFallbackPeriod.inputCount (A).degree L (A).cap (Z).n r)

/-- Transport whole dependent data, including the price, the original cable counts and both
requested physical fields, without choosing a new reached state. -/
def liftStage {Fam : (zz ww : ℕ)→(c : W.graph.Edge→ℕ)→(∀e,W.graph.width e=c e*(zz*G.b))→Sort*}
    (atStage : ∀h,Fam (A).z (A).wire (A).grainCount h) : Fam z w b.count b.fit :=
  moveInputs (ok:=fun zz ct=>∀e,W.graph.width e=ct e*(zz*G.b)) (F:=Fam)
    cap.grain cap.edges b.count_eq.symm atStage b.fit

abbrev Original {field slots : ℕ} (t : (Z).Fallback)
    (word : Cell (field*DescentFallbackPeriod.inputCount (A).degree slots (A).cap (Z).n r)) :=
  ∃e : slots=L,GroupStage.TreeMiddleRead (A) S cap.valid digits oldKey groupKey cap.vertex h C dep g field
    z w b.count b.fit (Z) T b.frame t (Fin.cast (congrArg (fun k=>2^(field*DescentFallbackPeriod.inputCount
      (A).degree k (A).cap (Z).n r)) e) word)

theorem middle_tree_paid (issued : b.Recorded p) (field : ℕ) (side : Bool) (t : (Z).Fallback)
    (actor : (dev (sel side (.inr t))).Site) {slots : ℕ}
    (word : Cell (field*DescentFallbackPeriod.inputCount (A).degree slots (A).cap (Z).n r))
    (prior : Original b (field:=field) (slots:=slots) t word) :
    amount (Z).graph C (Z).width ((Z).unit/p)
      (.tree ⟨actor.1.val,lt_of_lt_of_le actor.1.isLt (Nat.succ_le_succ ((T).bookHeight side t))⟩ actor.2)
      (treeInput (levels:=0) side ((Z).fallLabel T t,((T).code t).2.2) word)=
      payee b issued (.inr ⟨(side,.inr t),actor⟩) := by
  have positive : 0<(Z).unit:=by rw [b.unit,←cap.grain];exact Nat.mul_pos (A).unitPos G.base_pos
  obtain ⟨rfl,read⟩:=prior
  exact treeRead_paid (A) S cap.valid digits oldKey groupKey cap.vertex read key ((Z).unit/p) p
    issued.positive positive (Nat.div_mul_cancel issued.divides).symm side actor

/-- A model exposes the natural type of measured snapshots at the *same* frame. The
eliminator below returns the input from its signed gather, rather than a population. -/
structure Inputs (field : ℕ) (zz ww : ℕ) (ct : W.graph.Edge→ℕ) (cut₀ : ∀e,W.graph.width e=ct e*(zz*G.b))
    (R : ResetInput (W.granular ct (zz*G.b) cut₀) (q*ww) ε h C dep) (T₀ : R.Terminals)
    (frame : R.SourceFrame T₀ (fun u=>((A).pos u).2) (StarKeys.filled W.graph (A).pos (A).block digits) (A).hub g) where
  Snapshot : Type
  packed : Snapshot→R.Fallback→Cell (field*DescentFallbackPeriod.inputCount (A).degree
    (2^(S.groupWidth k tail i+k-T₀.commonDepth)) (A).cap R.n (R.k-T₀.commonDepth))
  prior : ∀a t,GroupStage.TreeMiddleRead (A) S cap.valid digits oldKey groupKey cap.vertex h C dep g field
    zz ww ct cut₀ R T₀ frame t (packed a t)

def originalInputs (field : ℕ) : Inputs b field z w b.count b.fit (Z) T b.frame := by
  let Fam := fun (zz ww : ℕ) (ct : W.graph.Edge→ℕ) (cut₀ : ∀e,W.graph.width e=ct e*(zz*G.b))=>
    ∀(R : ResetInput (W.granular ct (zz*G.b) cut₀) (q*ww) ε h C dep) (T₀ : R.Terminals)
      (frame : R.SourceFrame T₀ (fun u=>((A).pos u).2) (StarKeys.filled W.graph (A).pos (A).block digits) (A).hub g),
        Inputs b field zz ww ct cut₀ R T₀ frame
  have raw : ∀h₀,Fam (A).z (A).wire (A).grainCount h₀ := by
    intro h₀ R T₀ frame
    exact ⟨GroupStage.TreeInputSnapshot (field:=field) (A) S cap.valid digits R T₀ frame cap.vertex,
      fun a t=>GroupStage.treeMiddle (A) S cap.valid digits oldKey R T₀ frame groupKey cap.vertex a t,
      fun a t=>.observed R T₀ frame t a⟩
  exact (liftStage b (Fam:=Fam) raw) (Z) T b.frame

theorem middle_tree_fixed (issued : b.Recorded p) (field : ℕ) (input : (originalInputs b field).Snapshot)
    (side : Bool) (t : (Z).Fallback) (actor : (dev (sel side (.inr t))).Site) :
    amount (Z).graph C (Z).width ((Z).unit/p)
      (.tree ⟨actor.1.val,lt_of_lt_of_le actor.1.isLt (Nat.succ_le_succ ((T).bookHeight side t))⟩ actor.2)
      (treeInput (levels:=0) side ((Z).fallLabel T t,((T).code t).2.2) ((originalInputs b field).packed input t))=
      payee b issued (.inr ⟨(side,.inr t),actor⟩) :=
  middle_tree_paid b issued field side t actor _ ⟨rfl,(originalInputs b field).prior input t⟩

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
