import OAI.Hierarchy.DescentClosedFallbackPay
import OAI.Hierarchy.DescentFundedIssuedValues
import OAI.Hierarchy.DescentIssuedFallbackRoot
import OAI.Hierarchy.DescentResetStemClosedWindow

namespace OAI
/-! # The two directed fallback root registers in the funded atlas -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentPacking.PackedMatch.Local.Stage
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field slots : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groups : J↪ℕ) (vertex : V↪Fin H)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
    (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht) (T : Z.Terminals)
    (frm : Z.SourceFrame T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "here" => donor digits frm.basis fit
local notation "short" => fun t : Z.Fallback =>shortName c (T.code t)
local notation "D" => 32*Nat.clog 2 (2*A.degree)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groups ids)

/-- Short stencil digits on a physical predecessor, at the true reached price and
cable multiplicities. Only the compact old endpoint, basis and root labels enter. -/
def observedStencil (s : Bool) (u : Host J V k) : ℕ :=
  let old:=(frm.host u.1.2,Fin.cast (congrArg (fun j=>2^j) frm.extent.symm) (oldBlock digits u))
  let t:=Z.placement.fall s old
  2*DescentFallbackShapeTable.cell r (short t).2+
    (decide (baseOf Z.placement.b Z.placement.depth Z.placement.L old∈validBases Z.placement.b Z.placement.keys ∨
      Z.placement.hub old.1)).toNat

/-- Original scalar RAM and packed signed/stencil sheets before the root lookup.
Rows outside the received host embedding may be arbitrary. -/
structure RootObservation (field : ℕ) where
  n : ℕ
  f : ℕ
  B : ℕ
  wire : ℕ
  K : ℕ
  wt : V→Block m→ℕ
  flow : V→V→Block m→ℝ
  roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near n f B wire K flow A.degree wt
  precision : ℕ
  chart : DescentSharedBookScan.Chart
  memory : Memory precision
  cutoff : ℕ
  header : fixed chart r Y A.degree H memory
  room : Room chart r Y A.degree H precision cutoff
  layouts : DescentNativeFallbackShapes.Stored chart.shapes r D g f Y (2^Ht) memory
  peers : Fin H→Fin A.degree→Option (Fin H)
  rosterRead : ∀u j,peers (vertex u) j=(hostRoster A ids u j).map vertex
  old : ∀(u : V) (j : Fin A.degree),memory (chart.neighbors.base+((vertex u).val*A.degree+j.val))=
    (hostDigit vertex (hostRoster A ids u j):Word precision)
  hubs : ∀u,memory (chart.isHub.base+(vertex u).val)=((A.hub u).toNat:Word precision)
  pos : 0<precision
  heightFits : Ht+2≤precision
  available : ∀t : Z.Fallback,∀i z,z∈DescentFallbackLeafScan.localShape r D g f (short t).2 i→shapeNumber z+1<2^precision
  encoded : ∀t : Z.Fallback,shapeNumber (short t).2<2^precision
  word : Host J V k→ℕ
  wordFits : ∀u,word u+1<2^field
  onWire : ∀s (e : Grain A),word (home A (endSite A s e))=observedStencil A digits Z T frm s (home A (endSite A s e))
  signedFits : DescentSignedCableCodec.width A.degree A.cap≤field
  countFits : Ht+2≤field
  allSites : ∀(v : V) (hi : Block T.commonDepth) (lo : Fin (2^(m-T.commonDepth))),word (here v hi lo)/2=
    Stencil.shapeCode (m-c) Y (fieldsRelative c ((DescentPlainTerminal.endpoint A.near
      (fun v=>Z.placement.b (frm.host v)) frm.basis wt f D B g Y roster.2.2.2.2.2.choose
      (fun v j=>(frm.host v,j)∈Z.placement.keys) A.hub) v ((rearrange frm.basis).symm (join fit hi lo))))
  stencil : Fin H→Block c→Fin L→ℕ
  marks : Fin H→Block c→Fin L→Fin (2*A.cap)→Option (Live A.degree A.cap)
  stencilRead : ∀v hi lo,stencil (vertex v) hi lo=word (here v hi lo)
  markRead : ∀v hi lo j,marks (vertex v) hi lo j=signedPanel A native S ready names (here v hi lo) j

section Packed
variable {A S ready digits native groups vertex Z T frm}

def RootObservation.packed (a : RootObservation A S ready digits native groups vertex Z T frm field)
    (v : Fin H) (hi : Block c) :=
  let rank:=ranks (a:=r) («Y»:=Y) («D»:=A.degree) a.chart (2^Ht) (Ht+2) a.memory
  DescentFallbackPeriod.encodePacket
    (DescentFallbackPeriod.inputs (field:=field) a.stencil a.peers a.marks (fun u j=>(rank u j).val) v hi)

end Packed

section Nominal
variable (R : ResetInput (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T₀ : R.Terminals)
    (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) R T₀ (fun u : W.graph.Site => (A.pos u).2)
      (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    {H' : ℕ} (room : H≤H')
local notation "pad" => vertex.trans (Fin.castLEEmb room)
variable (a : RootObservation A S ready digits native groups (vertex.trans (Fin.castLEEmb room)) R T₀ frame field)

theorem root_observed (t : R.Fallback) :
    TreeMiddleRead A S ready digits native groups vertex h C Ht g field A.z A.wire A.grainCount
      (A.grainCount_fit S ready) R T₀ frame t (a.packed (pad (frame.host.symm (T₀.code t).1)) (R.rootBlock T₀ (.inr t))) :=by
  let previous : TreeInputSnapshot (field:=field) A S ready digits R T₀ frame pad :=
    ⟨a.n,a.f,a.B,a.wire,a.K,a.wt,a.flow,a.roster,a.precision,a.chart,a.memory,a.cutoff,a.header,a.room,
      a.layouts,a.old,a.hubs,a.pos,a.heightFits,a.available,a.encoded,a.word,a.wordFits,a.onWire,
      a.signedFits,a.countFits,a.allSites⟩
  have measured:=window_input (field:=field) A S ready digits native R T₀ frame groups pad a.word
    (ranks (a:=R.k-T₀.commonDepth) («Y»:=2^R.n) («D»:=A.degree) a.chart (2^Ht) (Ht+2) a.memory)
    a.stencilRead a.rosterRead a.markRead (frame.host.symm (T₀.code t).1) (R.rootBlock T₀ (.inr t))
  simp only [RootObservation.packed]
  rw [measured]
  exact .padded room R T₀ frame t previous

end Nominal
end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentSIMDLookup DescentGL DescentColonies DescentSharedCableNames.Stage
open DescentStageEdgeReceipt DescentResetHostSize DescentCompiler
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail H field : ℕ}
  {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl) (room : Fintype.card cap.V≤H)
local notation "A" => cap.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "oldKey" => B.order.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "host" => cap.vertex.trans (Fin.castLEEmb room)
local notation "height" => GroupStage.depthBound D n f g
local notation "cc" => (T).commonDepth
local notation "extent" => S.groupWidth k tail i+k
local notation "rel" => ((Z).k-cc)
local notation:max "v₀" t:arg => host (B.frame.host.symm ((T).code t).1)
local notation:max "hi₀" t:arg => (Z).rootBlock T (.inr t)

/-- The same prior word already authenticated by the closed signed stem receiver. -/
theorem observed_stencil (s : Bool) (u : Host (Fin (S.groupCount i)) cap.V k) :
    GroupStage.observedStencil A digits Z T B.frame s u=ClosedReset.Window.signedStemWord B s u :=rfl

abbrev PaddedSnapshot (field : ℕ) :=
  GroupStage.RootObservation A S cap.valid digits oldKey groupKey host Z T B.frame field

/-- The reached equality of the old width and count transports the original input
packet together with its observed predecessor chart. Neither directed output
nor a population of the new tree is an input. -/
theorem observed_at (snap : PaddedSnapshot B room field) (t : (Z).Fallback) :
    Original B (field:=field) t (snap.packed (v₀ t) (hi₀ t)) := by
  refine ⟨rfl,?_⟩
  let Fam:=fun (zz ww : ℕ) (ct:W.graph.Edge→ℕ) (ok:∀e,W.graph.width e=ct e*(zz*G.b))=>
    ∀(R:ResetInput (W.granular ct (zz*G.b) ok) (q*ww) ε h C height) (T₀:R.Terminals)
    (frame:R.SourceFrame T₀ (fun u=>((A).pos u).2) (StarKeys.filled W.graph (A).pos (A).block digits) (A).hub g)
    (a:GroupStage.RootObservation A S cap.valid digits oldKey groupKey host R T₀ frame field)
    (t:R.Fallback),GroupStage.TreeMiddleRead A S cap.valid digits oldKey groupKey cap.vertex h C height g field
      zz ww ct ok R T₀ frame t (a.packed (host (frame.host.symm (T₀.code t).1)) (R.rootBlock T₀ (.inr t)))
  have atOld : ∀ok,Fam (A).z (A).wire (A).grainCount ok:=by
    intro ok R T₀ frame a t
    exact GroupStage.root_observed A S cap.valid digits oldKey groupKey cap.vertex R T₀ frame room a t
  exact (liftStage B (Fam:=Fam) atOld) Z T B.frame snap t

/-- The real gathered input can use the reset's residual dimension. The cast is just
the reached key-width equality and leaves its bits intact. -/
def savedInput (snap : PaddedSnapshot B room field) (h₀ : Fin H) (hi : Block cc) :
    Cell (field*DescentFallbackPeriod.inputCount (A).degree (2^rel) (A).cap (Z).n rel) :=
  Fin.cast (by rw [B.keyWidth]) (snap.packed h₀ hi)

theorem saved_input_eq (snap : PaddedSnapshot B room field) (h₀ : Fin H) (hi : Block cc) :
    (savedInput B room snap h₀ hi).val=(snap.packed h₀ hi).val :=rfl

/-- Readback for Window.Observed.root at either true directed ticket, including a
null optional terminal or a legal height-zero tree. The same packed original
word feeds both directed finite root functions. -/
theorem root_input_observed (snap : PaddedSnapshot B room field)
    (middle : Bool → DescentResetHostSize.Code rel × Option (Fin (2^(Z).n))→Fin H→Block cc→
      Cell (field*DescentFallbackPeriod.inputCount (A).degree (2^rel) (A).cap (Z).n rel))
    (read : ∀s t,(middle s ((Z).fallLabel T t,((T).code t).2.2) (v₀ t) (hi₀ t)).val=
      (snap.packed (v₀ t) (hi₀ t)).val) :
    ∀s t,Original B (field:=field) (slots:=2^rel) t (middle s ((Z).fallLabel T t,((T).code t).2.2) (v₀ t) (hi₀ t)) :=by
  intro s t
  have eqn:2^rel=2^(extent-cc):=by rw [B.keyWidth]
  refine ⟨eqn,?_⟩
  have atOld:=observed_at B room snap t
  obtain ⟨_,prior⟩:=atOld
  convert prior using 1
  exact Fin.ext (read s t)

theorem saved_observed (snap : PaddedSnapshot B room field) :
    ∀s t,Original B (field:=field) (slots:=2^rel) t
      ((fun (_:Bool) (_:DescentResetHostSize.Code rel×Option (Fin (2^(Z).n)))=>savedInput B room snap)
        s ((Z).fallLabel T t,((T).code t).2.2) (v₀ t) (hi₀ t)) :=
  root_input_observed B room snap (fun _ _ => savedInput B room snap) (fun _ _=>rfl)

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
