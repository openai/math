import OAI.Hierarchy.DescentRecordedActorsAfterRoots
import OAI.Hierarchy.DescentDatedActorAperture
import OAI.Hierarchy.DescentResetNewActorDirectory

namespace OAI
/-! Feed the actual published stencil and retained old geometry through the prepared root pages
and use their attained shared count table to print the new actors on the very same RAM. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentDatedAddressBook DescentActorRaster
open DescentCompiler DescentGL DescentColonies DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentPacking.PackedMatch.Local DescentIssuedFallbackPanel
open ResetInput.SourceFrame DescentDenseHostOrder DescentCommonHost DescentPackedZip
open DescentActorRaster.CPU Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "width" => S.groupWidth k tail i+k
local notation "cc" => reset.terminals.commonDepth
local notation "oldDepth" => fun v=>reset.reset.placement.b (reset.frame.host v)
local notation "oldBad" => fun v j=>(reset.frame.host v,j)∈reset.reset.placement.keys
local notation "symNear" => fun v u (hit:u∈(A).near v)=>((A).symmetric v u).mp hit
local notation "rcp" => fun v u (hit:u∈(A).mutual v)=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hit).2,(Finset.mem_filter.mp hit).1⟩

local notation "peer" => PackedFlow.portAt A ((A).numberedHeader sourceDigits input.vertex).site
local notation "hw" => DescentCommonPalette.rotor reset.reset.graph
local notation "Y" => 2^reset.reset.n
local notation "Shape" => Node Unit (Unit×DescentContacts.Endpoint Y) (hw).Site
local notation "lev" => levelAt reset.frame f peer
local notation "op" => opcode (width-cc)
variable {nbits t a : ℕ}
  (level : S.groupWidth k tail i + k - reset.terminals.commonDepth < 2^nbits) (one : 1 < 2^nbits)
  (capacity : 2^(S.groupWidth k tail i + k - reset.terminals.commonDepth) *
    (input.placement.wire * (input.placement.z * G.b) * input.placement.cap) < 2^nbits)
  (shapeRoom : 2 * DescentFallbackShapeTable.rows (S.groupWidth k tail i + k - reset.terminals.commonDepth)
    (2^reset.reset.n) ≤ 2^t)
  (positive : 0 < input.placement.wire * (input.placement.z * G.b) * input.placement.cap)
  (quota : 0 < DescentCompiler.quota S.rounds) (degPos : 0 < 32 * Nat.clog 2 (2 * input.placement.degree))
local notation "stencil" => realPanel (reset:=reset) rfl reset.frame.basis nbits t

open DescentActorRaster
variable {H M w : ℕ} (previous : Fintype.card input.V≤H)
local notation "Q" => (DescentDenseHostOrder.roster reset.reset.graph (reset.reset.k-reset.terminals.commonDepth) (GroupStage.depthBound D n f g)).card
local notation "qs" => Window.shapes reset
local notation "rack" => Window.rack reset previous
local notation "idx" => input.vertex.trans (Fin.castLEEmb previous)
local notation "oldRank" => (reset.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb previous)
local notation "id" => reset.reset.rawHostRank reset.terminals oldRank
local notation "Yd" => (A).degree
local notation "common" => reset.terminals.commonDepth
local notation "rr" => reset.reset.k-common
local notation "arity" => DescentSharedBookScan.width rr Y Yd
local notation "used" => Fintype.card input.V
local notation "prev" => fun v=>reset.reset.placement.b (reset.frame.host v)
local notation "heightBound" => GroupStage.depthBound D n f g
local notation "capBook" => 2^heightBound
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSixParty.Chronology
variable (pop raw line : Bank)
variable {cap nn N G₀ K₀ R hh ll field : ℕ}
    (Q₀ : Receiver input.placement.degree cap N reset.reset.n
      (reset.reset.k - reset.terminals.commonDepth) reset.terminals.commonDepth H G₀ K₀ R M hh ll t field
      (GroupStage.depthBound D n f g) w)
    (bk : RootBook reset.reset.n (reset.reset.k - reset.terminals.commonDepth) input.placement.degree
      (2^(reset.reset.k-reset.terminals.commonDepth)) cap field)
    (safe : Q₀.PreparedFits bk)
local notation "base" => Q₀.preparedEnd bk
local notation "U" => (⟨H,cc,width-cc,M,t,a,Q,arity,width,Yd*capBook⟩ : ActorSetup)
local notation "chart" => bk.common Q₀.projectionEnd H
local notation "C₀" => DescentSharedBookScan.expr chart H Yd capBook
local notation "st" => (ProtocolRAM.Expr.lookup line .row)
local notation "ops" => fun j=>headerControl rr Yd (qs j)
local notation "choice" => fun j=>op (qs j)
local notation "L" => (U).gate base

include accepted level one capacity shapeRoom positive quota degPos in
theorem directory_after_roots (measured : Memory w) (page : RootPage rr Y)
    (stencilWords : PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) M t line.base idx (stencil) measured)
    (catalog : bk.fallbackDegree=32*Nat.clog 2 (2*Yd) ∧ bk.hubBits=g ∧ bk.loadBits=f ∧ bk.shapes=capBook)
    (ports : ∀u j,measured (bk.previousNeighbors.base+((idx u).val*Yd+j.val))=
      (DescentFallbackRankRAM.hostDigit idx (peer u j):Word w))
    (flags : ∀u,measured (bk.previousHubs.base+(idx u).val)=(((A).hub u).toNat:Word w))
    (count : measured pop.base=(used:Word w))
    (depth : ∀v,measured (raw.base+(idx v).val*(width+1))=(prev v:Word w))
    (ww : 0<w) (cardFit : Yd*capBook<2^w)
    (shapesFit : ∀z : DescentContacts.Endpoint Y,z.1.2<2^z.1.1→z.1.1≤rr→∀i h',
      h'∈DescentFallbackLeafScan.localShape rr (32*Nat.clog 2 (2*Yd)) g f z i→DescentFallbackShapeTable.shapeNumber h'+1<2^w)
    (hostRange : used<2^w) (bounded : ∀v,prev v≤width)
    (limit : ∀j v,lev v (qs j)+1<2^a)
    (popLow : pop.Fits w Q₀.origin) (depthLow : raw.Fits w Q₀.origin) (depthRows : H*(width+1)≤raw.size)
    (lineLow : line.base+H*chunks (2^cc) M≤Q₀.origin) (lineFit : line.Fits w base)
    (lineRows : H*chunks (2^cc) M≤line.size)
    (peerLow : bk.previousNeighbors.Fits w Q₀.origin) (peerSize : H*Yd≤bk.previousNeighbors.size)
    (hubLow : bk.previousHubs.Fits w Q₀.origin) (hubSize : H≤bk.previousHubs.size)
    (hostsFit : H<2^w) (degreeFit : Yd+1<2^w) (room : base<2^w)
    (countsFit : (C₀).Fits w base) (gateFits : (U).GateFits base pop ops st w)
    (accessible : ∀j : Fin Q,DescentSharedLeafLookup.Readable (HeaderGate.header L H (2^cc) M a j)
      1 H (2^cc) M a w (L).gateBase) (lanes : 0<M) (lanesFit : M≤w)
    (cells : chunks (2^cc) M≤2^w) (endFit : (U).directoryEnd base<2^w) :
    let scene:=(U).scene base
    let directory:=(U).directory base
    let cpu:=((U).headers base raw C₀ w).seq ((U).operator base pop ops choice st (w:=w))
    let ticks:=(U).headerTime base raw C₀ w+(U).operatorTime base pop ops choice st w
    ∃dst,(((Q₀.preparedRoots bk safe).seq cpu).seq (directory.program w scene)).Exec measured dst
        ((Q₀.preparedTicks bk safe+ticks)+directory.ticks scene) ∧
      dst directory.count.base=(Fintype.card reset.next.V:Word w) ∧
      (∀v : reset.next.V,dst (directory.inverse.base+(reset.reset.denseHostRank reset.terminals oldRank v).val)=((id v).val:Word w)) ∧
      (∀v : reset.next.V,dst (directory.ranks.base+(id v).val)=((reset.reset.denseHostRank reset.terminals oldRank v).val:Word w)) ∧
      (∀j : Fin (H*Q),dst (directory.flags.base+j.val)=if ∃v,id v=j then 1 else 0) ∧
      (∀z,z<Q₀.origin ∨ (U).directoryEnd base≤z→dst z=measured z) ∧
      ∃mid,dst=directory.result scene mid ∧
        (∀(j : Fin Q) (p : Row H (2^cc) M),mid (scene.base+j.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val)=
          ((data (realActor (reset:=reset) qs rack j) p).val:Word w)) ∧
        (∀z,z < base → mid z=Q₀.preparedImage bk safe measured z) ∧
        (∀v,mid (((U).depths base).base+(idx v).val)=(prev v:Word w)) ∧
        ∀d,d < ((U).levels base).size → mid (((U).levels base).base+d)=((d-cc+1:ℕ):Word w) :=by
  intro scene directory cpu ticks
  have occurs (h : Fin H) : h.val<used↔∃v,rack h=some v:=by
    rw [DescentHostCount.prefix_live input.vertex previous h]
    constructor
    · rintro ⟨v,hv⟩
      have loc:oldRank (reset.frame.host v)=h:=by simpa using hv
      refine ⟨v, ?_⟩
      rw [←loc]
      change (ResetInput.rackAt oldRank (oldRank (reset.frame.host v))).map reset.frame.host.symm = some v
      rw [ResetInput.rackAt_known]
      simp
    · rintro ⟨v,hv⟩
      obtain ⟨u,hit,same⟩:=Option.map_eq_some_iff.mp hv
      exact ⟨v,by simpa [←same] using ResetInput.rackAt_some oldRank hit⟩
  have addr (h : Fin H) (v : input.V) (hit:rack h=some v) : idx v=h:=by
    obtain ⟨u,raw,same⟩:=Option.map_eq_some_iff.mp hit
    simpa [←same] using ResetInput.rackAt_some oldRank raw
  have inv (v : input.V) : rack (idx v)=some v:=by
    have loc : oldRank (reset.frame.host v)=idx v:=by simp
    change (ResetInput.rackAt oldRank (idx v)).map reset.frame.host.symm = some v
    rw [←loc, ResetInput.rackAt_known]
    simp
  obtain ⟨mid,first,formed,keep,keepRoots,depths,levels⟩:=actors_after_roots accepted level one capacity shapeRoom positive quota degPos
    qs rack idx pop raw line Q₀ bk safe measured page stencilWords catalog ports flags count depth occurs addr inv
    ww cardFit shapesFit hostRange bounded limit popLow depthLow depthRows lineLow lineFit lineRows peerLow peerSize hubLow
    hubSize hostsFit degreeFit room countsFit gateFits accessible
  have extent:(U).endAddress base≤(U).directoryEnd base:=by
    exact Nat.le_add_right ..
  have span:scene.Fits w ((U).endAddress base):=⟨Nat.two_pow_pos _,
    (by exact (Nat.le_add_left scene.size scene.base).trans_lt (extent.trans_lt endFit)),le_rfl⟩
  have measure:H*Q*chunks (2^cc) M≤ scene.size:=by
    simpa [scene,ActorSetup.chunksPerHost,ActorSetup.groups,Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm]
      using (U).extent_scene base
  obtain ⟨second,count,inv,rank,flags,lower⟩:=Window.paid_actor_result reset previous ((U).endAddress base)
    scene mid lanes lanesFit formed span measure cells endFit
  have low₀:Q₀.origin≤(U).endAddress base:=by
    have first:Q₀.headerEnd bk≤base:=Nat.le_add_right ..
    obtain ⟨r₁,r₂,r₃⟩:=bk.limits Q₀.projectionEnd H (2^common) M
    have pre:=Q₀.origin_le_projection.trans (r₁.trans (r₂.trans (r₃.trans first)))
    apply pre.trans
    dsimp only [ActorSetup.endAddress,ActorSetup.next,ActorSetup.scene,ActorSetup.gate,ActorSetup.heights,ActorSetup.levels,
      ActorSetup.starts,ActorSetup.counts,ActorSetup.depths,ActorSetup.bank,DescentSharedLeafLookup.Public.stop]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  exact ⟨_,first.then second,count,inv,rank,flags,(fun z away=>(lower z (away.imp_left (·.trans_le low₀))).trans
    (keep z (away.imp_right (extent.trans ·)))),mid,rfl,formed,keepRoots,depths,levels⟩
end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
