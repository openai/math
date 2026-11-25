import OAI.Hierarchy.DescentRecordedActorHeaders
import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentRecordedIssuedStencil

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
variable {Q H M w : ℕ} (qs : Fin Q → Node Unit (Unit × DescentContacts.Endpoint (2^reset.reset.n))
    (DescentCommonPalette.rotor reset.reset.graph).Site) (rack : Fin H→Option input.V)
local notation "Yd" => (A).degree
local notation "common" => reset.terminals.commonDepth
local notation "rr" => reset.reset.k-common
local notation "arity" => DescentSharedBookScan.width rr Y Yd
local notation "used" => Fintype.card input.V
local notation "prev" => fun v=>reset.reset.placement.b (reset.frame.host v)
local notation "heightBound" => GroupStage.depthBound D n f g
local notation "capBook" => 2^heightBound
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSixParty.Chronology
variable (idx : input.V↪Fin H) (pop raw line : Bank)
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
theorem actors_after_roots (measured : Memory w) (page : RootPage rr Y)
    (stencilWords : PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) M t line.base idx (stencil) measured)
    (catalog : bk.fallbackDegree=32*Nat.clog 2 (2*Yd) ∧ bk.hubBits=g ∧ bk.loadBits=f ∧ bk.shapes=capBook)
    (ports : ∀u j,measured (bk.previousNeighbors.base+((idx u).val*Yd+j.val))=
      (DescentFallbackRankRAM.hostDigit idx (peer u j):Word w))
    (flags : ∀u,measured (bk.previousHubs.base+(idx u).val)=(((A).hub u).toNat:Word w))
    (count : measured pop.base=(used:Word w))
    (depth : ∀v,measured (raw.base+(idx v).val*(width+1))=(prev v:Word w))
    (occurs : ∀h,h.val<used↔∃v,rack h=some v) (addr : ∀h v,rack h=some v→idx v=h)
    (inv : ∀v,rack (idx v)=some v)
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
      1 H (2^cc) M a w (L).gateBase) :
    ∃dst,((Q₀.preparedRoots bk safe).seq (((U).headers base raw C₀ w).seq
      ((U).operator base pop ops choice st (w:=w)))).Exec measured dst
      (Q₀.preparedTicks bk safe+((U).headerTime base raw C₀ w+(U).operatorTime base pop ops choice st w)) ∧
      (∀(j : Fin Q) (p : Row H (2^cc) M),dst (((U).scene base).base+j.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val)=
        ((data (realActor (reset:=reset) qs rack j) p).val:Word w)) ∧
      (∀z,z<Q₀.origin ∨ (U).endAddress base≤z→dst z=measured z) ∧
      (∀z,z < base → dst z=Q₀.preparedImage bk safe measured z) ∧
      (∀v,dst (((U).depths base).base+(idx v).val)=(prev v:Word w)) ∧
      ∀d,d < ((U).levels base).size → dst (((U).levels base).base+d)=((d-cc+1:ℕ):Word w) :=by
  let root:=Q₀.preparedImage bk safe measured
  obtain ⟨program,_,hold⟩:=Q₀.prepared_any bk safe measured
  obtain ⟨resident,stored,_⟩:=Q₀.prepared_shared_final bk safe measured page
  obtain ⟨degree,hubs,loads,nt⟩:=catalog
  rw [degree,hubs,loads,nt] at stored
  have head:Q₀.headerEnd bk≤base:=Nat.le_add_right ..
  have pr:=bk.limits Q₀.projectionEnd H (2^common) M
  have old:Q₀.origin≤base:=Q₀.origin_le_projection.trans ((pr.1.trans (pr.2.1.trans pr.2.2)).trans head)
  have fits {b : Bank} (h : b.Fits w Q₀.origin):b.Fits w base:=⟨h.1,h.2.1,h.2.2.trans old⟩
  have frame (b : Bank) (early : b.Fits w Q₀.origin) (j : ℕ) (jlt : j<b.size) :
      root (b.base+j)=measured (b.base+j):=hold _ (.inl (lt_of_lt_of_le (Nat.add_lt_add_left jlt _) early.2.2))
  have commonRoom:=Q₀.prepared_room bk safe head room (fits peerLow) (fits hubLow) peerSize hubSize hostsFit degreeFit
  obtain ⟨tile,lookup,real⟩:=stencilWords
  let words:=fun h hi=>encode t (2^(width-cc)) (tile h hi)
  have exactWords (h v) (eq : rack h=some v) (hi) : words h hi=encode t (2^(width-cc)) (stencil v hi):=by
    rw [←addr h v eq]
    exact congrArg (encode t (2^(width-cc))) (funext (real v hi))
  have sheet : Source st words M root:=source_column line base lineFit root words lineRows
    (fun p=>(hold _ (.inl ((Nat.add_lt_add_left (row H (2^cc) M p).isLt _).trans_le lineLow))).trans (lookup p))
  have portWord (u : input.V) (j : Fin Yd) :=
    (frame _ peerLow _ ((by have hv:=(idx u).isLt;have hj:=j.isLt;nlinarith only [hv,hj,Nat.mul_le_mul_right Yd (Nat.succ_le_of_lt hv)] :
      (idx u).val*Yd+j.val<H*Yd).trans_le peerSize)).trans (ports u j)
  have depthWord (v : input.V) :=
    (frame _ depthLow _ ((by have hv:=(idx v).isLt;nlinarith only [Nat.mul_le_mul_right (width+1) (Nat.succ_le_of_lt hv)] :
      (idx v).val*(width+1)<H*(width+1)).trans_le depthRows)).trans (depth v)
  have popRead:root pop.base=measured pop.base:=by simpa using frame pop popLow 0 popLow.1
  obtain ⟨dst,native,actors,after,_,depths,levels⟩:=actor_headers accepted level one capacity shapeRoom positive quota degPos
    qs rack idx base pop raw chart st root words exactWords resident commonRoom stored portWord
    (fun v=>(frame _ hubLow _ ((idx v).isLt.trans_le hubSize)).trans (flags v)) (popRead.trans count) depthWord
    occurs addr inv ww cardFit shapesFit hostRange bounded limit (fits popLow) (fits depthLow) depthRows countsFit
    ⟨lineFit,trivial⟩ sheet gateFits accessible
  have end_:(U).endAddress base=base+(U).endAddress 0:=by
    simp [ActorSetup.endAddress,ActorSetup.scene,ActorSetup.gate,ActorSetup.next,
      ActorSetup.heights,ActorSetup.levels,ActorSetup.starts,ActorSetup.counts,ActorSetup.depths,ActorSetup.bank,
      DescentSharedLeafLookup.Public.stop,Bank.size,Nat.add_assoc]
  refine ⟨dst,program.then native,actors,?_,(fun z h=>after z (.inl h)),depths,levels⟩
  intro z hz
  exact (after z (hz.imp_left (·.trans_le old))).trans (hold z (hz.imp_right (fun h=>by omega)))
end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
