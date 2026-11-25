import OAI.Hierarchy.DescentRecordedActorProgram
import OAI.Hierarchy.DescentDatedActorGate

namespace OAI
/-! The literal actor header, read from the attained reset's actual RAM, issues its successor raster. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentDatedAddressBook DescentActorRaster
open DescentCompiler DescentGL DescentColonies DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentPacking.PackedMatch.Local DescentIssuedFallbackPanel
open ResetInput.SourceFrame DescentDenseHostOrder DescentCommonHost DescentPackedZip
open DescentActorRaster.CPU Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
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
variable (idx : input.V↪Fin H) (base : ℕ) (pop raw : Bank) (book : DescentSharedBookScan.Chart) (st : Expr)
local notation "U" => (⟨H,cc,width-cc,M,t,a,Q,arity,width,Yd*capBook⟩ : ActorSetup)
local notation "C" => DescentSharedBookScan.expr book H Yd capBook
local notation "ops" => fun j=>headerControl rr Yd (qs j)
local notation "choice" => fun j=>op (qs j)
local notation "L" => (U).gate base
local notation "B" => (U).sources pop base

set_option maxHeartbeats 600000 in
include accepted level one capacity shapeRoom positive quota degPos in
theorem actor_headers (source : Memory w) (words : Fin H→DescentActorRaster.Block cc→Cell (t*2^(width-cc)))
    (live : ∀h v,rack h=some v→∀hi,words h hi=encode t (2^(width-cc)) (stencil v hi))
    (resident : DescentSharedBookScan.fixed book rr Y Yd H source)
    (bookRoom : DescentSharedBookScan.Room book rr Y Yd H w base)
    (tables : DescentNativeFallbackShapes.Stored book.shapes rr (32*Nat.clog 2 (2*Yd)) g f Y capBook source)
    (ports : ∀u j,source (book.neighbors.base+((idx u).val*Yd+j.val))=(DescentFallbackRankRAM.hostDigit idx (peer u j):Word w))
    (flags : ∀u,source (book.isHub.base+(idx u).val)=(((A).hub u).toNat:Word w))
    (count : source pop.base=(used:Word w))
    (depth : ∀v,source (raw.base+(idx v).val*(width+1))=(prev v:Word w))
    (occurs : ∀h,h.val<used↔∃v,rack h=some v) (addr : ∀h v,rack h=some v→idx v=h)
    (inv : ∀v,rack (idx v)=some v)
    (ww : 0<w) (cardFit : Yd*capBook<2^w)
    (shapesFit : ∀z : DescentContacts.Endpoint Y,z.1.2<2^z.1.1→z.1.1≤rr→∀i h',
      h'∈DescentFallbackLeafScan.localShape rr (32*Nat.clog 2 (2*Yd)) g f z i→DescentFallbackShapeTable.shapeNumber h'+1<2^w)
    (hostRange : used<2^w) (bounded : ∀v,prev v≤width)
    (limit : ∀j v,lev v (qs j)+1<2^a)
    (popLow : pop.Fits w base) (depthLow : raw.Fits w base) (depthRows : H*(width+1)≤raw.size)
    (countsFit : (C).Fits w base) (stencilFit : st.Fits w base) (sheet : Source st words M source)
    (gateFits : (U).GateFits base pop ops st w)
    (accessible : ∀j : Fin Q,DescentSharedLeafLookup.Readable (HeaderGate.header L H (2^cc) M a j)
      1 H (2^cc) M a w (L).gateBase) :
    ∃dst,(((U).headers base raw C w).seq ((U).operator base pop ops choice st (w:=w))).Exec source dst
        ((U).headerTime base raw C w+(U).operatorTime base pop ops choice st w) ∧
      (∀(j : Fin Q) (p : Row H (2^cc) M),dst (((U).scene base).base+j.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val)=
        ((data (realActor (reset:=reset) qs rack j) p).val:Word w)) ∧
      (∀z,z<base ∨ (U).endAddress base≤z→dst z=source z) ∧
      CheapCode (((U).headers base raw C w).seq ((U).operator base pop ops choice st (w:=w))) ∧
      (∀v,dst (((U).depths base).base+(idx v).val)=(prev v:Word w)) ∧
      ∀d,d < ((U).levels base).size → dst (((U).levels base).base+d)=((d-cc+1:ℕ):Word w) := by
  let mid:=(U).headerImage base raw C source
  have order:=(U).gate_order base
  have repeatEnd : DescentSharedLeafLookup.Public.stop (L).repeatBase H (2^cc) M a = (L).gateBase := order.2.1
  have before : (L).repeatBase ≤ (L).gateBase := by
    rw [←repeatEnd]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have gateBefore : (L).gateBase ≤ (L).output := Nat.le_add_right ..
  have beginAt:base≤(L).scalar:=by
    dsimp [ActorSetup.gate,ActorSetup.next,ActorSetup.heights,ActorSetup.levels,ActorSetup.starts,ActorSetup.counts,ActorSetup.depths,ActorSetup.bank]
    omega
  have fin:(L).output+((U).scene base).size=(U).endAddress base:=rfl
  have n:Q*(H*chunks (2^cc) M)≤((U).scene base).size:=(U).extent_scene base
  have bounds:=gateFits.endFit
  have stop:(L).output+Q*(H*chunks (2^cc) M)<2^w:=by omega
  have lt:(L).scalar<2^w:=by omega
  obtain ⟨«prefix»,ch,keep⟩:=(U).headers_any base raw C source depthLow countsFit lt
  obtain ⟨depths,counts,starts,levels,heights⟩:=(U).headers_read base raw C source depthLow countsFit lt depthRows
  obtain ⟨dr,cr,sr,lr,hr⟩:=(U).extent_input base
  have ptr:pop.base<base:=by have :=popLow.1;have :=popLow.2.2;omega
  have small : ∀b∈[(B).population,(B).originalDepth,(B).counts,(B).hostStart,(B).levels,(B).heights],b.size<2^w:=by
    intro b member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    · exact popLow.2.1
    all_goals dsimp [ActorSetup.sources,ActorSetup.gate,ActorSetup.next,ActorSetup.heights,ActorSetup.levels,
      ActorSetup.starts,ActorSetup.counts,ActorSetup.depths,ActorSetup.bank] at lt ⊢;omega
  have boundHost:H≤2^w:=le_trans dr (small _ (by simp [ActorSetup.sources])).le
  have readCount (v : input.V) (p : DescentSharedBookScan.Fields rr Y Yd) :=
    (counts (DescentSharedBookScan.absolute (idx v) p)).trans
      (ProtocolRAMGeneratedWrite.read_image base (H*arity) C source (DescentSharedBookScan.absolute (idx v) p)).symm
  obtain ⟨dst,doIt,rows,«protected»,cheap⟩:=actor_program accepted level one capacity shapeRoom positive quota degPos
    qs rack idx L B st mid words live book source base resident bookRoom tables ports flags ww cardFit shapesFit
    occurs addr (fun h=>(rack h).elim 0 prev) (by intro v;simp [inv v])
    ((keep _ (.inl ptr)).trans count) hostRange boundHost (fun v=>(depths (idx v)).trans (depth v)) readCount
    starts levels heights (fun v=>lt_of_le_of_lt (bounded v) lr) hr ⟨dr,sr,cr⟩ small limit gateFits.control
    (ProtocolRAMGeneratedWrite.fits_mono _ beginAt stencilFit)
    (fun p=>(eval_below st _ source mid stencilFit (fun z hz=>keep z (.inl hz))).trans (sheet p))
    (by change (L).repeatBase+(DescentSharedLeafLookup.Public.stop (L).repeatBase H (2^cc) M a-(L).repeatBase)<2^w
        rw [repeatEnd, Nat.add_sub_of_le before]
        exact gateBefore.trans_lt ((Nat.le_add_right _ _).trans_lt stop))
    ⟨order.1.le,order.2.1.le,order.2.2.le⟩ stop accessible
  obtain ⟨b₀,b₁,b₂,b₃,b₄⟩:=(U).monotone base
  have levelFrame (d : ℕ) (hd : d < ((U).levels base).size) :
      dst (((U).levels base).base+d)=mid (((U).levels base).base+d) := by
    apply «protected» _ (.inl _)
    omega
  have depthFrame (v : input.V) :
      dst (((U).depths base).base+(idx v).val)=mid (((U).depths base).base+(idx v).val) := by
    apply «protected» _ (.inl _)
    change base+(idx v).val<(L).scalar
    have inside:(idx v).val<H:=(idx v).isLt
    change base+H≤_ at b₀
    omega
  refine ⟨dst, ?_, rows, ?_, ?_, ?_, ?_⟩
  · intro labels regs keys machine
    exact Procedure.Exec.then
      («A» := (U).headers base raw C w) («B» := (U).operator base pop ops choice st (w:=w))
      (a := source) (b := mid) (c := dst) «prefix» doIt machine
  · intro z hz
    exact («protected» z (by omega)).trans (keep z (by omega))
  · exact @ProtocolRAM.cheap_seq w ((U).headers base raw C w) ((U).operator base pop ops choice st (w:=w)) @ch @cheap
  · exact fun v => (depthFrame v).trans ((depths (idx v)).trans (depth v))
  · exact fun d hd => (levelFrame d hd).trans (levels d hd)

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
