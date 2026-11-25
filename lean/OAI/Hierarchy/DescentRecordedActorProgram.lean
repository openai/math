import OAI.Hierarchy.DescentRecordedActorBits
import OAI.Hierarchy.DescentActorHeaderGateRun
import OAI.Hierarchy.DescentActorHeaderControl
import OAI.Hierarchy.DescentHostMaskCore

namespace OAI
/-! # The recorded reset actor planes from physical shared books and old host rows -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
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
variable {Q H M w : ℕ}
  (qs : Fin Q → Node Unit (Unit × DescentContacts.Endpoint (2^reset.reset.n))
    (DescentCommonPalette.rotor reset.reset.graph).Site) (rack : Fin H → Option input.V)
  (idx : input.V ↪ Fin H) (L : HeaderGate.Layout) (S₀ : Headers.Banks) (st : Expr)
local notation "Yd" => (A).degree
local notation "common" => reset.terminals.commonDepth
local notation "rr" => reset.reset.k-common
local notation "arity" => DescentSharedBookScan.width rr Y Yd
local notation "used" => Fintype.card input.V
local notation "prev" => fun v=>reset.reset.placement.b (reset.frame.host v)
local notation "heightBound" => GroupStage.depthBound D n f g
local notation "capBook" => 2^heightBound
local notation "control" => fun j=>headerControl rr Yd (qs j)
local notation "gateOp" => fun j=>op (qs j)
local notation "prog" => HeaderGate.program (H:=H) (G:=2^common) (M:=M) (r:=width-cc) (t:=t) (a:=a) (w:=w) L S₀ control gateOp st
local notation "invoice" => HeaderGate.cost (H:=H) (G:=2^common) (M:=M) (r:=width-cc) (t:=t) (a:=a) (w:=w) L S₀ control gateOp st
local notation "endBank" => L.output+Q*(H*chunks (2^cc) M)

include accepted level one capacity shapeRoom positive quota degPos in
theorem actor_program
    (m : Memory w) (words : Fin H→DescentActorRaster.Block cc→Cell (t*2^(width-cc)))
    (live : ∀h v,rack h=some v→∀hi,words h hi=encode t (2^(width-cc)) (stencil v hi))
    (book : DescentSharedBookScan.Chart) (source : Memory w) (bookOut : ℕ)
    (resident : DescentSharedBookScan.fixed book rr Y Yd H source)
    (bookRoom : DescentSharedBookScan.Room book rr Y Yd H w bookOut)
    (tables : DescentNativeFallbackShapes.Stored book.shapes rr (32*Nat.clog 2 (2*Yd)) g f Y capBook source)
    (priorPorts : ∀u j,source (book.neighbors.base+((idx u).val*Yd+j.val))=
      (DescentFallbackRankRAM.hostDigit idx (peer u j):Word w))
    (flags : ∀u,source (book.isHub.base+(idx u).val)=(((A).hub u).toNat:Word w))
    (ww : 0<w) (cardFit : Yd*capBook<2^w)
    (shapesFit : ∀z : DescentContacts.Endpoint Y,z.1.2<2^z.1.1→z.1.1≤rr→∀i h',
      h'∈DescentFallbackLeafScan.localShape rr (32*Nat.clog 2 (2*Yd)) g f z i→DescentFallbackShapeTable.shapeNumber h'+1<2^w)
    (occurs : ∀h,h.val<used↔∃v,rack h=some v) (addr : ∀h v,rack h=some v→idx v=h)
    (prevDepth : Fin H→ℕ) (truth : ∀v,prevDepth (idx v)=prev v)
    (hostCount : m S₀.population.base=(used:Word w)) (hostRange : used<2^w) (hostSize : H≤2^w)
    (depthRead : ∀v,m (S₀.originalDepth.base+(idx v).val)=(prev v:Word w))
    (bookRead : ∀v (p : DescentSharedBookScan.Fields rr Y Yd),m (S₀.counts.base+(DescentSharedBookScan.absolute (idx v) p).val)=
      image bookOut (H*arity) (DescentSharedBookScan.expr book H Yd capBook) source (bookOut+(DescentSharedBookScan.absolute (idx v) p).val))
    (start : ∀h:Fin H,m (S₀.hostStart.base+h.val)=((h.val*arity:ℕ):Word w))
    (baseCal : ∀j,j<S₀.levels.size→m (S₀.levels.base+j)=((j-cc+1:ℕ):Word w))
    (treeCal : ∀j,j<S₀.heights.size→m (S₀.heights.base+j)=((Nat.clog 2 j+1:ℕ):Word w))
    (levelsWide : ∀v,prev v<S₀.levels.size)
    (countsWide : Yd*capBook<S₀.heights.size)
    (sizes : H≤S₀.originalDepth.size ∧ H≤S₀.hostStart.size ∧ H*arity≤S₀.counts.size)
    (small : ∀b∈[S₀.population,S₀.originalDepth,S₀.counts,S₀.hostStart,S₀.levels,S₀.heights],b.size<2^w)
    (limit : ∀j v,lev v (qs j)+1<2^a)
    (fits : ∀j,(Headers.expression S₀ (control j)).Fits w L.scalar) (earlier : st.Fits w L.scalar)
    (sheet : Source st words M m)
    (tableRoom : L.repeatBase+(DescentSharedLeafLookup.Public.literals L.repeatBase 1 H (2^cc) M a w).length<2^w)
    (bump : L.scalar+Q*H≤L.repeatBase ∧ DescentSharedLeafLookup.Public.stop L.repeatBase H (2^cc) M a≤L.gateBase ∧
       L.gateBase+Q*(2*2^((t*2^(width-cc)+a)*M))≤L.output)
    (stop : endBank<2^w) (accessible : ∀j : Fin Q,DescentSharedLeafLookup.Readable (HeaderGate.header L H (2^cc) M a j)
      1 H (2^cc) M a w L.gateBase) :
    ∃done,(prog).Exec m done invoice ∧
      (∀(j : Fin Q) (p : Row H (2^cc) M),done (L.output+j.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val)=
        ((data (realActor (reset:=reset) qs rack j) p).val:Word w)) ∧
      (∀x,x<L.scalar ∨ endBank≤x→done x=m x) ∧ CheapCode prog := by
  let bookState:=image bookOut (H*arity) (DescentSharedBookScan.expr book H Yd capBook) source
  let counted:=fun (h:Fin H) j=>(bookState (bookOut+(h.val*arity+j))).val
  let tags:=fun j(h:Fin H)=>(((rack h).elim 0 (fun v=>lev v (qs j)+1):ℕ):Cell a)
  have get (v:input.V) (j:ℕ) (hj:j<arity) : ∃p:DescentSharedBookScan.Fields rr Y Yd,
      (DescentSharedBookScan.absolute (idx v) p).val=(idx v).val*arity+j:=by
    let x:= (DescentSharedBookScan.Public.fields rr Y Yd).symm ⟨j,hj⟩
    refine ⟨x,?_⟩
    change (finProdFinEquiv (idx v,((DescentSharedBookScan.Public.fields rr Y Yd) x))).val=_
    simp [x,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have counts (j:Fin Q) (h:Fin H) (i:ℕ) (opEq:control j=.tree i) (hLive:h.val<used) :
      m (S₀.counts.base+(h.val*arity+i))=(counted h i:Word w):=by
    obtain ⟨v,atV⟩:=(occurs h).mp hLive
    obtain rfl:=addr h v atV
    obtain ⟨p,pID⟩:=get v i (root_field_fit (Z:=reset.reset) (T:=reset.terminals) (qs j) opEq)
    simpa [pID,counted,bookState] using bookRead v p
  have numeric (j:Fin Q) (h:Fin H) : (Headers.expression S₀ (control j)).eval m (h.val:Word w)=((tags j h).val:Word w):=by
    have sourceNum:=Headers.evaluated S₀ (control j) m L.scalar H used cc arity h prevDepth counted
      (fits j) hostRange hostSize small hostCount
      (by intro active;obtain ⟨v,atV⟩:=(occurs h).mp active;rw [←addr h v atV,truth];apply depthRead)
      (start h) (counts j h) baseCal treeCal sizes (fun _ eq=>root_field_fit (Z:=reset.reset) (T:=reset.terminals) (qs j) eq) (by
        intro active;obtain ⟨v,atV⟩:=(occurs h).mp active;rw [←addr h v atV]
        refine ⟨fun _=>by rw [truth];apply levelsWide,?_⟩
        intro field eq
        exact (root_tree_size reset.frame f idx peer book source bookOut (qs j) eq v resident bookRoom tables
          priorPorts flags ww cardFit shapesFit).trans_lt countsWide)
    rw [sourceNum]
    cases hit:rack h with
    | none=>
      have ghost : ¬h.val<used:=by rintro actual;obtain ⟨v,x⟩:=(occurs h).mp actual;simp [hit] at x
      simp [Headers.value,ghost,tags,hit]
    | some v=>
      have yes: h.val<used:=(occurs h).mpr ⟨v,hit⟩
      have atV:=addr h v hit
      have truthAt:=root_level reset.frame f idx peer book source bookOut used v (by rwa [atV])
        (qs j) prevDepth (truth v) resident bookRoom tables priorPorts flags ww cardFit shapesFit
      rw [atV] at truthAt
      rw [truthAt]
      simp only [tags,hit,Option.elim_some,Fin.val_cast_of_lt (limit j v)]
  obtain ⟨issued,pins,frame,cheap⟩:=HeaderGate.run L S₀ control gateOp st m words tags fits earlier numeric sheet tableRoom bump stop accessible
  have all (j:Fin Q) (h:Fin H) (hi:DescentActorRaster.Block cc):CPU.gate (width-cc) t a (gateOp j) (words h hi) (tags j h)=
      realActor (reset:=reset) qs rack j h hi:=by
    cases known:rack h with
    | none=>simp [tags,realActor,known,CPU.absent]
    | some v=>
      rw [live h v known]
      simp only [tags,realActor,known,Option.elim_some]
      exact actor_cell accepted level one capacity shapeRoom positive quota degPos v hi (qs j) (limit j v)
  exact ⟨_,issued,fun j p=>by simpa only [all] using pins j p,frame,cheap⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
