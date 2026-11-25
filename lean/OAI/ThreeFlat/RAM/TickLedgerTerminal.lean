import OAI.ThreeFlat.RAM.TickSlotKeep
import OAI.ThreeFlat.Diagonal.TickCursorSetup
import OAI.ThreeFlat.Diagonal.TickTerminalPins
import OAI.ThreeFlat.RAM.HistorySelectedInterior
import OAI.ThreeFlat.Diagonal.TraceCursorSlotControl

namespace OAI
/-! # Reading the actual selected chronological caches during terminal emission -/

set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM HistoryNodeDirectory HistoryNodeDirectory.Selected PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.TickWorkspace
open scoped BigOperators Fin.CommRing
noncomputable section
variable {F : Type*} {W n : ℕ}

/-- Bounds, owner rows, and actual source publications used by the native forward traversal. -/
structure VisitFrame (u : ℕ) (input : Memory W) (D : Directory W n) (v : Fin n→NodeValue F)
    (keep : ℕ→Prop) (cost : ℕ→ℕ) (cap : ℕ) : Prop where
  owner : Recorded (ownerData W u) D input
  len : (input ((ownerData W u) 4).val).val+(input ((ownerData W u) 5).val).val=n
  room : n<2^W
  different : ((ownerData W u) 0+1).val≠((ownerData W u) 0).val
  counts : ∀ j : Fin 2,((ownerData W u) ⟨4+j.val,by omega⟩).val≠((ownerData W u) 0).val
  dirs : ∀ i j,(addresses (ownerData W u) D i j).val≠((ownerData W u) 0).val ∧
      (addresses (ownerData W u) D i j).val≠((ownerData W u) 0+1).val
  immutable : ∀ a,keep a → a≠((ownerData W u) 0).val ∧ a≠((ownerData W u) 0+1).val
  aside : ∀ j : Fin n,∀ a,(v j).uses u j.val a → a≠((ownerData W u) 0).val
  wide : 2<2^W
  ctrlRoom : base u 18<2^W
  budget : 17+24*n+∑ root : Word W, (if D.owner root=(D.group,D.slot) then
      ∑ j : {i : Fin n // D.root i=root},cost j.val.val else 0) ≤ cap

structure NativeVisits (u : ℕ) (A : Archive) (B : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (fs : List Family) (input : Memory W)
    (D : Directory W n) (v : Fin n→NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    (keep : ℕ→Prop) (cost : ℕ→ℕ) (cap : ℕ)
    (seedCost : Fin n→ℕ) (stageCost : Fin n→Family→ℕ) : Prop extends VisitFrame u input D v keep cost cap where
  dispatch : ∀ (j : Fin n) (m : Memory W),Ledger u D tag v keep input j.val m → picked D j.val=true →
      let before:=bump (ownerData W u) m
      (nodeAddress u before+5<2^W) ∧
      (∀ f∈fs,(before (nodeAddress u before)).val=kind f.mode →
        stageAddress u before+48<2^W ∧ f.oldPorts<2^W) ∧
      bodyCost u before (seedCost j) (stageCost j) fs ≤ cost j.val
  publish : ∀ (j : Fin n) (m : Memory W),Ledger u D tag v keep input j.val m → picked D j.val=true →
      let before:=bump (ownerData W u) m
      ∃ out : Memory W,
        ((∀ f,fs.find? (matchesFamily u before)=some f →
           (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec before out (stageCost j f)) ∧
        (fs.find? (matchesFamily u before)=none →
           (HistoryInitialSeed.procedure W (Physical.initial u B) pub).Exec before out (seedCost j)) ∧
        (cur (ownerData W u) out).val=j.val+1 ∧ (out ((ownerData W u) 0+1).val).val=n ∧
        Recorded (ownerData W u) D out ∧ (∀ a,keep a → out a=m a) ∧
        (∀ t : Fin n,t.val<j.val → picked D t.val=true → ∀ a,(v t).uses u t.val a → out a=m a) ∧
        (v j).Cached tag u j.val out)

theorem NativeVisits.run (u : ℕ) (A : Archive) (B : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (fs : List Family) (input : Memory W)
    (D : Directory W n) (v : Fin n→NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    (keep : ℕ→Prop) (cost : ℕ→ℕ) (cap : ℕ)
    (seedCost : Fin n→ℕ) (stageCost : Fin n→Family→ℕ)
    (source : NativeVisits u A B pub fs input D v tag keep cost cap seedCost stageCost) :
    (selected W u A B pub fs).Spec (·=input) (fun _ out=>Ledger u D tag v keep input n out) cap :=
  selected_cache u A B pub fs input D v tag keep cost cap source.owner source.len source.room source.different
    source.counts source.dirs source.immutable source.aside seedCost stageCost source.wide source.ctrlRoom
    source.dispatch source.publish source.budget



end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure HistoryStageBody.Physical
open HistoryNodeDirectory HistoryNodeDirectory.Selected HistoryTerminalTape HistoryCompiledRows
open Diagonal Diagonal.TickWorkspace
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u n total p H J : ℕ} {arity : Fin n→ℕ}
local notation "W" => 16*u^10
variable (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p) (pin : Fin p→Bool)
    (wireStart wirePrefix : ℕ)
local notation "A" => mounted u p wireStart wirePrefix

theorem beforeAfter (_age : 1≤u) (space : 65≤ stride u) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (m μ : Memory W) (nfit : (rootIds u head own m).length≤ stride u)
    (frame : ∀ z,immutable u z→μ z=rootStart u head own m z)
    (z : ℕ) (read : (base u 10≤z ∧ z<base u 14) ∨ base u 18+stride u≤z) : μ z=m z := by
  let ids:=rootIds u head own m
  have s14:=apart (u:=u) (by decide : 14<17)
  have s17:=apart (u:=u) (by decide : 17<18)
  have stable : immutable u z := by rcases read with h|h;exact Or.inl h;exact Or.inr (Or.inr h)
  rw [frame z stable]
  apply TickRootScanInit.output_outside
  · change z<base u 18 ∨ base u 18+5≤z
    omega
  · change z<base u 17 ∨ base u 17+ids.length≤z
    dsimp [ids]
    omega

/-- Native root selection uses the cached final layer's start and the ordinal
from the S17 table, both read through the same frame as the real root loop. -/
theorem rootId_ledger_index (age : 1≤u) (space : 65≤ stride u)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W) (m μ : Memory W)
    (first : ℕ) (roots : Fin n→ℕ) (room : n≤ stride u) (rootsFit : ∀ i,roots i<2^W)
    (recorded : rootIds u head own m=List.ofFn roots)
    (header : (m (TickPhysicalABI.directory u 3)).val=first)
    (fr : ∀ z,immutable u z→μ z=rootStart u head own m z)
    (i : Fin n) (iteration : natMemory μ (A).control=i.val) :
    rootId A (natMemory μ)=first+roots i := by
  let xs:=rootIds u head own m
  have len : xs.length=n := by simp [xs,recorded]
  have ix : i.val<xs.length:=i.isLt.trans_eq len.symm
  have s10:=apart (u:=u) (by decide : 10<11)
  have s11:=apart (u:=u) (by decide : 11<14)
  have s17:=apart (u:=u) (by decide : 17<18)
  have hdr : natMemory μ (A).rootHeader=first := by
    change (μ (TickPhysicalABI.directory u 3)).val=_
    rw [beforeAfter age space head own m μ (len.le.trans room) fr _]
    · exact header
    · left
      change base u 10≤base u 11+3*(stride u/4) ∧ base u 11+3*(stride u/4)<base u 14
      omega
  have sel : immutable u (base u 17+i.val):=Or.inr (Or.inl (by have:=i.isLt;omega))
  have range : base u 17+xs.length≤base u 18:=by omega
  have stored:=TickRootScanInit.output_get (rootLookup u) xs m (.inr range) ⟨i.val,ix⟩
  have value : xs[i.val]=roots i := by simp [xs,recorded]
  change natMemory μ (A).rootHeader+natMemory μ (base u 17+natMemory μ (A).control)=_
  rw [hdr,iteration]
  apply congrArg (first+·)
  change (μ (base u 17+i.val)).val=_
  rw [fr _ sel,show rootStart u head own m (base u 17+i.val)=(xs[i.val]:Word W) from stored,
    value,Fin.val_cast_of_lt (rootsFit i)]

omit [Field F] [Fintype F] in
/-- Previously emitted S12 stream/endpoint rows and S13 six-word results
are retained by the S17 initializer and by every subsequent root iteration. -/
theorem ledger_cache {D : Directory W total} {keep : ℕ→Prop} {input m μ : Memory W}
    {v : Fin total→NodeValue F} {id : ((Fin 3→Bool)→F)→ℕ}
    (ledger : Ledger u D id v keep input total m)
    (age : 1≤u) (space : 65≤ stride u) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (nfit : (rootIds u head own m).length≤ stride u)
    (frame : ∀ z,immutable u z→μ z=rootStart u head own m z)
    (j : Fin total) (selected : picked D j.val=true) (results : 8*total≤ stride u)
    (streams : base u 12≤(v j).stream ∧ (v j).stream+4*(v j).net.cells≤base u 14)
    (ends : base u 12≤(v j).ext ∧ (v j).ext+(v j).external≤base u 14) :
    (v j).Cached id u j.val μ := by
  apply (ledger.published j j.isLt selected).retain
  intro a used
  apply beforeAfter age space head own m μ nfit frame
  left
  have s10:=apart (u:=u) (by decide : 10<12)
  have s12:=apart (u:=u) (by decide : 12<13)
  have s13:=apart (u:=u) (by decide : 13<14)
  have limit:=j.isLt
  rcases used with h|h|h <;> omega



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open HistoryTerminalTape HistoryCompiledRows Diagonal Diagonal.TickWorkspace
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u n total p H J : ℕ} {arity : Fin n→ℕ}
local notation "W" => 16*u^10
variable (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p) (pin : Fin p→Bool)
    (wireStart wirePrefix : ℕ)
local notation "A" => mounted u p wireStart wirePrefix

omit [Field F] in
theorem netAt {a b : ℕ} (ea : a=b) (x : BitNetwork F a) (y : BitNetwork F b) (en : HEq x y)
    {ptr : ℕ} {m : Memory W} (stored : Records tag x ptr m) :
    x.cells=y.cells ∧ x.internal=y.internal ∧ Records tag y ptr m := by
  subst b
  have h:=eq_of_heq en
  subst y
  exact ⟨rfl,rfl,stored⟩

omit [Field F] in
/-- At one selected root the cache itself supplies all generated gates, local
arity and hidden count. The two remaining checks concern only pointer geometry. -/
theorem forestRoot_of_cached (i : Fin n) (μ : Memory W) (age : 1≤u) (value : NodeValue F) (j : ℕ)
    (hit : rootId A (natMemory μ)=j) (cache : value.Cached tag u j μ)
    (arityAt : value.pins=arity i) (networkAt : HEq value.net (N i))
    (chart : CompactRoot p wireStart wirePrefix μ)
    (inc : Incidences (terminal A (natMemory μ)) (natMemory μ) μ (pins i))
    (metadataFit : ∀ r j,metadata tag (N i) r j<2^W) : ForestRoot A N pins (immutable u) i μ := by
  let T:=terminal A (natMemory μ)
  let hdr:=HistoryStageRoot.atResult (natMemory μ) ((A).results+8*rootId A (natMemory μ))
  have atH : hdr=value.info := by
    dsimp only [hdr]
    rw [hit]
    exact cache.header
  have size : T.localPins=value.pins:=congrArg HistoryStageRoot.Result.pins atH
  have rows : T.rows=value.net.cells:=congrArg HistoryStageRoot.Result.rows atH
  have stream : T.stream=value.stream:=congrArg HistoryStageRoot.Result.stream atH
  have bitsTaken : hdr.bits=value.net.internal:=congrArg HistoryStageRoot.Result.bits atH
  have exactNet:=netAt arityAt value.net (N i) networkAt cache.rows
  apply physical_root N pins wireStart wirePrefix i μ age chart (size.trans arityAt) (rows.trans exactNet.1)
    (bitsTaken.trans exactNet.2.1) _ inc metadataFit
  change Records tag (N i) T.stream μ
  rw [stream]
  exact exactNet.2.2

omit [Field F] in
/-- State of the native selected traversal immediately before root concatenation.
It suffices to supply primitive arithmetic and geometry per root, uniformly
over earlier root iterations. Local network publication follows from the ledger. -/
theorem terminalInput_of_ledger (age : 1≤u) (space : 65≤ stride u)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W)
    {D : Directory W total} {keep : ℕ→Prop} {input m : Memory W} (value : Fin total→NodeValue F)
    (ledger : Ledger u D tag value keep input total m) (dir : directoryInput u head own m)
    (first : ℕ) (header : (m (TickPhysicalABI.directory u 3)).val=first)
    (idx : Fin n→Fin total) (rel : Fin n→ℕ) (rank : ∀ i,(idx i).val=first+rel i)
    (rootsFit : ∀i,rel i<2^W) (list : rootIds u head own m=List.ofFn rel)
    (yes : ∀i,picked D (idx i).val=true) (resultRoom : 8*total≤ stride u)
    (rootRoom : 2*head.roots≤ stride u/4) (rowsRoom : 4*(forest N pins).cells≤ stride u)
    (bitRoom : (forest N pins).internal≤ stride u) (low : BitLayout.cellsBase p H≤ stride u)
    (keepPins : ∀ z<BitLayout.cellsBase p H,keep z) (physical : ∀ z<BitLayout.cellsBase p H,input z=TickMountedPins.memory pin z)
    (arityAt : ∀ i,(value (idx i)).pins=arity i)
    (netAt : ∀ i,HEq (value (idx i)).net (N i))
    (streams : ∀ i,base u 12≤(value (idx i)).stream ∧ (value (idx i)).stream+4*(value (idx i)).net.cells≤base u 14)
    (ends : ∀ i,base u 12≤(value (idx i)).ext ∧ (value (idx i)).ext+(value (idx i)).external≤base u 14)
    (metadataFit : ∀i r j,metadata tag (N i) r j<2^W)
    (geometry : ∀ (i : Fin n) (μ : Memory W),
      (∀ z,immutable u z→μ z=rootStart u head own m z) →
      natMemory μ (A).control=i.val → natMemory μ ((A).control+1)=n →
      natMemory μ ((A).control+2)=rowStart N i → natMemory μ ((A).control+3)=bitStart N i →
      rootId A (natMemory μ)=(idx i).val → (value (idx i)).Cached tag u (idx i).val μ →
      CompactRoot p wireStart wirePrefix μ ∧ Incidences (terminal A (natMemory μ)) (natMemory μ) μ (pins i))
    (allowance : ℕ) (cost : (∀ i : Fin n,
      let μ:=decrease A (images A (rootStart u head own m) i.val)
      (∀z,immutable u z→μ z=rootStart u head own m z) ∧
        rootId A (natMemory μ)=(idx i).val ∧ (value (idx i)).Cached tag u (idx i).val μ) →
      finishCost (H:=H) (J:=J) N pins wireStart wirePrefix head own m≤allowance) :
    terminalInput (u:=u) (H:=H) (J:=J) N pins pin wireStart wirePrefix head own allowance m := by
  have number : (rootIds u head own m).length=n:=by rw [list,List.length_ofFn]
  have leRoots : n≤head.roots := by
    rw [←number]
    simpa only [rootIds,TickRootScanInit.chosen,List.length_range] using
      List.length_filter_le (TickSlotLookup.matchesOwner own (m (rootLookup u).s1) (m ((rootLookup u).s1+3))) (List.range head.roots)
  have ns : n≤ stride u:=by omega
  let init:=rootStart u head own m
  have source (i : Fin n) (μ : Memory W) (frame : ∀z,immutable u z→μ z=init z)
      (iteration : natMemory μ (A).control=i.val) :
      rootId A (natMemory μ)=(idx i).val ∧ (value (idx i)).Cached tag u (idx i).val μ :=
    ⟨(rootId_ledger_index wireStart wirePrefix age space head own m μ first rel ns rootsFit list header frame i iteration).trans
        (rank i).symm,
     ledger_cache ledger age space head own (number.le.trans ns) frame (idx i) (yes i) resultRoom (streams i) (ends i)⟩
  let chart:=physical_forest N pins pin wireStart wirePrefix age space head own m number rootRoom rowsRoom bitRoom low
    (fun z hz=>(ledger.durable z (keepPins z hz)).trans (physical z hz)) (by
      intro i μ frame iteration count row bit
      obtain ⟨location,cache⟩:=source i μ frame iteration
      obtain ⟨bounds,inc⟩:=geometry i μ frame iteration count row bit location cache
      exact forestRoot_of_cached N pins wireStart wirePrefix i μ age _ _ location cache
        (arityAt i) (netAt i) bounds inc (metadataFit i))
  refine ⟨dir,⟨chart⟩,cost ?_⟩
  intro i
  obtain ⟨frame,iter⟩:=forest_iteration A N pins pin init chart i
  exact ⟨frame,source i _ frame iter⟩



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open HistoryTerminalTape HistoryCompiledRows Diagonal Diagonal.TickWorkspace Diagonal.PhysicalStage
open Diagonal.CompressorPacking.Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {u d l n p : ℕ}
local notation "W" => 16*u^10

/-- All fixed words read from S11–13 or the upper geometry banks survive
both native S17 initialization and every subsequent root iteration. -/
structure StableInterval (u at_ size : ℕ) : Prop where
  place : (base u 10≤at_ ∧ at_+size≤base u 14) ∨ base u 18+stride u≤at_
  bound : at_+size≤2^(16*u^10)

theorem StableInterval.bank {a s : ℕ} (S : StableInterval u a s) : ImmutableBank u a s :=
  ⟨S.place.imp And.right id,S.bound⟩

theorem StableInterval.sub {a s : ℕ} (S : StableInterval u a s) {b n : ℕ} (first : a≤b) (last : b+n≤a+s) :
    StableInterval u b n := by
  refine ⟨?_,last.trans S.bound⟩
  rcases S.place with h|h
  · exact Or.inl ⟨h.1.trans first,last.trans h.2⟩
  · exact Or.inr (h.trans first)

theorem StableInterval.safe {a s : ℕ} (S : StableInterval u a s) (z : ℕ) (lo : a≤z) (hi : z<a+s) :
    (base u 10≤z ∧ z<base u 14) ∨ base u 18+stride u≤z :=
  S.place.imp (fun h=>⟨h.1.trans lo,hi.trans_le h.2⟩) (fun h=>h.trans lo)

/-- Numeric compact geometry from the original S44/S49 journal. The final
wire prefix is read only at live edge bits. -/
structure HalfImage (X : State d l) (z : X.Site) (u root wireTable : ℕ) (m : Memory (16*u^10)) where
  nodeBase : ℕ
  header : ℕ
  entries : ℕ
  directory : natMemory m (TickPhysicalABI.directory u 3+1)=nodeBase
  pointer : natMemory m (nodeBase+8*root+6)=header
  count : natMemory m header=2*d
  data : natMemory m (header+1)=entries
  edge : ∀ i : Fin (2*d),natMemory m (entries+4*i.val)=Halves.edgeNumber X.order (Halves.sourceHalf X.graph (X.chart.symm z) i)
  width : ∀ i : Fin (2*d),natMemory m (entries+4*i.val+2)=X.width (Halves.sourceHalf X.graph (X.chart.symm z) i)
  start : ∀ i : Fin (2*d),natMemory m (entries+4*i.val+3)=Halves.prefixValue X.graph X.width (X.chart.symm z) i
  live : ∀ (i : Fin X.edgeCount) (j : Fin (X.wireWidth i)),natMemory m (wireTable+i.val)+j.val=(X.bitAddress i j).val
  headerBank : StableInterval u (nodeBase+8*root+6) 1
  countBank : StableInterval u header 2
  dataBank : StableInterval u entries (4*(2*d))
  edgeBank : StableInterval u wireTable X.edgeCount

def HalfImage.retain {X : State d l} {z : X.Site} {root wireTable : ℕ} {m μ : Memory W}
    (G : HalfImage X z u root wireTable m) (space : 65≤ stride u)
    (same : ∀ j,(base u 10≤j ∧ j<base u 14) ∨ base u 18+stride u≤j → μ j=m j) :
    HalfImage X z u root wireTable μ := by
  let before:=apart (u:=u) (by decide : 10<11)
  let after:=apart (u:=u) (by decide : 11<14)
  have head : (base u 10≤TickPhysicalABI.directory u 3+1 ∧ TickPhysicalABI.directory u 3+1<base u 14) := by
    change base u 10≤base u 11+3*(stride u/4)+1 ∧ base u 11+3*(stride u/4)+1<base u 14
    omega
  refine ⟨G.nodeBase,G.header,G.entries,?_,?_,?_,?_,?_,?_,?_,?_,G.headerBank,G.countBank,G.dataBank,G.edgeBank⟩
  · exact (congrArg Fin.val (same _ (.inl head))).trans G.directory
  · exact (congrArg Fin.val (same _ (G.headerBank.safe _ le_rfl (by omega)))).trans G.pointer
  · exact (congrArg Fin.val (same _ (G.countBank.safe _ le_rfl (by omega)))).trans G.count
  · exact (congrArg Fin.val (same _ (G.countBank.safe _ (by omega) (by omega)))).trans G.data
  · intro i
    exact (congrArg Fin.val (same _ (G.dataBank.safe _ (by omega) (by have:=i.isLt;omega)))).trans (G.edge i)
  · intro i
    exact (congrArg Fin.val (same _ (G.dataBank.safe _ (by omega) (by have:=i.isLt;omega)))).trans (G.width i)
  · intro i
    exact (congrArg Fin.val (same _ (G.dataBank.safe _ (by omega) (by have:=i.isLt;omega)))).trans (G.start i)
  · intro i j
    have eq:=congrArg Fin.val (same (wireTable+i.val) (G.edgeBank.safe _ (by omega) (by have:=i.isLt;omega)))
    exact (congrArg (·+j.val) eq).trans (G.live i j)



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryStageBody.Physical HistoryTerminalTape HistoryCompiledRows
open Diagonal Diagonal.TickWorkspace Diagonal.PhysicalStage Diagonal.CompressorPacking.Native.ShrinkStage
open private rootSum_mono rootSum_step rootSum_fin from OAI.ThreeFlat.RAM.TickTerminalForest
open scoped BigOperators Classical
noncomputable section

theorem prefixCell {n : ℕ} (f : Fin n→ℕ) (i : Fin n) :
    (∑ j : Fin i.val,f (Fin.castLE i.isLt.le j))+f i≤∑ j,f j := by
  have h:=rootSum_mono f (i:=i.val+1) (j:=n) i.isLt
  rwa [rootSum_step,dite_eq_left i.isLt,rootSum_fin f i.isLt.le,rootSum_all] at h

variable {d l u p : ℕ} {Pins F : Type} [Field F] [Fintype F]
local notation "W" => 16*u^10
variable (start wireTable : ℕ)
local notation "A" => mounted u p start wireTable

omit [Field F] in
/-- Counts consumed by the terminal interpreter are the actual recorded layer widths. -/
theorem HalfImage.iteration_sizes (m : Memory W) (X : State d l) (z : X.Site) (idx : ℕ)
    (G : HalfImage X z u idx wireTable m) (v : NodeValue F)
    (cache : v.Cached tag u idx m) (hit : rootId A (natMemory m)=idx) :
    let T:=terminal A (natMemory m)
    T.halves=2*d ∧ (∑j : Fin T.halves,(half T (natMemory m) j.val).width)=X.incidentWidth z ∧
      T.ext=v.external ∧ T.rows=v.net.cells := by
  let T:=terminal A (natMemory m)
  have hdr : HistoryStageRoot.atResult (natMemory m) ((A).results+8*rootId A (natMemory m))=v.info := by
    rw [hit];exact cache.header
  have directory : natMemory m ((A).rootHeader+1)=G.nodeBase := G.directory
  have ptr : natMemory m (natMemory m ((A).rootHeader+1)+8*rootId A (natMemory m)+6)=G.header := by
    rw [hit,directory];exact G.pointer
  have count : T.halves=2*d := (congrArg (natMemory m) ptr).trans G.count
  have entries : T.halfData=G.entries := (congrArg (fun a => natMemory m (a+1)) ptr).trans G.data
  refine ⟨count,?_,congrArg HistoryStageRoot.Result.extCount hdr,congrArg HistoryStageRoot.Result.rows hdr⟩
  change (∑ j:Fin T.halves,(half T (natMemory m) j.val).width)=_
  rw [count]
  calc
    _=(∑ j:Fin (2*d),X.width (Halves.sourceHalf X.graph (X.chart.symm z) j)):=by
      apply Finset.sum_congr rfl
      intro j _
      change natMemory m (T.halfData+4*j.val+2)=_
      rw [entries]
      exact G.width j
    _=X.incidentWidth z:=half_total X.graph X.width (X.chart.symm z)

omit [Field F] in
/-- Compact-root bounds follow from physical archived half tables, the true
sizes and addresses of the published root, and the actual prefix counters. -/
theorem compactRoot_of_ledger (space : 65≤ stride u)
    (words : p<2^W ∧ start<2^W ∧ wireTable<2^W) (m : Memory W)
    (X : State d l) (K : X.Words Pins) (ordered : X.OrderedHalves K) (z : X.Site) (idx : ℕ)
    (G : HalfImage X z u idx wireTable m) (value : NodeValue F)
    (cache : value.Cached tag u idx m) (hit : rootId A (natMemory m)=idx)
    (rootFits : 8*idx+6≤ stride u) (selected : natMemory m (A).control<stride u)
    (halfRoom : 7*(2*d+2)≤ stride u) (mapRoom : 64+value.pins≤ stride u)
    (stream : base u 12≤value.stream ∧ value.stream+4*value.net.cells≤base u 14)
    (endRoom : value.ext+value.external≤base u 14)
    (rowRoom : 4*(natMemory m ((A).control+2)+value.net.cells)≤ stride u)
    (ext : value.external=K.ext z) (pinCount : value.pins=K.ports.form.width z) :
    CompactRoot p start wireTable m := by
  let T:=terminal A (natMemory m)
  have info : HistoryStageRoot.atResult (natMemory m) ((A).results+8*rootId A (natMemory m))=value.info := by
    rw [hit]
    exact cache.header
  have directory : natMemory m ((A).rootHeader+1)=G.nodeBase := G.directory
  have ptr : natMemory m (natMemory m ((A).rootHeader+1)+8*rootId A (natMemory m)+6)=G.header := by
    rw [hit,directory];exact G.pointer
  have count : T.halves=2*d := (congrArg (natMemory m) ptr).trans G.count
  have entries : T.halfData=G.entries := (congrArg (fun a => natMemory m (a+1)) ptr).trans G.data
  have size : T.localPins=value.pins:=congrArg HistoryStageRoot.Result.pins info
  have external : T.ext=value.external:=congrArg HistoryStageRoot.Result.extCount info
  have ending : T.endpoints=value.ext:=congrArg HistoryStageRoot.Result.ext info
  have record : T.rows=value.net.cells:=congrArg HistoryStageRoot.Result.rows info
  have source : T.stream=value.stream:=congrArg HistoryStageRoot.Result.stream info
  have ed (b : Fin (2*d)) : (half T (natMemory m) b.val).edge=
      Halves.edgeNumber X.order (Halves.sourceHalf X.graph (X.chart.symm z) b) := by
    change natMemory m (T.halfData+4*b.val)=_; rw [entries];exact G.edge b
  have len (b : Fin (2*d)) : (half T (natMemory m) b.val).width=X.width (Halves.sourceHalf X.graph (X.chart.symm z) b) := by
    change natMemory m (T.halfData+4*b.val+2)=_; rw [entries];exact G.width b
  have offset (b : Fin (2*d)) : (half T (natMemory m) b.val).start=Halves.prefixValue X.graph X.width (X.chart.symm z) b := by
    change natMemory m (T.halfData+4*b.val+3)=_; rw [entries];exact G.start b
  have between:=apart (u:=u) (by decide : 13<14)
  refine ⟨space,words,selected,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change base u 13+8*rootId A (natMemory m)+6≤base u 14
    rw [hit];omega
  · change ImmutableBank u (natMemory m ((A).rootHeader+1)+8*rootId A (natMemory m)+6) 1
    rw [hit,directory];exact G.headerBank.bank
  · change ImmutableBank u (natMemory m (natMemory m ((A).rootHeader+1)+8*rootId A (natMemory m)+6)) 2
    rw [ptr];exact G.countBank.bank
  · change ImmutableBank u T.halfData (4*T.halves)
    rw [entries,count];exact G.dataBank.bank
  · change ∀ b : ℕ, b<T.halves → ImmutableBank u (wireTable+(half T (natMemory m) b).edge) 1
    intro b hb
    let i : Fin (2*d):=⟨b,hb.trans_eq count⟩
    let e:=Halves.sourceHalf X.graph (X.chart.symm z) i
    have boundAll (j : X.shape.Edge) : Halves.edgeNumber X.order j<X.edgeCount := by
      obtain ⟨⟨a,k⟩,l⟩:=j
      exact lt_of_eq_of_lt (X.wireOrder_val a k l).symm (X.wireOrder ((a,k),l)).isLt
    have bound:=boundAll e
    change ImmutableBank u (wireTable+(half T (natMemory m) b).edge) 1
    have edgeHere : (half T (natMemory m) b).edge=Halves.edgeNumber X.order e := ed i
    rw [edgeHere]
    exact (G.edgeBank.sub (by omega) (by omega)).bank
  · change 7*(T.halves+2)≤_;rwa [count]
  · change 64+T.localPins≤_;rwa [size]
  · constructor
    · change T.ext≤T.localPins
      rw [external,size,ext,pinCount]
      exact Nat.le_add_right ..
    · intro b hb
      let i : Fin (K.count z):=⟨b,(hb.trans_eq count).trans_eq (ordered.count z).symm⟩
      let i' := i.cast (ordered.count z)
      have localWidth : X.width (Halves.sourceHalf X.graph (X.chart.symm z) i')=K.ports.lengths z i :=
        congrArg X.width (ordered.edge z i).symm
      have startHere : (half T (natMemory m) b).start =
          ∑ j : Fin i.val,K.ports.lengths z (Fin.castLE i.isLt.le j) :=
        (offset i').trans (ordered.start z i)
      have widthHere : (half T (natMemory m) b).width=K.ports.lengths z i := (len i').trans localWidth
      have extHere : T.ext=K.ext z := external.trans ext
      have pinsHere : T.localPins=K.ext z+∑ j,K.ports.lengths z j := size.trans pinCount
      rw [startHere,widthHere,extHere,pinsHere,Nat.add_assoc]
      exact Nat.add_le_add_left (prefixCell (K.ports.lengths z) i) _
  · change T.endpoints+T.ext≤_
    rwa [ending,external]
  · change base u 9+4*natMemory m ((A).control+2)+4*T.rows≤base u 9+stride u
    rw [record];omega
  · change base u 10≤T.stream ∧ T.stream+4*T.rows≤_
    rw [source,record]
    exact ⟨(show base u 10≤base u 12 by have:=apart (u:=u) (by decide : 10<12);omega).trans stream.1,stream.2⟩



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open PhysicalStage RAM.TickTerminalRoot RAM.HistoryTerminalTape RAM.HistoryStageBody.Physical
open CompressorPacking.Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

variable (C : R.Charges) (O : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).ArchiveSites) (path : R.ArchivePath v.1 C O) (zero : O.layer.first=0)
local notation "total" => (R.finalArchive v.1 C O path).1.first+(R.finalArchive v.1 C O path).1.count
local notation "archiveNode" => R.archiveNode v.1 J.steps U N C O path zero
local notation "index" => R.archivePlanIndex v.1 C O path
local notation "sourceCode" => (fun p=>(2+(Buckets.packEndpoint c hc T v g room advice nt ns np (seedEndpoint L low p.1 p.2)).val : ℕ))

/-- The exact node payload used in the physical selected-root ledger, with
the mathematical tree, endpoint provenance and both S12 offsets. -/
def archivedValues (streams ends : Fin ((R.finalArchive v.1 C O path).1.first+
    (R.finalArchive v.1 C O path).1.count)→ℕ)
    (i : Fin ((R.finalArchive v.1 C O path).1.first+(R.finalArchive v.1 C O path).1.count)) :
    NodeValue F :=
  NodeValue.ofSite
    (PhysicalStage.Run.archiveNode R v.1 J.steps (seedWordLayout M t hF st B hk extent) N C O path zero i)
    (fun endpoint => 2+(Buckets.packEndpoint c hc T v g room advice nt ns np
      (seedEndpoint (period*width*a+period*width*a) low endpoint.1 endpoint.2)).val)
    (streams i) (ends i)

private theorem originAt {α : Type} {m n : ℕ} {f : Fin m→α} {g : Fin n→α}
    (eqv : m=n) (words : List.ofFn f=List.ofFn g) (i : Fin n) : f (i.cast eqv.symm)=g i := by
  subst n
  exact congrFun (List.ofFn_injective words) i

private theorem transportedWidth {Y Z : Shape} {Pins : Type} (e : Y=Z)
    (Q : Form Y Pins) (W : Form Z Pins) (forms : HEq Q W) (z : Z.Site) :
    W.width z=Q.width (cast (congrArg Shape.Site e).symm z) := by
  subst Z
  have eqv:=eq_of_heq forms
  subst W
  rfl

local notation "values" => archivedValues M t hF st B hk c hc extent R J N T v g room advice nt ns np C O path zero

/-- The original endpoints and the incident rows read by one terminal pass
account for exactly the typed arity at the scheduled root. -/
theorem archived_root_width (root : (R.plan.finish v.1).Site)
    (streams ends : Fin ((R.finalArchive v.1 C O path).1.first+(R.finalArchive v.1 C O path).1.count)→ℕ) :
    (archivedValues M t hF st B hk c hc extent R J N T v g room advice nt ns np C O path zero
      streams ends (R.archivePlanIndex v.1 C O path root)).external+R.terminalIncident v.1 root =
      (R.plan.assemble v.1 (J (seedWordLayout M t hF st B hk extent)) N).1.width root := by
  let seed := seedWordLayout M t hF st B hk extent
  have ext := PhysicalStage.Run.archivePlanExternal R v.1 J.steps seed N C O path zero root
  have widthAt := PhysicalStage.Run.terminal_width_exact R v.1 J.steps seed
    (seedWordLayout_halves M t hF st B hk extent) N root
  exact (congrArg (fun x => x+R.terminalIncident v.1 root) ext.1).trans widthAt.symm

open scoped Fin.CommRing in
set_option maxHeartbeats 1600000 in
/-- Recover all shape, size and endpoint equations for a true S17 terminal
root from its S13 result word and S12 cache. -/
theorem ledgerGeometry (root : (R.plan.finish v.1).Site) (streams ends : Fin total→ℕ)
    {age teams : ℕ} (wireStart wireTable : ℕ) (m : Memory (16*age^10)) :
    let arena := RAM.TickTerminalRoot.mounted age PINS wireStart wireTable
    let tape := RAM.TickTerminalRoot.terminal arena (natMemory m)
    let z:=R.physicalTerminal v.1 root
    let i:=index root
    let data:=values streams ends i
    let wire:=terminalWire M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np root
    (data.Cached TickTerminalRoot.tag age i.val m) →
    (rootId arena (natMemory m)=i.val) → HalfImage X z age i.val wireTable m →
    65≤TickWorkspace.stride age →
    (PINS<2^(16*age^10) ∧ wireStart<2^(16*age^10) ∧ wireTable<2^(16*age^10)) →
    8*i.val+6≤TickWorkspace.stride age → natMemory m arena.control<TickWorkspace.stride age →
    7*(2*(R.terminalLayer v.1).degree+2)≤TickWorkspace.stride age → 64+data.pins≤TickWorkspace.stride age →
    (TickWorkspace.base age 12≤data.stream ∧ data.stream+4*data.net.cells≤TickWorkspace.base age 14) →
    data.ext+data.external≤TickWorkspace.base age 14 →
    4*(natMemory m (arena.control+2)+data.net.cells)≤TickWorkspace.stride age →
    wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+(R.plan.write E v.1).length →
      CompactRoot PINS wireStart wireTable m ∧ Incidences tape (natMemory m) m wire := by
  intro arena tape z i data wire cache hit halfImage space wordFit idFit indexFit tableFit mapFit streamFit extFit metaFit wireAt
  have atExt:=R.archivePlanExternal v.1 J.steps U N C O path zero root
  have atNet:=R.archivePlanNetwork v.1 J.steps U N C O path zero root
  have countExt : data.external=(K).ext z:=atExt.1
  have countPins : data.pins=(K).ports.form.width z :=
    atNet.1.trans (transportedWidth (R.terminalLayer_shape v.1) (K).ports.form (result).1
      (R.endWords_form v.1 J.steps U N).symm root)
  have hdr : HistoryStageRoot.atResult (natMemory m) (arena.results+8*rootId arena (natMemory m))=data.info := by
    rw [hit];exact cache.header
  have headLoc : natMemory m (natMemory m (arena.rootHeader+1)+8*rootId arena (natMemory m)+6)=halfImage.header := by
    rw [hit]
    exact (congrArg (fun nodeBase => natMemory m (nodeBase+8*i.val+6)) halfImage.directory).trans halfImage.pointer
  have halfCount : tape.halves=2*(R.terminalLayer v.1).degree := by
    change natMemory m _=_;rw [headLoc];exact halfImage.count
  have halfBase : tape.halfData=halfImage.entries := by
    change natMemory m (_+1)=_; rw [headLoc];exact halfImage.data
  refine ⟨compactRoot_of_ledger wireStart wireTable space wordFit m X K (terminalHalves M t hF st B hk extent R J v)
    z i.val halfImage data cache hit idFit indexFit tableFit mapFit streamFit extFit metaFit countExt countPins,?_⟩
  refine terminalWire_published (age := age) (teams := teams) M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np
    root z (cast_heq _ root) tape (natMemory m) m
    ((congrArg HistoryStageRoot.Result.extCount hdr).trans countExt) halfCount ?_ wireAt ?_ halfImage.live
  · intro j
    have ptr : tape.endpoints=data.ext:=congrArg HistoryStageRoot.Result.ext hdr
    rw [ptr]
    have val:=cache.ends (j.cast countExt.symm)
    change m (data.ext+j.val)=((sourceCode ((archiveNode i).origin (j.cast countExt.symm)):ℕ):Word _) at val
    have endpoint : (archiveNode i).origin (j.cast countExt.symm) =
        R.extAncestor v.1 J.steps U z j := originAt countExt atExt.2 j
    exact val.trans (congrArg (fun p : Σ x : (A).Site, Fin ((U).ext x) =>
      ((sourceCode p : ℕ) : Word (16*age^10))) endpoint)
  · intro b
    change (natMemory m (tape.halfData+4*b.val)=_) ∧ (natMemory m (tape.halfData+4*b.val+2)=_) ∧
      (natMemory m (tape.halfData+4*b.val+3)=_)
    rw [halfBase];exact ⟨halfImage.edge b,halfImage.width b,halfImage.start b⟩



end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open Diagonal Diagonal.TickWorkspace
open scoped Classical BigOperators
variable {F : Type} [Field F] [Fintype F] {u n : ℕ} {D : Directory (16*u^10) n} {v : Fin n→NodeValue F}
  {keep : ℕ→Prop} {input m : Memory (16*u^10)}

omit [Field F] in
/-- The S6 compact directory and S11 owners loaded by terminal preparation
are still the ones mounted at its preceding selected traversal. -/
theorem ledgerDirectory (Q : Ledger u D tag v keep input n m) (h : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner (16*u^10)) (before : directoryInput u h own input)
    (s6 : ∀ i : Fin 8,keep (base u 6+i.val))
    (owners : ∀ j<h.roots,keep (TickPhysicalABI.directory u 1+2*j) ∧ keep (TickPhysicalABI.directory u 1+2*j+1)) :
    directoryInput u h own m := by
  constructor
  · intro i;exact (Q.durable _ (s6 i)).trans (before.1 i)
  · intro j hj
    exact ⟨(Q.durable _ (owners j hj).1).trans (before.2 j hj).1,(Q.durable _ (owners j hj).2).trans (before.2 j hj).2⟩

omit [Field F] in
theorem localMetadataFit {a W : ℕ} (N : BitNetwork F a) (width : 2+a+N.internal≤2^W)
    (library : Fintype.card ((Fin 3→Bool)→F)≤2^W) (i : Fin N.cells) (j : Fin 4) :
    HistoryCompiledRows.metadata tag N i j<2^W := by
  exact HistoryCompiledRows.metadata_fits tag N width
    (fun t => (Fintype.equivFin _ t).isLt.trans_le library) i j



end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open Diagonal Diagonal.TickWorkspace Diagonal.PhysicalStage Diagonal.CompressorPacking.Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u d l n root wp : ℕ} {X : State d l} {z : X.Site}
local notation "W" => 16*u^10

def HalfImage.reads {m : Memory W} (G : HalfImage X z u root wp m) (a : ℕ) :=
  a=TickPhysicalABI.directory u 3+1 ∨ a=G.nodeBase+8*root+6 ∨
  (G.header≤a ∧ a<G.header+2) ∨ (G.entries≤a ∧ a<G.entries+4*(2*d)) ∨ (wp≤a ∧ a<wp+X.edgeCount)

def HalfImage.transfer {input m : Memory W} (G : HalfImage X z u root wp input)
    (saved : ∀ j,G.reads j→m j=input j) : HalfImage X z u root wp m := by
  have same (j : ℕ) (belongs : G.reads j) : natMemory m j=natMemory input j :=
    congrArg Fin.val (saved j belongs)
  refine ⟨G.nodeBase,G.header,G.entries,(same _ (Or.inl rfl)).trans G.directory,
    (same _ (Or.inr (Or.inl rfl))).trans G.pointer,?_,?_,?_,?_,?_,?_,G.headerBank,G.countBank,G.dataBank,G.edgeBank⟩
  · exact (same _ (Or.inr (Or.inr (Or.inl (by omega))))).trans G.count
  · exact (same _ (Or.inr (Or.inr (Or.inl (by omega))))).trans G.data
  · intro i;exact (same _ (Or.inr (Or.inr (Or.inr (Or.inl (by have:=i.isLt;omega)))))).trans (G.edge i)
  · intro i;exact (same _ (Or.inr (Or.inr (Or.inr (Or.inl (by have:=i.isLt;omega)))))).trans (G.width i)
  · intro i;exact (same _ (Or.inr (Or.inr (Or.inr (Or.inl (by have:=i.isLt;omega)))))).trans (G.start i)
  · intro i j
    exact (congrArg (·+j.val) (same _ (Or.inr (Or.inr (Or.inr (Or.inr (by have:=i.isLt;omega))))))).trans (G.live i j)


def HalfImage.fromLedger {D : Directory W n} {value : Fin n→NodeValue F} {keep : ℕ→Prop}
    {input m : Memory W} (G : HalfImage X z u root wp input)
    (Q : Ledger u D tag value keep input n m) (saved : ∀ j,G.reads j→keep j) : HalfImage X z u root wp m :=
  G.transfer (fun j hj=>Q.durable j (saved j hj))



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open PhysicalStage RAM.TickTerminalRoot RAM.HistoryTerminalTape RAM.HistoryStageBody.Physical
open CompressorPacking.Native.ShrinkStage
open NavigationPass NavigationPass.RootArchive RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

variable (C : R.Charges) (O : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).ArchiveSites) (path : R.ArchivePath v.1 C O) (zero : O.layer.first=0)
local notation "total" => (R.finalArchive v.1 C O path).1.first+(R.finalArchive v.1 C O path).1.count
local notation "archiveNode" => R.archiveNode v.1 J.steps U N C O path zero
local notation "index" => R.archivePlanIndex v.1 C O path
local notation "sourceCode" => (fun p=>(2+(Buckets.packEndpoint c hc T v g room advice nt ns np (seedEndpoint L low p.1 p.2)).val : ℕ))

local notation "values" => archivedValues M t hF st B hk c hc extent R J N T v g room advice nt ns np C O path zero

variable (arch : RootArchive) (work pairs : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).Site→ℕ) (teams slot : ℕ)
local notation "roots" => arch.teamRoots R v.1 C work pairs c teams g.val slot
local notation "rank" => fun i : Fin (roots).length=>NavigationPass.RootArchive.terminalRank R v.1 ((roots).get i)
local notation "current" => fun i : Fin (roots).length=>index ((roots).get i)
local notation "Nets" => fun (i : Fin (roots).length)=>((result).2 ((roots).get i)).compile
local notation "Wires" => fun (i : Fin (roots).length)=>terminalWire M t hF st B hk c hc extent R J N E T v g
  room wireRoom advice nt ns np ((roots).get i)

/-- The complete selected interior actually supplies the terminal preparation
predicate for its real ranked roots and their mounted wire maps. The resource
arguments are physical region bounds and the measured slot finish allowance. -/
theorem selected_terminalInput {age H Jmax : ℕ} (wireStart wireTable : ℕ)
    (pin : Fin PINS→Bool) (streams ends : Fin total→ℕ)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*age^10))
    (D : Directory (16*age^10) total) (keep : ℕ→Prop) (input m : Memory (16*age^10))
    (Q : Ledger age D TickTerminalRoot.tag (values streams ends) keep input total m)
    (before : TickTerminalRoot.directoryInput age head own input)
    (s6 : ∀ i : Fin 8,keep (TickWorkspace.base age 6+i.val))
    (ownerWords : ∀ j<head.roots,keep (TickPhysicalABI.directory age 1+2*j) ∧ keep (TickPhysicalABI.directory age 1+2*j+1))
    (firstKept : keep (TickPhysicalABI.directory age 3))
    (first : (input (TickPhysicalABI.directory age 3)).val=(R.finalArchive v.1 C O path).1.first)
    (num : R.FinalNumbered v.1 C O path) (rootsFit : ∀i,rank i<2^(16*age^10))
    (selected : TickTerminalRoot.rootIds age head own m=(roots).map (NavigationPass.RootArchive.terminalRank R v.1))
    (pickedRoots : ∀ i, picked D (current i).val=true)
    (agePos : 1≤age) (space : 65≤TickWorkspace.stride age)
    (wordFit : PINS<2^(16*age^10) ∧ wireStart<2^(16*age^10) ∧ wireTable<2^(16*age^10))
    (resultRoom : 8*total≤TickWorkspace.stride age) (rootRoom : 2*head.roots≤TickWorkspace.stride age/4)
    (rowsRoom : 4*(TickTerminalRoot.forest Nets Wires).cells≤TickWorkspace.stride age)
    (bitRoom : (TickTerminalRoot.forest Nets Wires).internal≤TickWorkspace.stride age)
    (low : BitLayout.cellsBase PINS H≤TickWorkspace.stride age)
    (library : Fintype.card ((Fin 3→Bool)→F)≤2^(16*age^10))
    (keepPins : ∀ z<BitLayout.cellsBase PINS H,keep z)
    (physical : ∀ z<BitLayout.cellsBase PINS H,input z=TickMountedPins.memory pin z)
    (geometry : ∀ i, HalfImage X (R.physicalTerminal v.1 ((roots).get i)) age (current i).val wireTable input)
    (keepGeometry : ∀i j,(geometry i).reads j→keep j)
    (tableFit : 7*(2*(R.terminalLayer v.1).degree+2)≤TickWorkspace.stride age)
    (mapFit : ∀i,64+(values streams ends (current i)).pins≤TickWorkspace.stride age)
    (streamFit : ∀i,let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.stream ∧ val.stream+4*val.net.cells≤TickWorkspace.base age 14)
    (endFit : ∀i, let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.ext ∧ val.ext+val.external≤TickWorkspace.base age 14)
    (wireAt : wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+(R.plan.write E v.1).length)
    (allowance : ℕ)
    (time : (∀i : Fin (roots).length,
      let A':=mounted age PINS wireStart wireTable
      let raw:=natMemory (decrease A' (images A' (rootStart age head own m) i.val))
      let tape:=terminal A' raw
      tape.halves=2*(R.terminalLayer v.1).degree ∧
        (∑j : Fin tape.halves,(half tape raw j.val).width)=R.terminalIncident v.1 ((roots).get i) ∧
        tape.ext=(values streams ends (current i)).external ∧ tape.rows=(Nets i).cells) →
      TickTerminalRoot.finishCost (H:=H) (J:=Jmax) Nets Wires wireStart wireTable head own m≤allowance) :
    TickTerminalRoot.terminalInput (u:=age) (H:=H) (J:=Jmax) Nets Wires pin wireStart wireTable head own allowance m := by
  let valuesAt:=values streams ends
  have lists : TickTerminalRoot.rootIds age head own m=List.ofFn rank := by
    calc
      _=(roots).map (NavigationPass.RootArchive.terminalRank R v.1) := selected
      _=(List.ofFn (roots).get).map _ := by rw [List.ofFn_get]
      _=List.ofFn rank := by rw [List.map_ofFn]; rfl
  have nBound : (roots).length≤head.roots := by
    rw [←show (TickTerminalRoot.rootIds age head own m).length=(roots).length by rw [lists,List.length_ofFn]]
    change ((List.range head.roots).filter _).length ≤ head.roots
    simpa only [List.length_range] using List.length_filter_le _ (List.range head.roots)
  have regFit : (TickTerminalRoot.rootIds age head own m).length≤TickWorkspace.stride age := by
    rw [lists,List.length_ofFn];omega
  have actual (i : Fin (roots).length) : (valuesAt (current i)).pins=(result).1.width ((roots).get i) ∧
      HEq (valuesAt (current i)).net (Nets i) := R.archivePlanNetwork v.1 J.steps U N C O path zero ((roots).get i)
  have rawHidden (i : Fin (roots).length) : (Nets i).internal≤TickWorkspace.stride age := by
    have all : (∑ j,(Nets j).internal)=(TickTerminalRoot.forest Nets Wires).internal := by
      rw [TickTerminalRoot.forest,TickSlotForest.internal]; rfl
    exact (Finset.single_le_sum (fun j _=>Nat.zero_le ((Nets j).internal)) (Finset.mem_univ i)).trans (all.le.trans bitRoom)
  apply TickTerminalRoot.terminalInput_of_ledger Nets Wires pin wireStart wireTable agePos space head own valuesAt Q
    (TickTerminalRoot.ledgerDirectory Q head own before s6 ownerWords) (R.finalArchive v.1 C O path).1.first
    ((congrArg Fin.val (Q.durable _ firstKept)).trans first) current rank _ rootsFit lists pickedRoots resultRoom rootRoom
    rowsRoom bitRoom low keepPins physical (fun i=>(actual i).1) (fun i=>(actual i).2) streamFit endFit _ _ allowance _
  · intro i
    exact congrArg ((R.finalArchive v.1 C O path).1.first+·) (num ((R.finalSite v.1).symm ((roots).get i)))
  · intro i
    apply TickTerminalRoot.localMetadataFit _ _ library
    have upper:=TickWorkspace.word_space (i:=1) agePos (by omega)
    have bank : TickWorkspace.base age 1=2*TickWorkspace.stride age:=rfl
    rw [bank] at upper
    have h:=mapFit i
    rw [(actual i).1] at h
    have b:=rawHidden i
    change ((result).2 ((roots).get i)).compile.internal ≤ TickWorkspace.stride age at b
    omega
  · intro i μ frame pos length rowOffset bitOffset hit cache
    let storedImage:=((geometry i).fromLedger Q (keepGeometry i)).retain space (TickTerminalRoot.beforeAfter agePos space head own m μ regFit frame)
    have idFit : 8*(current i).val+6≤TickWorkspace.stride age := by have:=(current i).isLt;omega
    have rowAll : (∑ i,(Nets i).cells)=(TickTerminalRoot.forest Nets Wires).cells := rfl
    have placed : rowStart Nets i+(Nets i).cells≤(TickTerminalRoot.forest Nets Wires).cells :=
      (TickTerminalRoot.prefixCell (fun i=>(Nets i).cells) i).trans rowAll.le
    have countRows : (valuesAt (current i)).net.cells=(Nets i).cells :=
      (TickTerminalRoot.netAt (actual i).1 _ _ (actual i).2 cache.rows).1
    apply ledgerGeometry M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np C O path zero
      ((roots).get i) streams ends wireStart wireTable μ cache hit storedImage space wordFit idFit _ tableFit (mapFit i)
      (streamFit i) (endFit i).2 _ wireAt
    · rw [pos];have:=i.isLt;omega
    · rw [rowOffset,countRows];omega
  · intro observations
    apply time
    intro i
    let arena:=mounted age PINS wireStart wireTable
    let μ:=decrease arena (images arena (rootStart age head own m) i.val)
    obtain ⟨frame,hit,cache⟩:=observations i
    let geom:=((geometry i).fromLedger Q (keepGeometry i)).retain space (TickTerminalRoot.beforeAfter agePos space head own m μ regFit frame)
    obtain ⟨a,b,c',rows⟩:=HalfImage.iteration_sizes wireStart wireTable μ X _ _ geom _ cache hit
    exact ⟨a,b,c',rows.trans (TickTerminalRoot.netAt (actual i).1 _ _ (actual i).2 cache.rows).1⟩

theorem selected_interior_spec {age H Jmax : ℕ} (wireStart wireTable : ℕ)
    (pin : Fin PINS→Bool) (streams ends : Fin total→ℕ)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*age^10))
    (D : Directory (16*age^10) total) (keep : ℕ→Prop) (input : Memory (16*age^10))
    (archive : HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word (16*age^10)) (fs : List HistoryStageBody.Physical.Family)
    (cost : ℕ→ℕ) (inside : ℕ) (seedCost : Fin total→ℕ) (stageCost : Fin total→HistoryStageBody.Physical.Family→ℕ)
    (source : HistoryStageBody.Physical.NativeVisits age archive shape pub fs input D (values streams ends)
      TickTerminalRoot.tag keep cost inside seedCost stageCost)
    (before : TickTerminalRoot.directoryInput age head own input)
    (s6 : ∀ i : Fin 8,keep (TickWorkspace.base age 6+i.val))
    (ownerWords : ∀ j<head.roots,keep (TickPhysicalABI.directory age 1+2*j) ∧ keep (TickPhysicalABI.directory age 1+2*j+1))
    (firstKept : keep (TickPhysicalABI.directory age 3))
    (first : (input (TickPhysicalABI.directory age 3)).val=(R.finalArchive v.1 C O path).1.first)
    (num : R.FinalNumbered v.1 C O path) (rootsFit : ∀i,rank i<2^(16*age^10))
    (groupWord : keep (TickWorkspace.base age 1)) (slotWord : keep (TickWorkspace.base age 1+3))
    (selected : TickTerminalRoot.rootIds age head own input=(roots).map (NavigationPass.RootArchive.terminalRank R v.1))
    (pickedRoots : ∀ i, picked D (current i).val=true)
    (agePos : 1≤age) (space : 65≤TickWorkspace.stride age)
    (wordFit : PINS<2^(16*age^10) ∧ wireStart<2^(16*age^10) ∧ wireTable<2^(16*age^10))
    (resultRoom : 8*total≤TickWorkspace.stride age) (rootRoom : 2*head.roots≤TickWorkspace.stride age/4)
    (rowsRoom : 4*(TickTerminalRoot.forest Nets Wires).cells≤TickWorkspace.stride age)
    (bitRoom : (TickTerminalRoot.forest Nets Wires).internal≤TickWorkspace.stride age)
    (low : BitLayout.cellsBase PINS H≤TickWorkspace.stride age)
    (library : Fintype.card ((Fin 3→Bool)→F)≤2^(16*age^10))
    (keepPins : ∀ z<BitLayout.cellsBase PINS H,keep z)
    (physical : ∀ z<BitLayout.cellsBase PINS H,input z=TickMountedPins.memory pin z)
    (geometry : ∀ i, HalfImage X (R.physicalTerminal v.1 ((roots).get i)) age (current i).val wireTable input)
    (keepGeometry : ∀i j,(geometry i).reads j→keep j)
    (tableFit : 7*(2*(R.terminalLayer v.1).degree+2)≤TickWorkspace.stride age)
    (mapFit : ∀i,64+(values streams ends (current i)).pins≤TickWorkspace.stride age)
    (streamFit : ∀i,let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.stream ∧ val.stream+4*val.net.cells≤TickWorkspace.base age 14)
    (endFit : ∀i, let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.ext ∧ val.ext+val.external≤TickWorkspace.base age 14)
    (wireAt : wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+(R.plan.write E v.1).length)
    (allowance : ℕ)
    (time : ∀ m,Ledger age D TickTerminalRoot.tag (values streams ends) keep input total m →
    (∀i : Fin (roots).length,
      let A':=mounted age PINS wireStart wireTable
      let raw:=natMemory (decrease A' (images A' (rootStart age head own m) i.val))
      let tape:=terminal A' raw
      tape.halves=2*(R.terminalLayer v.1).degree ∧
        (∑j : Fin tape.halves,(half tape raw j.val).width)=R.terminalIncident v.1 ((roots).get i) ∧
        tape.ext=(values streams ends (current i)).external ∧ tape.rows=(Nets i).cells) →
      TickTerminalRoot.finishCost (H:=H) (J:=Jmax) Nets Wires wireStart wireTable head own m≤allowance) :
    (HistoryStageBody.Physical.selected (16*age^10) age archive shape pub fs).Spec (·=input)
      (fun _ m=>TickTerminalRoot.terminalInput (u:=age) (H:=H) (J:=Jmax) Nets Wires pin
        wireStart wireTable head own allowance m) inside := by
  refine _root_.OAI.ThreeFlat.RAM.PhysicalProcedure.Procedure.Spec.mono
    (HistoryStageBody.Physical.NativeVisits.run age archive shape pub fs input D (values streams ends)
      TickTerminalRoot.tag keep cost inside seedCost stageCost source) (fun _ h=>h) ?_ le_rfl
  intro _ m Q
  have ids : TickTerminalRoot.rootIds age head own m=TickTerminalRoot.rootIds age head own input := by
    change (List.range head.roots).filter (TickSlotLookup.matchesOwner own (m (TickWorkspace.base age 1))
      (m (TickWorkspace.base age 1+3)))=_
    rw [Q.durable _ groupWord,Q.durable _ slotWord]; rfl
  exact selected_terminalInput M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np
    C O path zero arch work pairs teams slot wireStart wireTable pin streams ends head own D keep input m Q before
    s6 ownerWords firstKept first num rootsFit (ids.trans selected) pickedRoots agePos space wordFit resultRoom rootRoom
    rowsRoom bitRoom low library keepPins physical geometry keepGeometry tableFit mapFit streamFit endFit wireAt
    allowance (time m Q)

/-- The chosen native slot uses the S43 schedule for both the selected scan and the actual
terminal copy. The two uniform allowances are chosen before reading the slot memory. -/
theorem selected_interior_fixed {age : ℕ} (wireStart wireTable : ℕ)
    (pin : Fin PINS→Bool) (streams ends : Fin total→ℕ)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*age^10))
    (D : Directory (16*age^10) total) (keep : ℕ→Prop) (input : Memory (16*age^10))
    (archive : HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word (16*age^10)) (fs : List HistoryStageBody.Physical.Family)
    (cost : ℕ→ℕ) (inside : ℕ) (seedCost : Fin total→ℕ) (stageCost : Fin total→HistoryStageBody.Physical.Family→ℕ)
    (source : HistoryStageBody.Physical.NativeVisits age archive shape pub fs input D (values streams ends)
      TickTerminalRoot.tag keep cost inside seedCost stageCost)
    (before : TickTerminalRoot.directoryInput age head own input)
    (s6 : ∀ i : Fin 8,keep (TickWorkspace.base age 6+i.val))
    (ownerWords : ∀ j<head.roots,keep (TickPhysicalABI.directory age 1+2*j) ∧ keep (TickPhysicalABI.directory age 1+2*j+1))
    (firstKept : keep (TickPhysicalABI.directory age 3))
    (first : (input (TickPhysicalABI.directory age 3)).val=(R.finalArchive v.1 C O path).1.first)
    (num : R.FinalNumbered v.1 C O path) (rootsFit : ∀i,rank i<2^(16*age^10))
    (groupWord : keep (TickWorkspace.base age 1)) (slotWord : keep (TickWorkspace.base age 1+3))
    (selected : TickTerminalRoot.rootIds age head own input=(roots).map (NavigationPass.RootArchive.terminalRank R v.1))
    (pickedRoots : ∀ i, picked D (current i).val=true)
    (agePos : 1≤age) (space : 65≤TickWorkspace.stride age)
    (wordFit : PINS<2^(16*age^10) ∧ wireStart<2^(16*age^10) ∧ wireTable<2^(16*age^10))
    (resultRoom : 8*total≤TickWorkspace.stride age) (rootRoom : 2*head.roots≤TickWorkspace.stride age/4)
    (rowsRoom : 4*(TickTerminalRoot.forest Nets Wires).cells≤TickWorkspace.stride age)
    (bitRoom : (TickTerminalRoot.forest Nets Wires).internal≤TickWorkspace.stride age)
    (low : BitLayout.cellsBase PINS (TickCursorSetup.hidden age)≤TickWorkspace.stride age)
    (library : Fintype.card ((Fin 3→Bool)→F)≤2^(16*age^10))
    (keepPins : ∀ z<BitLayout.cellsBase PINS (TickCursorSetup.hidden age),keep z)
    (physical : ∀ z<BitLayout.cellsBase PINS (TickCursorSetup.hidden age),input z=TickMountedPins.memory pin z)
    (geometry : ∀ i, HalfImage X (R.physicalTerminal v.1 ((roots).get i)) age (current i).val wireTable input)
    (keepGeometry : ∀i j,(geometry i).reads j→keep j)
    (tableFit : 7*(2*(R.terminalLayer v.1).degree+2)≤TickWorkspace.stride age)
    (mapFit : ∀i,64+(values streams ends (current i)).pins≤TickWorkspace.stride age)
    (streamFit : ∀i,let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.stream ∧ val.stream+4*val.net.cells≤TickWorkspace.base age 14)
    (endFit : ∀i, let val:=values streams ends (current i)
      TickWorkspace.base age 12≤val.ext ∧ val.ext+val.external≤TickWorkspace.base age 14)
    (wireAt : wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+(R.plan.write E v.1).length)
    (startup : ℕ) (fixed : 32*TickCursorSetup.overhead F≤age) (ageClock : 152+1+TraceVolume.cm≤age)
    (sites : total≤2^(age^10-age^4)) (rootCount : head.roots≤total)
    (clock : arch.slotBudget=TraceVolume.cap age/4) (boot : startup≤2*age^152)
    (walk : inside≤17+24*total+∑ i:Fin total,if picked D i.val then cost i.val else 0)
    (price : (∑i:Fin total,if picked D i.val then cost i.val else 0)≤(TraceVolume.cap age/4)/4)
    (degree rate : ℕ) (halves : 2*(R.terminalLayer v.1).degree≤degree)
    (tariff : rootFactor*(degree+4*rate+3)≤arch.nodeBank.unitWork)
    (typed : ∀ z∈roots,let charge:=R.chargeAt v.1 C work z
      1≤charge ∧ (((result).2 z).compile.cells≤rate*charge) ∧ (result).1.width z≤2*charge) :
    startup+inside≤TraceVolume.cap age/8 ∧
    (HistoryStageBody.Physical.selected (16*age^10) age archive shape pub fs).Spec (·=input)
      (fun _ m=>TickTerminalRoot.terminalInput (u:=age) (H:=TickCursorSetup.hidden age)
        (J:=TickCursorSetup.cells age) Nets Wires pin wireStart wireTable head own (TraceVolume.cap age/8) m) inside := by
  let weight:=fun z=>arch.nodeBank.unitWork*R.chargeAt v.1 C work z
  have live : (roots).length≤head.roots:=by
    have len:=congrArg List.length selected
    rw [List.length_map] at len
    rw [←len]
    change ((List.range head.roots).filter _).length≤head.roots
    simpa only [List.length_range] using List.length_filter_le _ (List.range head.roots)
  have scheduled : (∑i:Fin (roots).length,weight ((roots).get i))≤(TraceVolume.cap age/4)/4:=by
    have sum:=arch.teamRoots_budget R v.1 C work pairs c teams g.val slot
    rw [clock] at sum
    change ((roots).map weight).sum≤_ at sum
    have reindex : List.ofFn (fun i : Fin (roots).length => weight ((roots).get i)) = (roots).map weight := by
      simpa only [List.ofFn_get] using List.ofFn_comp' (roots).get weight
    rwa [←List.sum_ofFn, reindex]
  have front:=TickCursorSetup.uniform_clocks (F:=F) (gCells:=0) (gHidden:=0)
    (finish:=0) fixed ageClock sites rootCount live boot walk price (by exact Nat.zero_le _)
  refine ⟨front.1,?_⟩
  apply selected_interior_spec M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np
    C O path zero arch work pairs teams slot wireStart wireTable pin streams ends head own D keep input archive
    shape pub fs cost inside seedCost stageCost source before s6 ownerWords firstKept first num rootsFit
    groupWord slotWord selected pickedRoots agePos space wordFit resultRoom rootRoom rowsRoom bitRoom low
    library keepPins physical geometry keepGeometry tableFit mapFit streamFit endFit wireAt (TraceVolume.cap age/8)
  intro m ledger sizes
  apply (TickCursorSetup.selected_pass_clocks Nets Wires wireStart wireTable head own m
    (fun i=>weight ((roots).get i)) fixed ageClock sites rootCount live boot walk price scheduled ?_).2
  intro i
  have h:=typed ((roots).get i) (List.get_mem roots i)
  have width:=archived_root_width M t hF st B hk c hc extent R J N T v g room advice nt ns np C O path zero
    ((roots).get i) streams ends
  apply TickCursorSetup.root_iteration_price _ _ i.val (R.chargeAt v.1 C work ((roots).get i)) rate degree
    ((result).1.width ((roots).get i)) (Nets i).cells arch.nodeBank.unitWork h.1 h.2.1 h.2.2 tariff
  obtain ⟨count,incident,external,rows⟩:=sizes i
  exact ⟨count.trans_le halves,(congrArg₂ Nat.add external incident).trans width,rows⟩



end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.PhysicalStage.Run
variable {F : Type} [Field F]

/-- Only the live final layer needs a word-sized incident width. Earlier receipts
are available at the fixed journal image without imposing a bound on their incidences. -/
theorem terminalHalfRows (W : ℕ) (safe : ℕ→Prop) (mem : ℕ→ℕ) {d l : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (seed : (∀ z,A.incidentWidth z<2^W)→State.HalfRows O safe mem)
    (seen : r.ArchiveVisits (fun M j _ _ row=>(∀ z,(M.next j).incidentWidth z<2^W)→
      State.HalfRows row.sites safe mem) h C O path)
    (fit : ∀ z,(r.terminalLayer h).state.incidentWidth z<2^W) :
    State.HalfRows (r.endSites h C O path) safe mem := by
  induction r with
  | done A=>exact seed fit
  | step M next ih=>exact ih h.1 (tailHistory M next h) (C.2 h.1) path.1.sites path.2 seen.1 seen.2 fit



end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected Diagonal.TickWorkspace
variable {u : ℕ}

theorem HalfImage.slotKeep_reads {d l root wp : ℕ} {X : Diagonal.PhysicalStage.State d l} {z : X.Site}
    {m : Memory (16*u^10)} (G : HalfImage X z u root wp m) (room : 65≤ stride u)
    (node : base u 19≤G.nodeBase) (head : base u 19≤G.header) (entries : base u 19≤G.entries)
    (prefixLow : base u 19≤wp) (i : ℕ) (h : G.reads i) : slotKeep u i := by
  rcases h with rfl|rfl|h|h|h
  · left;change 12*stride u+3*(stride u/4)+1<13*stride u;omega
  · right;omega
  · exact Or.inr (head.trans h.1)
  · exact Or.inr (entries.trans h.1)
  · exact Or.inr (prefixLow.trans h.1)

theorem slotKeep.prototype (at_ len : ℕ) (prototype : base u 53≤at_) (j : Fin len) :
    slotKeep u (at_+j.val) := by
  right
  have sep:=apart (u:=u) (by decide : 19<53)
  omega

theorem slotKeep.publicReader (j : Fin FixedTraceProgram.P) : slotKeep u (base u 57+j.val) :=
  slotKeep.prototype _ _ (by have:=apart (u:=u) (by decide : 53<57);omega) j

theorem slotKeep.outside {i addr : ℕ} (bank : base u 12+(i+1)*(volume u)^2≤base u 13)
    (results : base u 13+8*i+8≤base u 14) (h : slotKeep u addr) : OutsideNode u i addr := by
  have b:=apart (u:=u) (by decide : 12<13)
  have c:=apart (u:=u) (by decide : 12<14)
  have e:=apart (u:=u) (by decide : 13<19)
  have f:=apart (u:=u) (by decide : 14<19)
  rcases h with low|high
  · exact ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩
  · exact ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inl high)⟩

theorem ledger_seed_banks {W n : ℕ} {F : Type*} {D : Directory W n} {id : ((Fin 3→Bool)→F)→ℕ}
    {v : Fin n→NodeValue F} {m input : Memory W} (Q : Ledger u D id v (slotKeep u) input n m) (count : ℕ) :
    (∀ j : Fin count, m (base u 53+j.val)=input (base u 53+j.val)) ∧
    (∀ j : Fin FixedTraceProgram.P,m (base u 57+j.val)=input (base u 57+j.val)) :=
  ⟨fun j=>Q.durable _ (slotKeep.prototype _ _ le_rfl j),fun j=>Q.durable _ (slotKeep.publicReader j)⟩



end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open Computability.VPVNP.BurstRAM NavigationPass
variable {F : Type} [Field F] {W K headEnd heapEnd : ℕ} {cur ctr : Word W} {m : Memory W}

/-- At the actual last stage, the recorded shrink or refresh pass supplies the
full graph ordered half-edge records. The empty program uses its seed image. -/
theorem terminalHalfRows_of_visits (safe : ℕ→Prop) {d l : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (seed : (∀ z,A.incidentWidth z<2^W)→State.HalfRows O safe (fun i=>(m i).val))
    (seen : r.ArchiveVisits (RecordedStep K cur ctr headEnd heapEnd m) h C O path)
    (heapSafe : ∀ i,headEnd≤ i ∧ i<heapEnd→safe i)
    (fit : ∀ z,(r.terminalLayer h).state.incidentWidth z<2^W) :
    State.HalfRows (r.endSites h C O path) safe (fun i=>(m i).val) := by
  apply r.terminalHalfRows W safe _ h C O path seed _ fit
  refine ArchiveVisits.mono ?_ r h C O path seen
  intro d l D L A M j prior cost row visit bounded
  rcases visit with shrink|refresh
  · exact shrink.halfRows.transfer (fun _ _=>rfl) heapSafe
  · exact (refresh.halfRows bounded).transfer (fun _ _=>rfl) heapSafe



end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM Diagonal Diagonal.PhysicalStage Diagonal.TickWorkspace
open scoped Classical
noncomputable section

/-- Join the output of the chronological graph pass to the final root's native
S44 pointer and the live terminal edge-prefix register. -/
def HalfImage.of_rows {u d l root wp : ℕ} {X : State d l} (O : X.ArchiveSites) (z : X.Site)
    (m : Memory (16*u^10)) (nodes : ℕ) (positive : 0<d)
    (directory : natMemory m (TickPhysicalABI.directory u 3+1)=nodes)
    (pointer : natMemory m (nodes+8*root+6)=O.layer.incident+(O.ord z).val*2)
    (rows : State.HalfRows O (fun a=>base u 19≤a ∧ a<2^(16*u^10)) (natMemory m))
    (node : StableInterval u (nodes+8*root+6) 1) (prefixBank : StableInterval u wp X.edgeCount)
    (prefixAt : ∀ (i : Fin X.edgeCount) (j : Fin (X.wireWidth i)),natMemory m (wp+i.val)+j.val=(X.bitAddress i j).val) :
    HalfImage X z u root wp m := by
  let hdr:=O.layer.incident+(O.ord z).val*2
  let arr:=natMemory m (hdr+1)
  have upper:=apart (u:=u) (by decide : 18<19)
  have hd0:=rows.headerSafe z 0
  have hd1:=rows.headerSafe z 1
  change base u 19≤hdr+0 ∧ hdr+0<2^(16*u^10) at hd0
  change base u 19≤hdr+1 ∧ hdr+1<2^(16*u^10) at hd1
  let last : Fin (2*d):=⟨2*d-1,by omega⟩
  let first : Fin (2*d):=⟨0,by omega⟩
  have en0:=rows.entriesSafe z first 0
  have en1:=rows.entriesSafe z last 3
  change base u 19≤arr+4*0+0 ∧ arr+4*0+0<2^(16*u^10) at en0
  change base u 19≤arr+4*(2*d-1)+3 ∧ arr+4*(2*d-1)+3<2^(16*u^10) at en1
  exact ⟨nodes,hdr,arr,directory,pointer,rows.count z,rfl,rows.edge z,rows.width z,rows.start z,prefixAt,
    node,⟨Or.inr (by omega),by omega⟩,⟨Or.inr (by omega),by omega⟩,prefixBank⟩



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM Diagonal Diagonal.PhysicalStage Diagonal.TickWorkspace
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {u d l : ℕ} {A : State d l}

def HalfImage.of_terminal (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (v : (r.plan.finish h).Site) (wp : ℕ) (m : Memory (16*u^10))
    (degree : 0<(r.terminalLayer h).degree)
    (halves : State.HalfRows (r.endSites h C O path) (fun a=>base u 19≤a ∧ a<2^(16*u^10)) (natMemory m))
    (nodes : m (TickPhysicalABI.directory u 3+1)=(base u 44 : Word (16*u^10)))
    (pointer : m (base u 44+8*(r.archivePlanIndex h C O path v).val+6)=
      (((r.finalArchive h C O path).1.incident+2*((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val:ℕ):Word (16*u^10)))
    (word : base u 44<2^(16*u^10))
    (nodeBank : StableInterval u (base u 44+8*(r.archivePlanIndex h C O path v).val+6) 1)
    (prefixBank : StableInterval u wp (r.terminalLayer h).state.edgeCount)
    (prefixAt : ∀ (i : Fin (r.terminalLayer h).state.edgeCount) (j : Fin ((r.terminalLayer h).state.wireWidth i)),
      natMemory m (wp+i.val)+j.val=((r.terminalLayer h).state.bitAddress i j).val) :
    HalfImage (r.terminalLayer h).state (r.physicalTerminal h v) u (r.archivePlanIndex h C O path v).val wp m := by
  let z:=r.physicalTerminal h v
  let endO:=r.endSites h C O path
  have ord : (endO.ord z).val=((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val := by
    have j:=r.archiveLastOrdinal h C O path ((r.finalSite h).symm v)
    rw [r.finalSite_physical] at j
    change endO.layer.first+(endO.ord z).val=(r.finalArchive h C O path).1.first+_ at j
    have layerFirst : endO.layer.first=(r.finalArchive h C O path).1.first := congrArg (·.first) (r.endSites_layer h C O path)
    omega
  have head : (r.finalArchive h C O path).1.incident+2*((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val=
      endO.layer.incident+(endO.ord z).val*2 := by
    have inc : endO.layer.incident=(r.finalArchive h C O path).1.incident := congrArg (·.incident) (r.endSites_layer h C O path)
    rw [ord,inc];omega
  have hdrFit : endO.layer.incident+(endO.ord z).val*2<2^(16*u^10) := (halves.headerSafe z 0).2
  apply HalfImage.of_rows endO z m (base u 44) degree _ _ halves nodeBank prefixBank prefixAt
  · exact (congrArg Fin.val nodes).trans (Fin.val_cast_of_lt word)
  · rw [head] at pointer
    exact (congrArg Fin.val pointer).trans (Fin.val_cast_of_lt hdrFit)



end
end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM RAM PhysicalStage NodePublication NavigationNodeRows RootArchive RAM.TickPhysicalABI
open TickWorkspace TickTerminalRoot
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {d l q H J : ℕ} {X : State d l}
variable (pars : Parameters)
local notation "W" => 16*pars.age^10
variable {B : TickActiveROM.Layout} {clock : TickChronology.Clock}
  {fit : Contraction.Fits (TickWeightedBank.shape F q H J) (16*pars.age^10)}
local notation "b" => TickWorkspace.base pars.age
local notation "zone" => fun a=>(b 20≤a ∧ a<b 40) ∨ (b 49≤a ∧ a<b 53)

set_option Elab.async false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- The real slot starts with the S44 pointer and prefix values of the original
decoded history, after native node publication, scheduling, and prototype startup. -/
def Selection.warm_half_image (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) {budget : ℕ} (m out prepared warm : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤b 6) (requests : B.auxRequest+8*B.bits≤b 6)
    (hdr : 16*layers.length≤ stride pars.age) (volume : ∀ t∈layers,8*(t.actual.first+t.actual.count)≤ stride pars.age)
    (startup : ∀ a,a<b 53→warm a=prepared a)
    (word : b 53≤2^W) (heapStart : b 20 ≤ s.headerEnd) (heapLimit : s.heapEnd≤b 40)
    (first : State.HalfRows O zone (natMemory m))
    (widths : ∀z,(r.terminalLayer s.history).state.incidentWidth z<2^W)
    (positive : 0<(r.terminalLayer s.history).degree)
    (wp : ℕ) (prefixStart : b 20≤wp) (prefixEnd : wp+(r.terminalLayer s.history).state.edgeCount≤b 40)
    (prefixAt : ∀ (i : Fin (r.terminalLayer s.history).state.edgeCount)
      (j : Fin ((r.terminalLayer s.history).state.wireWidth i)),natMemory m (wp+i.val)+j.val=
      ((r.terminalLayer s.history).state.bitAddress i j).val)
    (z : (r.plan.finish s.history).Site) :
    {G : HalfImage (r.terminalLayer s.history).state (r.physicalTerminal s.history z) pars.age
      (r.archivePlanIndex s.history C O s.path z).val wp warm // ∀ addr,G.reads addr→slotKeep pars.age addr} := by
  let k:=r.archivePlanIndex s.history C O s.path z
  let a:=parameterArchive pars degree stages W
  let stride:=TickWorkspace.stride pars.age
  have fixed : 128≤ stride:=sizes.fixed
  have small : k.val<a.rootsTotal := by change k.val<a.firstFinal+a.rootCount;rw [s.first,s.card];exact k.isLt
  have count : 8*a.rootsTotal≤ stride:=sizes.nodes
  have high z (h : zone z) : b 19≤z ∧ z<b 53 := by
    change (21*stride≤z ∧ z<41*stride) ∨ (50*stride≤z ∧ z<54*stride) at h
    change 20*stride≤z ∧ z<54*stride
    omega
  have h20 : b 6≤b 20:=by change 7*stride≤21*stride;omega
  have kept (i : ℕ) (h : zone i) : warm i=m i := by
    rw [startup i (high i h).2]
    exact s.prepared_journal_cell pars degree stages r C O seed start pay layers m out prepared ran x nodes teams groups
      done sizes headers (bounds.trans h20) (requests.trans h20) hdr volume i (h.imp_right And.left)
  have last:=r.terminalHalfRows_of_visits zone s.history C O s.path (fun _=>first) s.visits
    (fun i h=>Or.inl ⟨heapStart.trans h.1,h.2.trans_le heapLimit⟩) widths
  have rows:=last.transfer (fun i hi=>congrArg Fin.val (kept i hi))
    (fun i hi=>(high i hi).imp_right (fun h=>h.trans_le word))
  obtain ⟨node,ptr⟩:=s.prepared_terminal_half_pointers pars degree stages r C O seed start pay layers m out prepared
    ran x nodes teams groups done sizes headers bounds requests z
  have dirFit : TickPhysicalABI.directory pars.age 3+1<b 53 := by
    change 12*stride+3*(stride/4)+1<54*stride;omega
  have offFit : b 44+8*k.val+6<b 53 := by change 45*stride+8*k.val+6<54*stride;omega
  have wr : b 44<2^W := by change 45*stride<_;change 54*stride≤_ at word;omega
  let loc:=r.physicalTerminal s.history z
  let endO:=r.endSites s.history C O s.path
  let head:=endO.layer.incident+(endO.ord loc).val*2
  have headHigh : b 19≤head := (rows.headerSafe loc 0).1
  have entryHigh : b 19≤natMemory warm (head+1) := (rows.entriesSafe loc ⟨0,by omega⟩ 0).1
  refine ⟨HalfImage.of_terminal r s.history C O s.path z wp warm positive rows
    ((startup _ dirFit).trans node) ((startup _ offFit).trans ptr) wr ?_ ?_ ?_,?_⟩
  · refine ⟨Or.inr ?_,?_⟩
    · change 19*stride+stride≤45*stride+8*k.val+6;omega
    · change 45*stride+8*k.val+6+1≤_;change 54*stride≤_ at word;omega
  · refine ⟨Or.inr ?_,?_⟩
    · change 19*stride+stride≤wp;change 21*stride≤wp at prefixStart;omega
    · exact prefixEnd.trans ((by change 41*stride≤54*stride;omega : b 40≤b 53).trans word)
  · intro i j
    have h : zone (wp+i.val):=Or.inl ⟨by omega,by have:=i.isLt;omega⟩
    exact (congrArg (fun w : Word W=>w.val+j.val) (kept _ h)).trans (prefixAt i j)
  · have nodeLow : b 19 ≤ b 44 := by change 20*stride ≤ 45*stride; omega
    have prefixLow : b 19 ≤ wp := by
      change 20*stride ≤ wp
      change 21*stride ≤ wp at prefixStart
      omega
    exact HalfImage.slotKeep_reads _ (by omega) nodeLow headHigh entryHigh prefixLow



end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM Diagonal Diagonal.TickWorkspace
open scoped Fin.CommRing
variable {u : ℕ}

structure SlotKeepFacts (u roots stop : ℕ) : Prop where
  groupWord : slotKeep u (base u 1)
  slotWord : slotKeep u (base u 1+3)
  header : ∀ i : Fin 8,slotKeep u (base u 6+i.val)
  first : slotKeep u (TickPhysicalABI.directory u 3)
  owners : ∀ i<roots,slotKeep u (TickPhysicalABI.directory u 1+2*i) ∧
    slotKeep u (TickPhysicalABI.directory u 1+2*i+1)
  pins : ∀ i<stop,slotKeep u i

theorem slotKeep_facts {roots stop : ℕ} (space : 65≤ stride u)
    (ownerRoom : 2*roots≤ stride u/4) (low : stop≤ stride u) : SlotKeepFacts u roots stop := by
  let s:=stride u
  refine ⟨Or.inl ?_,Or.inl ?_,?_,Or.inl ?_,?_,?_⟩
  · change 2*s<13*s;omega
  · change 2*s+3<13*s;omega
  · intro i;left;change 7*s+i.val<13*s;have:=i.isLt;omega
  · change 12*s+3*(s/4)<13*s;omega
  · intro i hi
    have fit : 12*s+1*(s/4)+2*i+1<13*s:=by omega
    have first : 12*s+1*(s/4)+2*i<13*s:=by omega
    exact ⟨Or.inl first,Or.inl fit⟩
  · intro i hi;left;change i<13*s;omega

/-- The actual bootstrap writes only at and above S53. All selection and input
array reads needed by the terminal loop can therefore use the same ranked slot. -/
theorem warm_directory {W stop : ℕ} (h : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (prepared warm : Memory W) (space : 65≤ stride u)
    (ownerRoom : 2*h.roots≤ stride u/4) (low : stop≤ stride u)
    (startup : ∀ i,i<base u 53→warm i=prepared i)
    (before : directoryInput u h own prepared) (first : ℕ)
    (atFirst : (prepared (TickPhysicalABI.directory u 3)).val=first)
    (ranks : List ℕ) (ids : rootIds u h own prepared=ranks) :
    directoryInput u h own warm ∧ (warm (TickPhysicalABI.directory u 3)).val=first ∧
      rootIds u h own warm=ranks ∧ ∀ i<stop,warm i=prepared i := by
  let s:=stride u
  have same (i : ℕ) (hi : i<base u 12) : warm i=prepared i := startup _ (hi.trans_le (by change 13*s≤54*s;omega))
  have s6 (i : Fin 8) : warm (base u 6+i.val)=prepared (base u 6+i.val) := same _ (by change 7*s+i.val<13*s;have:=i.isLt;omega)
  have one : warm (base u 1)=prepared (base u 1):=same _ (by change 2*s<13*s;omega)
  have three : warm (base u 1+3)=prepared (base u 1+3):=same _ (by change 2*s+3<13*s;omega)
  refine ⟨⟨fun i=>(s6 i).trans (before.1 i),?_⟩,?_,?_,?_⟩
  · intro i hi
    have max : 12*s+1*(s/4)+2*i+1<13*s:=by omega
    have firstBound : 12*s+1*(s/4)+2*i<13*s:=by omega
    exact ⟨(same _ firstBound).trans (before.2 i hi).1,(same _ max).trans (before.2 i hi).2⟩
  · exact (congrArg Fin.val (same _ (by change 12*s+3*(s/4)<13*s;omega))).trans atFirst
  · simpa only [rootIds,TickRootScanInit.chosen,rootLookup,one,three] using ids
  · intro i hi;exact same i (by change i<13*s;omega)


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM Diagonal.TickWorkspace

/-- Geometric and table addresses used to construct the terminal forest fit the
native words at the selected H tick. -/
theorem slot_word_resources {F : Type} [Field F] [Fintype F] {u p h lut : ℕ}
    (x : TerminalWireArchive.Layout) (walk : TerminalWireArchive.Bounds x (16*u^10))
    (age : 1≤u) (space : 65≤ stride u) (low : BitLayout.cellsBase p h≤ stride u)
    (net : BitNetwork F p)
    (table : lut+8*((HistoryCompiledRows.library net).count+2)≤2^(16*u^10)) :
    (p<2^(16*u^10) ∧ x.oldSource<2^(16*u^10) ∧ x.prefixBase<2^(16*u^10)) ∧
      Fintype.card ((Fin 3→Bool)→F)≤2^(16*u^10) := by
  have bank:=word_space (i:=0) age (by omega)
  have old:=walk.oldBits
  have prefixBound:=walk.prefix
  change 2+p+h≤ stride u at low
  change lut+8*(Fintype.card ((Fin 3→Bool)→F)+2)≤_ at table
  exact ⟨⟨by omega,by omega,by omega⟩,by omega⟩


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM PhysicalStage
open scoped Fin.CommRing
variable {F : Type} [Field F]

/-- The native S11 first-final word is the ordinal used in the typed S44
directory, including an empty terminal range. -/
theorem first_word {W : ℕ} (a : RootArchive) (large : PublishSizes a W)
    (m : Memory W) (h : ∀i : Fin 3,m (TickPhysicalABI.directory a.age 3+i.val)=(a.rootWords i:Word W)) :
    (m (TickPhysicalABI.directory a.age 3)).val=a.firstFinal := by
  have e : m (TickPhysicalABI.directory a.age 3)=(a.firstFinal:Word W):=h 0
  have fit:=large.nodes
  have space:=large.address
  change 8*(a.firstFinal+a.rootCount)≤TickWorkspace.stride a.age at fit
  change 51*TickWorkspace.stride a.age<2^W at space
  exact (congrArg Fin.val e).trans (Fin.val_cast_of_lt (by omega))

theorem physical_rank {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (a : RootArchive)
    (first : a.firstFinal=(r.finalArchive h C O path).1.first) (number : r.FinalNumbered h C O path)
    (z : (r.plan.finish h).Site) :
    (r.archivePlanIndex h C O path z).val=a.firstFinal+terminalRank r h z := by
  rw [first]
  exact congrArg ((r.finalArchive h C O path).1.first+·) (number ((r.finalSite h).symm z))



end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
