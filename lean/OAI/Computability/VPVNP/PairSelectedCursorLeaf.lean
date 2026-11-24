import OAI.Computability.VPVNP.PairVertexFrameWrites
import OAI.Computability.VPVNP.PairSelectedPacketOrders
import OAI.Computability.VPVNP.PairVertexSelectedReport
import OAI.Computability.VPVNP.PairSimulationLeafReads
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-! # The native cursor leaves of the selected terminal history -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.SelectedCursorLeaf

open BurstRAM PrivateRAM DFS VertexImage CursorRouting CursorNetwork LeafStartup
open TreeDecode LocalHistory LeafHandler NodeArguments NetworkKernel CompressorRecords
open CompressorRecords.SourceTransport NativeFrame
open scoped Fin.CommRing

set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 10000
attribute [local irreducible] LeafRole.labelCount LeafRole.privateCount

private theorem leafDispatch {W n p r : ℕ} {S : Part → Segment} {V : Placement S p r}
    {M : Machine W p r 11} (link : Contains V M) (G offset hist : Word W) (m : Memory W)
    (handlers : NodeDispatch.Role → HookParser W n) (domain : Word W → Scratch W n → Prop)
    (body : (handlers .leaf).ExactOn domain M (V.entry .leaf) (V.dfsPC 3) V.dfs m) :
    (dispatcher handlers m offset).ExactOn
      (fun node s => ResidentGeometry s G offset hist ∧ domain node s ∧ NodeDispatch.role (m (offset+node).val) = .leaf)
      M (V.core (.roleBase 0)) (V.dfsPC 3) V.dfs m := by
  apply dispatch_exactOn link G offset hist m _ (fun _ _ h => h.1) handlers
  intro role
  constructor
  · intro node saved h bits job tail hit
    have eqn := h.2.symm.trans h.1.2.2
    subst role
    exact body.success node saved h.1.2.1 bits job tail hit
  · intro node bits c top pending h pc nodeReg stack endPos topReg endReg one fail
    have eqn := h.2.symm.trans h.1.2.2
    subst role
    exact body.reject node bits c top pending h.1.2.1 pc nodeReg stack endPos topReg endReg one fail

private theorem dispatch_footprint {w : ℕ} (allow : ℕ → Prop) (m : Memory w) (offset node : Word w)
    (tag : m (offset+node).val = 0) (addr : allow (offset+node).val) :
    Reads allow (dispatchEvents m offset node) ∧ after m (dispatchEvents m offset node) = m := by
  simp only [dispatchEvents,NodeDispatch.events,tag,ite_true,List.append_nil]
  refine ⟨TerminalFootprint.reads_append (TerminalFootprint.reads_ticks _ _) ?_,rfl⟩
  intro a v ha
  simp only [List.mem_cons,List.not_mem_nil,reduceCtorEq,or_false,false_or,Event.read.injEq] at ha
  exact ha.1 ▸ addr

private theorem pop {w n : ℕ} {R : LeafArena.Regions} {format : Packet → Prop}
    {stable : Scratch w n → Prop} {desc : ℕ → List ℕ} {head : Packet} {pending : List Packet} {s out : Scratch w n}
    (h : Frontier R.arguments format stable desc (head::pending) s) (outFrame : stable out)
    (typed : ∀ q, format q → q.node < R.nodes)
    (keep : ∀ i : {a : Word w // n ≤ a.val}, i.val.val < R.stackBase → out i = s i) :
    Frontier R.arguments format stable desc pending out := by
  apply h.pop outFrame
  intro q member fits stored
  apply stored.congr
  intro i
  let a : Word w := ((R.arguments.base q.node+i.val : ℕ) : Word w)
  have hv : a.val = R.arguments.base q.node+i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le fits.2.2)
  have above : n ≤ a.val := hv ▸ fits.1.trans (Nat.le_add_right _ _)
  have endRoom := R.node_before (typed q (h.prepared.2 q (List.mem_cons_of_mem _ member)).1)
  have tailRoom := R.hist_before
  have low : a.val < R.stackBase := by
    rw [hv,LeafArena.Regions.stackBase]
    have := i.isLt
    have := fits.2.1
    omega
  change rawScratch out a = rawScratch s a
  simpa only [rawScratch,dite_eq_left above] using keep ⟨a,above⟩ low

open private realized_counts from OAI.Computability.VPVNP.PairSimulationVertexJobs

/-- A successful leaf consumes one outstanding subtree without increasing
any histogram coordinate. The same effects therefore preserve its headroom. -/
private theorem budgetLeaf {W n : ℕ} {A : Type*} [CommRing A] {J : Type} [Fintype J]
    {κ : J → A} {N : Network} (P : SiteParsers κ N) (ptr : N.Site → ℕ × ℕ) (input : Packets N)
    (hook : HookParser W n) (arena : Arena) (format : Packet → Prop) (stable : Scratch W n → Prop)
    (desc : ℕ → List ℕ) (hist : Scratch W n → J → ℕ) (guard : VisitPath W n → Prop)
    (nodeCap limit : ℕ) (shape : ∀ u z, desc (input u z).node = [])
    (unchanged : ∀ u s bits job tail, hook.read ((ptr u).1 : Word W) s bits = some (job,tail) →
      ∀ l, hist (job.update s) l = hist s l) (zero : ∀ u z i l, (P.witnesses u z).exponents i l = 0)
    (basic : Subtrees hook (Frontier arena format stable desc) P (fun u => leafTree (ptr u)) input ∧
      Emits (Frontier arena format stable desc) hist guard P input (leafJobs P ptr)) :
    let valid := Budgeted arena format stable desc hist nodeCap limit
    Subtrees hook valid P (fun u => leafTree (ptr u)) input ∧ Emits valid hist guard P input (leafJobs P ptr) := by
  intro valid
  constructor
  · intro u z
    constructor
    · intro pending s bits out tail h read
      obtain ⟨selected,front⟩ := (basic.1 u z).sound pending s bits out tail h.frontier read
      change hook.decode [((ptr u).1 : Word W)] s bits = some (out,tail) at read
      rw [HookParser.decode] at read
      obtain ⟨⟨job,rest⟩,hit,done⟩ := Option.bind_eq_some_iff.mp read
      change some (job.update s,rest) = some (out,tail) at done
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj done).symm
      exact ⟨selected,h.advance (children := []) (shape u z) front (fun l =>
        (unchanged u s bits job tail hit l).le.trans (Nat.le_add_right _ _))⟩
    · intro pending s x tail h
      exact (basic.1 u z).complete pending s x tail h.frontier
  · intro u z x pending s h
    obtain ⟨jobs,eff⟩ := basic.2 u z x pending s h.frontier
    refine ⟨jobs,eff.realized,eff.ready,eff.framed,h.advance (children := []) (shape u z) eff.remaining ?_⟩
    intro l
    have hc := realized_counts eff.realized s eff.ready l
    simp only [leafJobs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,zero,Nat.add_zero] at hc
    exact hc.le.trans (Nat.le_add_right _ _)

variable {geometry rootFields shrink refresh : Segment} {p r w : ℕ}
    (V : Placement (segments geometry rootFields LeafRole.segment shrink refresh) p r)
    (M : Machine w p r 11)
    {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
    (D : PrimedCounter.Data Q s) {b l e degree pad : ℕ} [NeZero (b+l)]
    (hD : 1 < b+l) (hd : 2+pad = 2^degree) (budget : ProcessorBudget n (b+l) e w)
    {K : Type*} [CommRing K] {Label : Type} [Fintype Label] (f : Label → K)
    (bound : NominationClock D budget.tags budget.capFits (n^39))
    (m : Memory w) (header offset : Word w) (arity cap : ℕ)

local notation "regions" => fromHeader arity M.publicData header m
local notation "data" => leafWords arity M.publicData header offset m
local notation "fields" => LeafRole.addressFields data
local notation "X" => LeafArguments.state hD hd (2^e) w
local notation "leaves" => TraversalRows.sitePointers cap (Fin.val (fields LeafAddress.Field.base)) (siteOrder X)
local notation "sites" => nominationSites D budget.tags budget.capFits (cursorCoordinateLabels b l) hD hd f (n^39) bound

/-- Prepared cursor packets supply both the exact leaf reader and its native
zero-increment job. The concrete dispatch and role reader preserve every
pending argument below the verifier stacks, on every returned suffix. -/
theorem checks (link : Contains V M) (fit : (regions).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (hn : 2048 ≤ n) (hwidth : b+l ≤ w)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l) (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafStartup.steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w), LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser data D budget regions fit m (n^39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow (fields .shadow+site).val)
    (tag : ∀ u, m (offset+((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset+((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (stable : Scratch w n → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (regions).nodes ∧ q.node < 2^w)
    (cached : ∀ s, stable s → LeafSourceLoad.Cached (regions).cacheBase (rawScratch s) (LeafVisit.cacheWords D (b+l) e))
    (record : ∀ s, stable s → LeafGeometryLoad.Stored n (frameBase regions) (rawScratch s) data)
    (resident : ∀ s, stable s → ResidentGeometry s (frameBase regions : Word w) offset ((regions).histBase : Word w))
    (preserve : ∀ s out, stable s →
      (∀ i : {a : Word w // n ≤ a.val}, i.val.val < (regions).stackBase → out i = s i) → stable out)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (regions).histWords) :
    let input := fun v z => Packet.mk (leaves v).1 (packed X v z)
    let valid := Frontier (regions).arguments format stable desc
    let hook := dispatcher handlers m offset
    let guard := JobGuard V M m allow (fun j : VisitPath w n => countProbes j.trace ≤ 2 ∧ j.trace.length+17 ≤ n^40)
    Subtrees hook valid sites (fun v => leafTree (leaves v)) input ∧
      Emits valid (privateHistogram order (regions).histBase) guard sites input (leafJobs sites leaves) := by
  intro input valid hook guard
  let roleParser := LeafRole.parser (endAddr := n) data D budget regions fit m (n^39)
  let domain := LeafRole.Domain (endAddr := n) (e := e) data D hD hd regions cap (frameBase regions)
  have body := LeafRole.site_exact V M D hD hd budget m header offset arity cap (n^39) fit link
    stride rb rl span shadowFit headers size time room
  have exactDispatch := leafDispatch link (frameBase regions : Word w) offset ((regions).histBase : Word w) m
    handlers domain (leaf.symm ▸ body)
  have roleAt (u : (X).network.Site) : NodeDispatch.role (m (offset+((leaves u).1 : Word w)).val) = .leaf := by
    rw [tag]; rfl
  have ready (v : Position (b+l)) (z : (X).network.Half (lanePositions (cursorCoordinateLabels b l) v))
      (pending : List Packet) (s : Scratch w n) (h : valid (input (lanePositions (cursorCoordinateLabels b l) v) z::pending) s) :
      let node : Word w := (leaves (lanePositions (cursorCoordinateLabels b l) v)).1
      StoredCursorRow hD hd fields (regions).arguments node s cap v z ∧ domain node s := by
    intro node
    have ⟨hs,type,fits,stored⟩ := h.head
    have ⟨hl,hv⟩ := typed _ type
    have addr : node.val = (leaves (lanePositions (cursorCoordinateLabels b l) v)).1 := Nat.mod_eq_of_lt hv
    have fit' : (cursorPacket hD hd node.val v z).Fits (regions).arguments w n := by rw [addr]; exact fits
    have stored' : (cursorPacket hD hd node.val v z).Stored (regions).arguments s := by rw [addr]; exact stored
    exact ⟨⟨hwidth,stride,rb,rl,addr,fit',stored'⟩,⟨⟨addr ▸ hl,cached s hs,v,z,addr,fit',stored'⟩,record s hs⟩⟩
  have pops (u : (X).network.Site) (z : (X).network.Half u) (pending : List Packet) (s : Scratch w n)
      (bits tail : List Bool) (j : VisitPath w n) (h : valid (input u z::pending) s)
      (hit : roleParser.read ((leaves u).1 : Word w) s bits = some (j,tail)) : valid pending (j.update s) := by
    have keep := LeafRole.below_stack D budget (n^39) data regions fit m _ s bits tail j hit room
    exact pop h (preserve s _ h.frame keep) (fun q hq => (typed q hq).1) keep
  constructor
  · apply leaf_subtrees hook valid sites leaves input
    · intro u z pending s bits h
      obtain ⟨v,rfl⟩ := (lanePositions (cursorCoordinateLabels b l)).surjective u
      let node : Word w := (leaves (lanePositions (cursorCoordinateLabels b l) v)).1
      have row := (ready v z pending s h).1
      change ((dispatcher handlers m offset).read node s bits).map Prod.snd = _
      have hn : NodeDispatch.role (m (offset+node).val) = .leaf := roleAt _
      rw [dispatcher_suffix,hn,leaf]
      let load := LeafVisit.loaded (endAddr := n) D budget regions fit fields m
      have suffix := cursorHook_suffix hD hd D budget.tags budget.capFits f (n^39) bound (LeafVisit.storage regions fit)
        fields (regions).arguments (fun node s => (load node s).trace) (fun node s => (load node s).prepared) node s cap v z row bits
      have same : physicalInput (b+l) e w fields (regions).arguments (fun n s => (load n s).trace)
          (fun n s => (load n s).prepared) = load := rfl
      unfold cursorHook at suffix
      rw [same] at suffix
      simp only [LeafRole.parser,LeafRole.withReload,Option.map_map,Function.comp_def]
      exact suffix
    · intro u z pending s bits j tail h hit
      change (dispatcher handlers m offset).read _ _ _ = _ at hit
      simp only [dispatcher,roleAt,leaf,Option.map_eq_some_iff] at hit
      obtain ⟨⟨body,rest⟩,hb,eqn⟩ := hit
      cases eqn
      exact pops u z pending s bits rest body h hb
  · apply leaf_emits valid (privateHistogram order (regions).histBase) guard sites input leaves
    intro u z x pending s h
    obtain ⟨v,rfl⟩ := (lanePositions (cursorCoordinateLabels b l)).surjective u
    let u := lanePositions (cursorCoordinateLabels b l) v
    let node : Word w := (leaves u).1
    have ⟨row,hdomain⟩ := ready v z pending s h
    let code := ((sites).read u z).encode x
    let src := (regions).histBase
    have low : n ≤ src := by
      change n ≤ (regions).arguments.start + (regions).nodes*(regions).arguments.stride
      have hs : (regions).arguments.start = n := size
      omega
    have top : src+g ≤ (regions).stackBase := le_trans (Nat.add_le_add_left hcount _) ((regions).hist_before.trans (Nat.le_add_right ..))
    have topFit : (regions).stackBase < 2^w := (Nat.le_add_right _ _).trans_lt fit
    let addr (label : Label) : Word w := ((src+(order.symm label).val : ℕ) : Word w)
    have val (label : Label) : (addr label).val = src+(order.symm label).val :=
      Nat.mod_eq_of_lt (((Nat.add_lt_add_left (order.symm label).isLt _).trans_le top).trans topFit)
    let cell (label : Label) : {a : Word w // n ≤ a.val} := ⟨addr label,(val label).symm ▸ low.trans (Nat.le_add_right _ _)⟩
    have away (label : Label) : (cell label).val.val < (regions).stackBase := (val label).symm ▸
      (Nat.add_lt_add_left (order.symm label).isLt _).trans_le top
    obtain ⟨j,hread,enabled,real⟩ := LeafRole.selected_job D hD hd budget f (n^39) bound data regions cap fit m
      node s v z row cell away (room v _) code [] ⟨x,rfl⟩
    rw [List.append_nil] at hread
    let actual := dispatchJob m offset node s j
    have hit : hook.read node s code = some (actual,[]) := by
      have hn : NodeDispatch.role (m (offset+node).val) = .leaf := roleAt u
      change (dispatcher handlers m offset).read node s code = _
      simp only [dispatcher,hn,leaf,hread,Option.map_some,actual]
    have good := exactDispatch.success node s ⟨resident _ h.frame,hdomain,roleAt u⟩ code actual [] hit
    obtain ⟨reads,mem⟩ := LeafRole.site_footprint D budget regions fit m data node s (n^39) code [] j allow shadow hread
    obtain ⟨probe,len⟩ := LeafRole.site_work M D budget m header offset arity fit hn boot node s code [] j hread
    obtain ⟨dr,dm⟩ := dispatch_footprint allow m offset node (tag u) (tagRead u)
    have dc := dispatchEvents_cost m offset node
    refine ⟨actual,⟨good.1,?_,?_⟩,⟨rfl,enabled⟩,⟨good.2.2.2,?_,TerminalFootprint.reads_append dr reads,?_,?_⟩,
      pops u z pending s code [] j h hread⟩
    · exact (List.append_nil _ ▸ good.2.2.1).symm
    · intro old en label
      have hist (old : Scratch w n) : privateHistogram order src old label = (old (cell label)).val := by
        change (rawScratch old (addr label)).val = _
        simp only [rawScratch,dite_eq_left (cell label).property,cell]
      change privateHistogram order src (j.update old) label = privateHistogram order src old label + 0
      rw [hist,hist]
      exact real.counts old en.2 label
    · change after m (dispatchEvents m offset node ++ j.trace) = m
      simp only [after,List.foldl_append] at dm mem ⊢
      rw [dm,mem]
    · change countProbes (dispatchEvents m offset node ++ j.trace) ≤ 2
      rw [countProbes_append,dc.1]; omega
    · change (dispatchEvents m offset node ++ j.trace).length+17 ≤ n^40
      rw [List.length_append]; omega

open Compression

/-- Apply the physical leaf checks at every selected branch of an ordered
execution. In the block program the canonical ordering is
`execute_readerOrders`, giving the initial packet of `selected_inputPacked`. -/
theorem selected (link : Contains V M) (fit : (regions).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (hn : 2048 ≤ n) (hwidth : b+l ≤ w)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l) (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafStartup.steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w), LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser data D budget regions fit m (n^39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow (fields .shadow+site).val)
    (tag : ∀ u, m (offset+((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset+((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (stable : Scratch w n → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (regions).nodes ∧ q.node < 2^w)
    (cached : ∀ s, stable s → LeafSourceLoad.Cached (regions).cacheBase (rawScratch s) (LeafVisit.cacheWords D (b+l) e))
    (record : ∀ s, stable s → LeafGeometryLoad.Stored n (frameBase regions) (rawScratch s) data)
    (resident : ∀ s, stable s → ResidentGeometry s (frameBase regions : Word w) offset ((regions).histBase : Word w))
    (preserve : ∀ s out, stable s →
      (∀ i : {a : Word w // n ≤ a.val}, i.val.val < (regions).stackBase → out i = s i) → stable out)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (regions).histWords) :
    ∀ {lastDegree lastLanes : ℕ} (E : StateExecution K lastDegree lastLanes X) (W : E.MapWitnesses f)
      (readers : ExecutionReaders E W) (rec : E.Records) (z : E.Choices),
      ExecutionOrders E W readers → ∀ ptr : RowPointers (E.termChain rec z),
        let input := (fromRows (E.termChain rec z) (branchParsers E W readers rec z) ptr
          (fun u => (leaves u).1) (packed (E.finalState z))).1
        let valid := Frontier (regions).arguments format stable desc
        let hook := dispatcher handlers m offset
        let guard := JobGuard V M m allow (fun j : VisitPath w n => countProbes j.trace ≤ 2 ∧ j.trace.length+17 ≤ n^40)
        Subtrees hook valid sites (fun v => leafTree (leaves v)) input ∧
          Emits valid (privateHistogram order (regions).histBase) guard sites input (leafJobs sites leaves) := by
  intro lastDegree lastLanes E W readers rec z orders ptr input valid hook guard
  have same : input = fun u q => Packet.mk (leaves u).1 (packed X u q) := by
    funext u q
    exact execution_inputPacked E W readers rec z orders ptr (fun i => (leaves i).1) u q
  rw [same]
  exact checks V M D hD hd budget f bound m header offset arity cap link fit hn hwidth stride rb rl span
    shadowFit headers size time room boot handlers leaf allow shadow tag tagRead format stable desc typed
    cached record resident preserve order hcount

/-- The same physical leaf consumes its root from the budgeted frontier.
Its private histogram remains equal to the one on entry, even on arbitrary
successfully decoded leaf tapes. -/
theorem checksBudgeted (link : Contains V M) (fit : (regions).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (hn : 2048 ≤ n) (hwidth : b+l ≤ w)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l) (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafStartup.steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w), LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser data D budget regions fit m (n^39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow (fields .shadow+site).val)
    (tag : ∀ u, m (offset+((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset+((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (stable : Scratch w n → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (regions).nodes ∧ q.node < 2^w)
    (cached : ∀ s, stable s → LeafSourceLoad.Cached (regions).cacheBase (rawScratch s) (LeafVisit.cacheWords D (b+l) e))
    (record : ∀ s, stable s → LeafGeometryLoad.Stored n (frameBase regions) (rawScratch s) data)
    (resident : ∀ s, stable s → ResidentGeometry s (frameBase regions : Word w) offset ((regions).histBase : Word w))
    (preserve : ∀ s out, stable s →
      (∀ i : {a : Word w // n ≤ a.val}, i.val.val < (regions).stackBase → out i = s i) → stable out)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (regions).histWords)
    (nodeCap limit : ℕ) (shape : ∀ u, desc (leaves u).1 = []) :
    let input := fun v z => Packet.mk (leaves v).1 (packed X v z)
    let valid := Budgeted (regions).arguments format stable desc (privateHistogram order (regions).histBase) nodeCap limit
    let hook := dispatcher handlers m offset
    let guard := JobGuard V M m allow (fun j : VisitPath w n => countProbes j.trace ≤ 2 ∧ j.trace.length+17 ≤ n^40)
    Subtrees hook valid sites (fun u => leafTree (leaves u)) input ∧
      Emits valid (privateHistogram order (regions).histBase) guard sites input (leafJobs sites leaves) := by
  intro input valid hook guard
  have basic := checks V M D hD hd budget f bound m header offset arity cap link fit hn hwidth stride rb rl span
    shadowFit headers size time room boot handlers leaf allow shadow tag tagRead format stable desc typed
    cached record resident preserve order hcount
  apply budgetLeaf sites leaves input hook (regions).arguments format stable desc
    (privateHistogram order (regions).histBase) guard nodeCap limit (fun u _ => shape u) _ (fun _ _ _ _ => rfl) basic
  intro u s bits job tail hit l
  let node : Word w := (leaves u).1
  have role : NodeDispatch.role (m (offset+node).val) = .leaf := by rw [tag u]; rfl
  change (dispatcher handlers m offset).read node s bits = some (job,tail) at hit
  simp only [dispatcher,role,leaf,Option.map_eq_some_iff] at hit
  obtain ⟨⟨body,rest⟩,read,eqn⟩ := hit
  cases eqn
  let addr : Word w := (((regions).histBase+(order.symm l).val : ℕ) : Word w)
  change (rawScratch (body.update s) addr).val = (rawScratch s addr).val
  by_cases hi : n ≤ addr.val
  · have hv : addr.val ≤ (regions).histBase+(order.symm l).val := Nat.mod_le _ _
    have htop := (regions).hist_before
    have hbelow : addr.val < (regions).stackBase := by
      unfold LeafArena.Regions.stackBase
      have := (order.symm l).isLt
      omega
    have kept := LeafRole.below_stack D budget (n^39) data regions fit m node s bits rest body read room ⟨addr,hi⟩ hbelow
    simp only [rawScratch,dite_eq_left hi]
    exact congrArg Fin.val kept
  · simp only [rawScratch,dite_eq_right hi]

/-- The selected mathematical branch starts at the very same budgeted
cursor packets used in the native vertex execution. -/
theorem selectedBudgeted (link : Contains V M) (fit : (regions).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (hn : 2048 ≤ n) (hwidth : b+l ≤ w)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l) (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafStartup.steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w), LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser data D budget regions fit m (n^39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow (fields .shadow+site).val)
    (tag : ∀ u, m (offset+((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset+((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (stable : Scratch w n → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (regions).nodes ∧ q.node < 2^w)
    (cached : ∀ s, stable s → LeafSourceLoad.Cached (regions).cacheBase (rawScratch s) (LeafVisit.cacheWords D (b+l) e))
    (record : ∀ s, stable s → LeafGeometryLoad.Stored n (frameBase regions) (rawScratch s) data)
    (resident : ∀ s, stable s → ResidentGeometry s (frameBase regions : Word w) offset ((regions).histBase : Word w))
    (preserve : ∀ s out, stable s →
      (∀ i : {a : Word w // n ≤ a.val}, i.val.val < (regions).stackBase → out i = s i) → stable out)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (regions).histWords)
    (nodeCap limit : ℕ) (shape : ∀ u, desc (leaves u).1 = []) :
    ∀ {lastDegree lastLanes : ℕ} (E : StateExecution K lastDegree lastLanes X) (W : E.MapWitnesses f)
      (readers : ExecutionReaders E W) (rec : E.Records) (z : E.Choices),
      ExecutionOrders E W readers → ∀ ptr : RowPointers (E.termChain rec z),
        let input := (fromRows (E.termChain rec z) (branchParsers E W readers rec z) ptr
          (fun u => (leaves u).1) (packed (E.finalState z))).1
        let valid := Budgeted (regions).arguments format stable desc (privateHistogram order (regions).histBase) nodeCap limit
        let hook := dispatcher handlers m offset
        let guard := JobGuard V M m allow (fun j : VisitPath w n => countProbes j.trace ≤ 2 ∧ j.trace.length+17 ≤ n^40)
        Subtrees hook valid sites (fun v => leafTree (leaves v)) input ∧
          Emits valid (privateHistogram order (regions).histBase) guard sites input (leafJobs sites leaves) := by
  intro lastDegree lastLanes E W readers rec z orders ptr input valid hook guard
  have same : input = fun u q => Packet.mk (leaves u).1 (packed X u q) := by
    funext u q
    exact execution_inputPacked E W readers rec z orders ptr (fun i => (leaves i).1) u q
  rw [same]
  exact checksBudgeted V M D hD hd budget f bound m header offset arity cap link fit hn hwidth stride rb rl span
    shadowFit headers size time room boot handlers leaf allow shadow tag tagRead format stable desc typed
    cached record resident preserve order hcount nodeCap limit shape

/-- The common vertex frame supplies the resident cache and geometry for the
native leaf reader and persists after every returned leaf. -/
theorem selectedFramed (link : Contains V M) (fit : (regions).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (hn : 2048 ≤ n) (hwidth : b+l ≤ w)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l) (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafStartup.steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w), LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser data D budget regions fit m (n^39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow (fields .shadow+site).val)
    (tag : ∀ u, m (offset+((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset+((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (regions).nodes ∧ q.node < 2^w)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (regions).histWords)
    (nodeCap limit : ℕ) (shape : ∀ u, desc (leaves u).1 = []) :
    ∀ {lastDegree lastLanes : ℕ} (E : StateExecution K lastDegree lastLanes X) (W : E.MapWitnesses f)
      (readers : ExecutionReaders E W) (rec : E.Records) (z : E.Choices),
      ExecutionOrders E W readers → ∀ ptr : RowPointers (E.termChain rec z),
        let input := (fromRows (E.termChain rec z) (branchParsers E W readers rec z) ptr
          (fun u => (leaves u).1) (packed (E.finalState z))).1
        let valid := Budgeted (regions).arguments format
          (VertexFrameData regions data offset (LeafVisit.cacheWords D (b+l) e)) desc
          (privateHistogram order (regions).histBase) nodeCap limit
        let hook := dispatcher handlers m offset
        let guard := JobGuard V M m allow (fun j : VisitPath w n => countProbes j.trace ≤ 2 ∧ j.trace.length+17 ≤ n^40)
        Subtrees hook valid sites (fun v => leafTree (leaves v)) input ∧
          Emits valid (privateHistogram order (regions).histBase) guard sites input (leafJobs sites leaves) := by
  have low : n ≤ (regions).arguments.start := size.ge
  have endBefore : n < (regions).stackBase := by
    unfold LeafArena.Regions.stackBase LeafArena.Regions.cacheBase LeafArena.Regions.histBase Arena.base
    omega
  intro lastDegree lastLanes E W readers rec z orders ptr
  exact selectedBudgeted V M D hD hd budget f bound m header offset arity cap link fit hn hwidth stride rb rl span
    shadowFit headers size time room boot handlers leaf allow shadow tag tagRead format
    (VertexFrameData regions data offset (LeafVisit.cacheWords D (b+l) e)) desc typed
    (fun _ h => h.cached) (fun _ h => h.record) (fun _ h => h.resident)
    (fun _ _ h => h.of_below_stack endBefore) order hcount nodeCap limit shape E W readers rec z orders ptr

end PairSimulation.SelectedCursorLeaf

end VPVNP
end Computability
end OAI
