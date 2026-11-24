import OAI.Computability.VPVNP.PairVertexActiveOccurrence
import OAI.Computability.VPVNP.PairVertexOrdinalPhase

/-!
# Accepted vertex paths of a selected compressor execution

Use the native role proofs and the initialized DFS frame at each reached
ordinal to classify the complete physical phase. The site data refer to the
selected term chain and the same fixed half-wire arguments throughout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NetworkKernel NodeArguments TreeDecode TraversalRows
open CompressorRecords SourceTransport TerminalLink
open scoped Fin.CommRing

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → R) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (base grammar : ℕ) (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network)

local notation "exec₀" => B.execute κ hκ T hT X
local notation "data₀" => B.records κ hκ T hT X
local notation "chain₀" => StateExecution.termChain (exec₀) (data₀) z
local notation "readers₀" => selectedParsers B κ hκ T hT X z
local notation "trees₀" => selectedTrees B κ hκ T hT X z rowBase
local notation "Y" => StateExecution.finalState (exec₀) z
local notation "ord₀" => siteOrder (Y)
local notation "final₀" => finalParsers (chain₀) (readers₀) P
local notation "head₀" => TerminalLink.header (Machine.publicData M)
local notation "allow₀" => workerCell (head₀)

variable (half : ∀ u, ((B.execute κ hκ T hT X).finalState z).network.Half u)

local notation "selected₀" => siteOrdinals (final₀) (Order.entries (ord₀)) order half

/-- Operand, row and stack facts at an active physical ordinal. These describe
the individual installed roles and the deterministic root prefix. -/
structure OrdinalRows (cap : ℕ) (m : Memory w) (i : Fin (ord₀).length) where
  /-- End of the DFS stack interval separating stack addresses from private scratch for this
  final-site visit. -/
  endAddr : ℕ
  /-- Private histogram base whose counters are initialized to zero at the beginning of this
  vertex traversal. -/
  src : ℕ
  /-- Machine-word address of the resident private geometry record for this vertex. -/
  G : Word w
  /-- Role-table displacement used to dispatch the popped DFS nodes during the selected visit. -/
  offset : Word w
  /-- Predicate relating the pending node packets to the contents of the private scratch image. -/
  valid : List Packet → Scratch w endAddr → Prop
  /-- Entry predicate on a popped node and scratch image for the local role parser. -/
  domain : Word w → Scratch w endAddr → Prop
  /-- The leaf, shrink, and refresh hook parsers available at this ordinal's DFS nodes. -/
  handlers : NodeDispatch.Role → HookParser w endAddr
  /-- Cost predicate required of the local visit path used in the ordinal's resource bound. -/
  cost : VisitPath w endAddr → Prop
  selected : SelectedChecks B κ hκ T hT X z rowBase A M m G offset src order P valid domain handlers cost
  /-- Native vertex machine configuration reached by the ordinal's initial prefix. -/
  cfg : Config w p r
  /-- Events of the native prefix leading to this ordinal's vertex computation. -/
  pre : List (Event w)
  pref : TerminalSiteStart.Continues M m (M.program.start (i.val : Word w)) cfg pre
  noChoice : choiceBits pre = []
  noWrite : after m pre = m
  prefixReads : Reads (allow₀) pre
  persistent : cfg.persistent = (M.program.start (i.val : Word w)).persistent
  atRoot : cfg.pc = A.dfsPC 0
  /-- DFS stack top at the start of the ordinal's local traversal. -/
  top : ℕ
  stack : Represents cfg.privateMem top [(((trees₀) ((ord₀).entries i)).address : Word w)]
  endTop : top + 1 = endAddr
  sp : cfg.reg (A.dfs 5) = (top : Word w)
  endReg : cfg.reg (A.dfs 6) = (endAddr : Word w)
  one : cfg.reg (A.dfs 3) = 1
  zero : ∀ l, privateHistogram order src (scratch endAddr cfg.privateMem) l = 0
  prepared : valid [⟨((trees₀) ((ord₀).entries i)).address,
    packed (Y) ((ord₀).entries i) (half ((ord₀).entries i))⟩] (scratch endAddr cfg.privateMem)
  rows : AllRows w m B.recordLimit rowBase rowBase (selectedLayers B κ hκ T hT X z)
  space : rowBase + words B.recordLimit (selectedLayers B κ hκ T hT X z) ≤ (head₀).val
  hfit : (head₀).val + 31 < 2^w
  capacity : B.growthConstant^T ≤ endAddr
  above : endAddr ≤ src
  hsrc : src + g < 2^w
  hdst : base + grammar + g < 2^w
  cells : ∀ j : Fin g, (allow₀) (base + grammar + j.val)
  hbase : M.publicData 4 = (base : Word w)
  hgrammar : M.publicData 5 = (grammar : Word w)
  hg : M.publicData 9 = (g : Word w)
  /-- Upper bound on the instruction ticks assigned to this vertex visit. -/
  maxTicks : ℕ
  small : ∀ j, cost j → j.trace.length ≤ maxTicks
  room : pre.length + (15 + maxTicks) * (chain₀).occurrences (fun _ => 1) ((ord₀).entries i) + 7*g+46 ≤ cap

variable {B κ hκ T hT X z rowBase A M base grammar order P half}
variable {cap : ℕ} {m : Memory w} {i : Fin (siteOrder ((B.execute κ hκ T hT X).finalState z)).length}

local notation "rows₀" => OrdinalRows B κ hκ T hT X z rowBase A M base grammar order P half cap m i

/-- The complete native call and its probes, indexed by the selected
preorder visits. This retains the individual role costs for physical charging. -/
theorem OrdinalRows.report (q : rows₀) (linked : Contains A M) (x : (selected₀).Choice i) :
    ∃ rep, execute M.program cap (M.program.start (i.val : Word w)) m ((selected₀).encode i x) = some rep ∧
      rep.result = some ((i.val + 1 : ℕ) : Word w) ∧ choiceBits rep.events = (selected₀).encode i x ∧
      after m rep.events = Counters.addHistogram base grammar ((selected₀).powers i x) m ∧
      Reads (allow₀) rep.events ∧ rep.events.length + 31 ≤ cap ∧
      ∃ native : List (VisitPath w q.endAddr), native.length = ((trees₀) ((ord₀).entries i)).preorder.length ∧
        (∀ j ∈ native, q.cost j) ∧ countProbes rep.events + 1 =
          countProbes q.pre + 3*native.length + (native.map (fun j => countProbes j.trace)).sum + 2*g := by
  obtain ⟨rep,run,next,bits,flush,read,room,native⟩ :=
    active_occurrence B κ hκ T hT X z rowBase A M m q.G q.offset base grammar q.src order P q.valid q.domain
      q.handlers q.cost linked q.selected ((ord₀).entries i) (half ((ord₀).entries i))
      (M.program.start (i.val : Word w)) q.cfg q.pre q.pref q.noChoice q.noWrite q.prefixReads q.persistent
      q.atRoot q.top q.stack q.endTop q.sp q.endReg q.one q.zero q.prepared q.rows q.space q.hfit q.capacity
      q.above q.hsrc q.hdst q.cells q.hbase q.hgrammar q.hg q.maxTicks cap q.small q.room x
  refine ⟨rep,run,?_,bits,flush,read,room,native⟩
  change rep.result = some ((i.val : Word w) + 1) at next
  simpa only [Nat.cast_add, Nat.cast_one] using next

/-- The selected call has room for its physical terminal dispatch and reads
only worker addresses. -/
theorem OrdinalRows.emit (q : rows₀) (linked : Contains A M) (x : (selected₀).Choice i) :
    ∃ rep, execute M.program cap (M.program.start (i.val : Word w)) m ((selected₀).encode i x) = some rep ∧
      rep.result = some ((i.val + 1 : ℕ) : Word w) ∧
      after m rep.events = Counters.addHistogram base grammar ((selected₀).powers i x) m ∧
      Reads (allow₀) rep.events ∧ rep.events.length + 1 ≤ cap-30 := by
  obtain ⟨rep,run,next,_,flush,read,room,_⟩ := q.report linked x
  exact ⟨rep,run,next,flush,read,by omega⟩

/-- Decode arbitrary actual tapes on the selected row image. -/
theorem OrdinalRows.recover (q : rows₀) (linked : Contains A M) (bs : List Bool) (rep : Report w)
    (run : execute M.program cap (M.program.start (i.val : Word w)) m bs = some rep) :
    ∃ x : (selected₀).Choice i, bs = (selected₀).encode i x := by
  exact (active_recover B κ hκ T hT X z rowBase A M m q.G q.offset q.src order P q.valid q.domain q.handlers
    q.cost linked q.selected ((ord₀).entries i) (half ((ord₀).entries i))
    (M.program.start (i.val : Word w)) q.cfg q.pre q.pref q.atRoot q.top q.stack q.endTop q.sp q.endReg q.one
    q.prepared q.rows q.space q.hfit q.capacity cap bs rep run).exists

variable (B κ hκ T hT X z rowBase A M base grammar order P half)

/-- Discharge both the ascending interpreter and its active-report checks
from the local selected rows and their deterministic root preparations. -/
theorem selectedCalls (ref : Memory w) (linked : Contains A M)
    (localRows : ∀ i m, VertexFrame.Linked (head₀) base grammar g ref i.val m →
      Nonempty (OrdinalRows B κ hκ T hT X z rowBase A M base grammar order P half cap m i)) :
    ActiveCalls (selected₀) M.program cap base grammar (VertexFrame.Linked (head₀) base grammar g ref) ∧
      ∀ i m, VertexFrame.Linked (head₀) base grammar g ref i.val m → ∀ (x : (selected₀).Choice i) r,
        execute M.program cap (M.program.start (i.val : Word w)) m ((selected₀).encode i x) = some r →
        Reads (allow₀) r.events ∧ r.events.length + 1 ≤ cap-30 := by
  constructor
  · constructor
    · intro i m frame x
      obtain ⟨q⟩ := localRows i m frame
      obtain ⟨r,call,next,flush,_,_⟩ := q.emit linked x
      exact ⟨r,call,next,flush⟩
    · intro i m frame bits r run
      obtain ⟨q⟩ := localRows i m frame
      exact q.recover linked bits r run
    · intro i m frame x
      exact frame.preserve _
  · intro i m frame x r run
    obtain ⟨q⟩ := localRows i m frame
    obtain ⟨out,call,_,_,support,room⟩ := q.emit linked x
    obtain rfl := Option.some.inj (run.symm.trans call)
    exact ⟨support,room⟩

local notation "image₀" => segments geometry rootFields leaf shrink refresh

/-- Construct the native worker frame of this selected compressor branch.
All successful source and physical paths are classified by the local rows. -/
theorem selectedWorkerFrame (F : DescriptorSpace.Shape) (limit : ℕ) (ops : Fin 11 → Word w)
    (ref src phy : Memory w)
    (localRows : ∀ i m, VertexFrame.Linked (TerminalLink.header ops) base grammar g ref i.val m →
      Nonempty (OrdinalRows B κ hκ T hT X z rowBase (placement image₀) ((template image₀).instantiate w ops)
        base grammar order P half cap m i))
    (room : (TerminalLink.header ops).val + 32 ≤ 2^w) (clock : 45 ≤ cap)
    (below : base+grammar+g ≤ (TerminalLink.header ops).val)
    (sites : ref (TerminalLink.header ops + 7).val = ((ord₀).length : Word w))
    (hs : VertexFrame.Linked (TerminalLink.header ops) base grammar g ref 0 src)
    (hp : VertexFrame.Linked (TerminalLink.header ops) base grammar g ref 0 phy)
    (agree : Agree (workerCell (TerminalLink.header ops)) src phy) :
    ActiveCalls (selected₀) (((template image₀).instantiate w ops).program) cap base grammar
      (VertexFrame.Linked (TerminalLink.header ops) base grammar g ref) ∧
    WorkerFrame (TerminalProgram.workers F limit image₀) ops cap (.resume Stage.vertices 0) src phy := by
  obtain ⟨active,checks⟩ :=
    selectedCalls B κ hκ T hT X z rowBase (placement image₀) ((template image₀).instantiate w ops) base grammar
      order P half ref (template_contains image₀ ops) localRows
  exact ⟨active, ordinalWorkerFrame F limit ref src phy active
    (template_closes (by omega) (linked_finalSites ref room below sites)) room clock checks hs hp agree⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
