import OAI.Computability.VPVNP.PairVertexBurstReadback
import OAI.Computability.VPVNP.PairVertexSelectedReport
import OAI.Computability.VPVNP.PairVertexSelectedControl
import OAI.Computability.VPVNP.PairSelectedRowChecks

/-! # Exact transcripts of a complete active terminal vertex call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NetworkKernel NodeArguments TreeDecode
  TraversalRows
open CompressorRecords.SourceTransport TerminalFootprint
open scoped Fin.CommRing

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → K) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g endAddr : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (m : Memory w) (G offset : Word w) (base grammar src : ℕ) (order : Fin g ≃ B.Entry)
    (P : SiteParsers κ X.network) (valid : List Packet → Scratch w endAddr → Prop)
    (domain : Word w → Scratch w endAddr → Prop) (handlers : NodeDispatch.Role → HookParser w
      endAddr)
    (cost : VisitPath w endAddr → Prop)

local notation "exec₀" => B.execute κ hκ T hT X
local notation "data₀" => B.records κ hκ T hT X
local notation "chain₀" => StateExecution.termChain (exec₀) (data₀) z
local notation "readers₀" => selectedParsers B κ hκ T hT X z
local notation "passes₀" =>
  repeatReaders (blockReaders B κ hκ) _ T lanes (Eq.symm (Nat.add_sub_of_le hT)) X
local notation "ptr₀" => selectedPointers B κ hκ T hT X z rowBase
local notation "leaves₀" => sitePointers B.recordLimit rowBase (siteOrder X)
local notation "trees₀" => selectedTrees B κ hκ T hT X z rowBase
local notation "H₀" => TerminalLink.header M.publicData
local notation "allow₀" => TerminalLink.workerCell (H₀)
local notation "hook₀" => dispatcher handlers m offset
local notation "hist₀" => privateHistogram order src
local notation "guard₀" => JobGuard A M m (allow₀) cost
local notation "final₀" => finalParsers (chain₀) (readers₀) P
local notation "leafPackets₀" => (fun v y => Packet.mk (Prod.fst ((leaves₀) v)) (packed X v y))
local notation "frames₀" =>
  fromRows (chain₀) (readers₀) (ptr₀) (fun v => (Prod.fst ((leaves₀) v))) (packed
  (StateExecution.finalState (exec₀) z))

/-- Row obligations for the selected compressor execution, expressed in its
actual states, address order, and packed half-wire buffers. -/
structure SelectedChecks : Prop where
  resident : ∀ node s, domain node s → ResidentGeometry s G offset (src : Word w)
  remaining : ∀ s, valid [] s → ResidentGeometry s G offset (src : Word w)
  head : HeadDomain valid domain
  nativeRole : ∀ role, (handlers role).ExactOn
    (fun node s => domain node s ∧ NodeDispatch.role (m (offset + node).val) = role)
    M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m
  leafDecode : Subtrees (hook₀) valid P (fun u => leafTree ((leaves₀) u)) (leafPackets₀)
  leafEmit : Emits valid (hist₀) (guard₀) P (leafPackets₀) (leafJobs P (leaves₀))
  passes : ExecutionChecks (hook₀) valid (hist₀) (guard₀) (exec₀) _ (passes₀) (data₀) z (ptr₀)
    (fun u => ((leaves₀) u).1)

private theorem sum_le_size {J : Type*} (f : J → ℕ) (xs : List J) (cap : ℕ) (h : ∀ x ∈ xs, f x ≤
  cap) :
    (xs.map f).sum ≤ xs.length * cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (h _ List.mem_cons_self) (ih (fun i hi => h i (List.mem_cons_of_mem _
      hi)))).trans_eq
      (Nat.add_comm _ _)

variable (linked : Contains A M)
    (check : SelectedChecks B κ hκ T hT X z rowBase A M m G offset src order P valid domain
      handlers cost)
    (u : (((B.execute κ hκ T hT X)).finalState z).network.Site) (y : (((B.execute κ hκ T hT
      X)).finalState z).network.Half u)
    (start cfg : Config w p r) (pre : List (Event w))
    (pref : TerminalSiteStart.Continues M m start cfg pre) (noChoice : choiceBits pre = [])
    (noWrite : after m pre = m) (prefixReads : Reads ((TerminalLink.workerCell
      ((TerminalLink.header M.publicData)))) pre) (persistent : cfg.persistent = start.persistent)
    (atRoot : cfg.pc = A.dfsPC 0) (top : ℕ) (stack : Represents cfg.privateMem top
      [((((selectedTrees B κ hκ T hT X z rowBase)) u).address : Word w)])
    (endTop : top + 1 = endAddr) (sp : cfg.reg (A.dfs 5) = (top : Word w)) (endReg : cfg.reg
      (A.dfs 6)
      = (endAddr : Word w))
    (one : cfg.reg (A.dfs 3) = 1) (zero : ∀ l, (privateHistogram order src) (scratch endAddr
      cfg.privateMem) l = 0)
    (prepared : valid [⟨(((selectedTrees B κ hκ T hT X z rowBase)) u).address, packed (((B.execute
      κ hκ T hT X)).finalState z) u y⟩] (scratch endAddr cfg.privateMem))
    (rows : AllRows w m B.recordLimit rowBase rowBase (selectedLayers B κ hκ T hT X z))
    (space : rowBase + words B.recordLimit (selectedLayers B κ hκ T hT X z) ≤ ((TerminalLink.header
      M.publicData)).val)
    (hfit : (TerminalLink.header M.publicData).val + 31 < 2 ^ w)
    (capacity : B.growthConstant ^ T ≤ endAddr)
    (above : endAddr ≤ src) (hsrc : src + g < 2 ^ w) (hdst : base + grammar + g < 2 ^ w)
    (cells : ∀ i : Fin g, TerminalLink.workerCell (TerminalLink.header M.publicData)
      (base + grammar + i.val))
    (hbase : M.publicData 4 = (base : Word w)) (hgrammar : M.publicData 5 = (grammar : Word w))
    (hg : M.publicData 9 = (g : Word w))

include linked check pref atRoot stack endTop sp endReg one prepared rows space hfit capacity

/-- Starting at the bootstrap, any successful raw stream is the unique
encoding of an occurrence. This covers arbitrary public cutoffs and all
short, malformed, or surplus private choice tapes. -/
theorem active_recover (fuel : ℕ) (bits : List Bool) (observed : Report w)
    (returned : execute M.program fuel start m bits = some observed) :
    ∃! x, bits = ((final₀).read u y).encode x := by
  obtain ⟨control,visits,_,_,_,_⟩ := selected_control B κ hκ T hT X z rowBase m (H₀) endAddr
    rows space hfit capacity u
  have leafEq : (frames₀).1 = leafPackets₀ := by
    funext v z'
    exact selected_inputPacked B κ hκ T hT X z (ptr₀) _ v z'
  obtain ⟨steps,_⟩ := execution_checks (hook₀) valid (hist₀) (guard₀) (exec₀) _ (passes₀) (data₀) z
    (ptr₀) _ (execute_readerOrders B κ hκ T hT X) check.passes
  have accept := returns_iff_occurrence A M linked G offset (src : Word w) m domain valid
    check.resident check.head handlers check.nativeRole (chain₀) (readers₀) (ptr₀) (frames₀).2
    P (leaves₀) (frames₀).1 (fun v z' => fromRows_inputAddress _ _ _ _ _ v z') (fromRows_pointers
      ..) (leafEq ▸ check.leafDecode) steps
    u y cfg atRoot top (((trees₀) u).address : Word w) stack endTop sp endReg one control visits
    ((selected_rootPacket B κ hκ T hT X z rowBase u y).symm ▸ prepared)
  exact (prefix_occurrences _ pref accept bits).mp ⟨fuel,observed,returned⟩

include noChoice noWrite prefixReads persistent zero above hsrc hdst cells hbase hgrammar hg

/-- The whole source call executes the chosen occurrence and flushes its
actual exponents. The clock bound uses the number of rows of this selected
tree and the time bound of each local body. The read support excludes the
two cells written by the enclosing phase controller. -/
theorem active_occurrence_costs (maxTicks fuel : ℕ) (small : ∀ j, cost j → j.trace.length ≤
  maxTicks)
    (room : pre.length + (15 + maxTicks) * (chain₀).occurrences (fun _ => 1) u + 7 * g + 46 ≤ fuel)
    (x : ((final₀).witnesses u y).Choice) :
    let code := ((final₀).read u y).encode x
    let powers := fun j : Fin g => ((final₀).witnesses u y).exponents x (order j)
    ∃ rep : Report w, execute M.program fuel start m code = some rep ∧
      rep.result = some (start.persistent + 1) ∧ choiceBits rep.events = code ∧
      after m rep.events = Counters.addHistogram base grammar powers m ∧
      Reads (allow₀) rep.events ∧ rep.events.length + 31 ≤ fuel ∧
      ∃ native : List (VisitPath w endAddr),
        native.length = ((trees₀) u).preorder.length ∧ (∀ j ∈ native, cost j) ∧
        countProbes rep.events + 1 = countProbes pre + 3 * native.length +
          (native.map (fun j => countProbes j.trace)).sum + 2 * g ∧
        rep.events.length + 4 = pre.length + 15 * native.length +
          (native.map (fun j => j.trace.length)).sum + 7 * g + 14 := by
  intro code powers
  obtain ⟨control,visits,reads,nodes,time,probes⟩ := selected_control B κ hκ T hT X z rowBase m
    (H₀) endAddr
    rows space hfit capacity u
  have leafEq : (frames₀).1 = leafPackets₀ := by
    funext v z'
    exact selected_inputPacked B κ hκ T hT X z (ptr₀) _ v z'
  obtain ⟨_,layers⟩ := execution_checks (hook₀) valid (hist₀) (guard₀) (exec₀) _ (passes₀) (data₀) z
    (ptr₀) _ (execute_readerOrders B κ hκ T hT X) check.passes
  obtain ⟨native,rep,effects,result,bits,memory,ticks,bodyProbes,support,run⟩ :=
    occurrence_report A M linked m (allow₀) cost valid order base grammar src G offset (chain₀)
      (readers₀)
      (ptr₀) (frames₀).2 P (frames₀).1 (leaves₀) (leafEq ▸ check.leafEmit) layers u y x cfg atRoot
        top
      (((trees₀) u).address : Word w) stack endTop sp endReg one control visits
      ((selected_rootPacket B κ hκ T hT X z rowBase u y).symm ▸ prepared) check.remaining zero
        reads cells
      above hsrc hdst hbase hgrammar hg
  have addr := (vertexJobs_spec (chain₀) (readers₀) (ptr₀) P (leaves₀)).addresses u y x
  have len : native.length = ((trees₀) u).preorder.length :=
    effects.realized.length_eq.symm.trans (by simpa using congrArg List.length addr)
  have sizes : ∀ j ∈ native, cost j := fun j hj => (effects.framed j hj).2.2.2
  have sum := sum_le_size (fun j : VisitPath w endAddr => j.trace.length) native maxTicks (fun j
    hj => small j (sizes j hj))
  have total : pre.length + rep.events.length + 31 ≤ fuel := by
    rw [len] at sum
    calc
      _ ≤ pre.length + (15 + maxTicks) * ((trees₀) u).preorder.length + 7 * g + 46 := by
        rw [Nat.add_mul, Nat.mul_comm maxTicks _]
        omega
      _ ≤ pre.length + (15 + maxTicks) * (chain₀).occurrences (fun _ => 1) u + 7 * g + 46 := by
        gcongr
      _ ≤ fuel := room
  have emit := emit_at_cutoff pref noWrite noChoice rep code bits run fuel (by omega)
  refine ⟨⟨pre ++ rep.events,rep.result⟩,emit.1,result.trans (by rw [persistent]),emit.2.1,
    emit.2.2.1.trans memory,reads_append prefixReads support,by simpa only [List.length_append]
      using total,
    native,len,sizes,?_,?_⟩
  · change countProbes (pre ++ rep.events) + 1 = _
    rw [countProbes_append,bodyProbes,len]
    omega
  · change (pre ++ rep.events).length + 4 = _
    rw [List.length_append,ticks,len]
    omega

/-- The successful source report at the caller's public cutoff. -/
theorem active_occurrence (maxTicks fuel : ℕ) (small : ∀ j, cost j → j.trace.length ≤ maxTicks)
    (room : pre.length + (15 + maxTicks) * (chain₀).occurrences (fun _ => 1) u + 7 * g + 46 ≤ fuel)
    (x : ((final₀).witnesses u y).Choice) :
    let code := ((final₀).read u y).encode x
    let powers := fun j : Fin g => ((final₀).witnesses u y).exponents x (order j)
    ∃ rep : Report w, execute M.program fuel start m code = some rep ∧
      rep.result = some (start.persistent + 1) ∧ choiceBits rep.events = code ∧
      after m rep.events = Counters.addHistogram base grammar powers m ∧
      Reads (allow₀) rep.events ∧ rep.events.length + 31 ≤ fuel ∧
      ∃ native : List (VisitPath w endAddr),
        native.length = ((trees₀) u).preorder.length ∧ (∀ j ∈ native, cost j) ∧
        countProbes rep.events + 1 = countProbes pre + 3 * native.length +
          (native.map (fun j => countProbes j.trace)).sum + 2 * g := by
  obtain ⟨rep,run,result,bits,memory,reads,space,native,len,sizes,probes,_⟩ :=
    active_occurrence_costs B κ hκ T hT X z rowBase A M m G offset base grammar src order P valid
      domain handlers cost linked check u y start cfg pre pref noChoice noWrite prefixReads
        persistent
      atRoot top stack endTop sp endReg one zero prepared rows space hfit capacity above hsrc hdst
        cells
      hbase hgrammar hg maxTicks fuel small room x
  exact ⟨rep,run,result,bits,memory,reads,space,native,len,sizes,probes⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
