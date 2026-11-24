import OAI.Computability.VPVNP.PairVertexSiteSegments
import OAI.Computability.VPVNP.PairSimulationVertexJobs
import OAI.Computability.VPVNP.PairCounterReadFootprint

/-!
# The actual report of a selected final vertex

The DFS follows the chosen jobs, the physical flush reads their accumulated
private histogram, and the last four rows return the next persistent ordinal.
The resulting external memory adds precisely that vertex's monomial powers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory NodeArguments NetworkKernel
open CompressorRecords.SourceTransport
open scoped Fin.CommRing
open private realized_counts realized_bits realized_addresses from OAI.Computability.VPVNP.PairSimulationVertexJobs
open private probes_append from OAI.Computability.VPVNP.PairSimulationDFSHooks

variable {geometry rootFields leaf shrink refresh : Segment} {p r W endAddr g : ℕ}
  (A : Placement (segments geometry rootFields leaf shrink refresh) p r)
  (M : Machine W p r 11)
  {Label : Type} [Fintype Label] {R : Type*} [CommRing R] {f : Label → R} {N : Network}

/-- Read a typed counter from the fixed private histogram interval. -/
def privateHistogram (order : Fin g ≃ Label) (src : ℕ) (s : Scratch W endAddr) (label : Label) : ℕ :=
  (rawScratch s ((src + (order.symm label).val : ℕ) : Word W)).val

/-- On the genuine assembled image every realized site occurrence produces
one exact successful report. Its external effect, choices and costs are
the ones of this occurrence and its actual linked hook calls. -/
theorem vertex_report_supported (linked : Contains A M) (P : SiteParsers f N) (trees : N.Site → VertexTree)
    (jobs : JobsFor P) (spec : JobsSpec P trees jobs) (v : N.Site) (z : N.Half v)
    (x : (P.witnesses v z).Choice) (order : Fin g ≃ Label)
    (base grammar src : ℕ) (G offset : Word W) (m : Memory W)
    {pending : List (Word W)} {control : List (Event W)}
    (visits : Visits m endAddr pending ((trees v).preorder.map (fun n : ℕ => (n : Word W))) control)
    (native : List (VisitPath W endAddr))
    (realized : List.Forall₂ (RealizesJob (privateHistogram order src)) (jobs v z x) native)
    (hook : ∀ j ∈ native, j.Linked M (A.core (.roleBase 0)) (A.dfsPC 3) A.dfs m)
    (readOnly : ∀ j ∈ native, after m j.trace = m)
    (c : Config W p r) (here : c.pc = A.dfsPC 0) (top : ℕ) (stack : Represents c.privateMem top pending)
    (length : top+pending.length = endAddr) (sp : c.reg (A.dfs 5) = (top : Word W))
    (endReg : c.reg (A.dfs 6) = (endAddr : Word W)) (one : c.reg (A.dfs 3) = 1)
    (ready : Ready native (scratch endAddr c.privateMem))
    (resident : ResidentGeometry (native.foldl (fun s j => j.update s) (scratch endAddr c.privateMem))
      G offset (src : Word W))
    (zero : ∀ l, privateHistogram order src (scratch endAddr c.privateMem) l = 0)
    (above : endAddr ≤ src) (hsrc : src+g < 2^W) (hdst : base+grammar+g < 2^W)
    (hbase : M.publicData 4 = (base : Word W)) (hgrammar : M.publicData 5 = (grammar : Word W))
    (hg : M.publicData 9 = (g : Word W)) :
    let powers := fun i : Fin g => (P.witnesses v z).exponents x (order i)
    ∃ rep : Report W, rep.result = some (c.persistent+1) ∧
      choiceBits rep.events = (P.read v z).encode x ∧ after m rep.events = Counters.addHistogram base grammar powers m ∧
      rep.events.length = control.length + (native.map fun j => j.trace.length).sum + 7*g+14 ∧
      countProbes rep.events = countProbes control + (native.map fun j => countProbes j.trace).sum + 2*g ∧
      (∀ allow, Reads allow control → (∀ j ∈ native, Reads allow j.trace) →
        (∀ i : Fin g, allow (base+grammar+i.val)) → Reads allow rep.events) ∧
      ∀ extra, execute M.program (extra+rep.events.length+1) c m ((P.read v z).encode x) = some rep := by
  intro powers
  have names : native.map VisitPath.node = (trees v).preorder.map (fun n : ℕ => (n : Word W)) := by
    rw [← spec.addresses v z x, List.map_map]
    exact realized_addresses realized
  obtain ⟨dfs,copy,_⟩ := core_linked A M linked
  obtain ⟨mid,body,atFlush,state,spEnd,noWrites,support,finalScratch,bodyBits,bodyTime,bodyProbes,bodyRun⟩ :=
    execute_linked_visits_supported dfs copy visits native names hook c here top stack length sp endReg one ready
  have exactBits := bodyBits.trans ((realized_bits realized).trans (spec.bits v z x))
  have hist (i : Fin g) : mid.privateMem ((src+i.val : ℕ) : Word W) = (powers i : Word W) := by
    have atCell := realized_counts realized (scratch endAddr c.privateMem) ready (order i)
    rw [← finalScratch,zero,Nat.zero_add,spec.increments] at atCell
    unfold privateHistogram at atCell
    rw [Equiv.symm_apply_apply] at atCell
    have addr : ((src+i.val : ℕ) : Word W).val = src+i.val :=
      Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt src).trans hsrc)
    have ok : endAddr ≤ ((src+i.val : ℕ) : Word W).val := by rw [addr]; exact above.trans (Nat.le_add_right _ _)
    simp only [rawScratch,dite_eq_left ok,scratch] at atCell
    simpa only [Fin.cast_val_eq_self] using congrArg (fun n : ℕ => (n : Word W)) atCell
  obtain ⟨out,flush,atFinish,_,persistent,flushLog,flushTime,flushProbes,flushBits,flushAfter,flushRun⟩ :=
    flush_run_events linked G offset mid atFlush spEnd base grammar src (finalScratch ▸ resident)
      hbase hgrammar hg powers hist hsrc hdst m
  let close : List (Event W) := [.tick,.tick,.tick]
  let events := body ++ flush ++ close
  let rep : Report W := ⟨events,some (c.persistent+1)⟩
  have runFinish (extra : ℕ) : execute M.program (extra+4) out (Counters.addHistogram base grammar powers m) [] =
      some ⟨close,some (c.persistent+1)⟩ := by
    rw [TerminalSiteStart.finish_run (finish_finishLinked A M linked) _ _ atFinish]
    simp [close,persistent,state]
  refine ⟨rep,rfl,?_,?_,?_,?_,?_,?_⟩
  · change choiceBits events = _
    simp [events,close,PrimedInputRAM.Flow.choiceBits_append,exactBits,flushBits,choiceBits]
  · change after m events = _
    have app (mem : Memory W) (xs ys : List (Event W)) : after mem (xs++ys) = after (after mem xs) ys :=
      List.foldl_append
    change after m ((body ++ flush) ++ close) = _
    rw [app,app,noWrites readOnly,flushAfter]
    rfl
  · change events.length = _
    simp [events,close,bodyTime,flushTime,Nat.add_assoc]
  · change countProbes events = _
    simp [events,close,probes_append,bodyProbes,flushProbes,countProbes]
  · intro allow ctrl calls cells a v mem
    change .read a v ∈ (body ++ flush) ++ close at mem
    rcases List.mem_append.mp mem with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases support _ h with hc | ⟨j, hj, he⟩
        · exact ctrl a v hc
        · exact calls j hj a v he
      · rw [flushLog] at h
        rcases List.mem_append.mp h with head | rest
        · have eq : (.read a v : Event W) = .tick := List.eq_of_mem_replicate head
          cases eq
        · exact Counters.events_reads _ _ _ _ _ hdst allow cells a v rest
    · simp [close] at h
  · intro extra
    have a := bodyRun (extra+4+7*g+11) []
    rw [List.append_nil,exactBits] at a
    have b := flushRun (extra+4) []
    rw [runFinish] at b
    change execute M.program (extra+events.length+1) c m _ = _
    have len : extra+events.length+1 = extra+4+7*g+11+body.length := by
      simp [events,close,flushTime]; omega
    rw [len,a,b]
    simp [rep,events,List.append_assoc]

theorem vertex_report (linked : Contains A M) (P : SiteParsers f N) (trees : N.Site → VertexTree)
    (jobs : JobsFor P) (spec : JobsSpec P trees jobs) (v : N.Site) (z : N.Half v)
    (x : (P.witnesses v z).Choice) (order : Fin g ≃ Label)
    (base grammar src : ℕ) (G offset : Word W) (m : Memory W)
    {pending : List (Word W)} {control : List (Event W)}
    (visits : Visits m endAddr pending ((trees v).preorder.map (fun n : ℕ => (n : Word W))) control)
    (native : List (VisitPath W endAddr))
    (realized : List.Forall₂ (RealizesJob (privateHistogram order src)) (jobs v z x) native)
    (hook : ∀ j ∈ native, j.Linked M (A.core (.roleBase 0)) (A.dfsPC 3) A.dfs m)
    (readOnly : ∀ j ∈ native, after m j.trace = m)
    (c : Config W p r) (here : c.pc = A.dfsPC 0) (top : ℕ) (stack : Represents c.privateMem top pending)
    (length : top+pending.length = endAddr) (sp : c.reg (A.dfs 5) = (top : Word W))
    (endReg : c.reg (A.dfs 6) = (endAddr : Word W)) (one : c.reg (A.dfs 3) = 1)
    (ready : Ready native (scratch endAddr c.privateMem))
    (resident : ResidentGeometry (native.foldl (fun s j => j.update s) (scratch endAddr c.privateMem))
      G offset (src : Word W))
    (zero : ∀ l, privateHistogram order src (scratch endAddr c.privateMem) l = 0)
    (above : endAddr ≤ src) (hsrc : src+g < 2^W) (hdst : base+grammar+g < 2^W)
    (hbase : M.publicData 4 = (base : Word W)) (hgrammar : M.publicData 5 = (grammar : Word W))
    (hg : M.publicData 9 = (g : Word W)) :
    let powers := fun i : Fin g => (P.witnesses v z).exponents x (order i)
    ∃ rep : Report W, rep.result = some (c.persistent+1) ∧
      choiceBits rep.events = (P.read v z).encode x ∧ after m rep.events = Counters.addHistogram base grammar powers m ∧
      rep.events.length = control.length + (native.map fun j => j.trace.length).sum + 7*g+14 ∧
      countProbes rep.events = countProbes control + (native.map fun j => countProbes j.trace).sum + 2*g ∧
      ∀ extra, execute M.program (extra+rep.events.length+1) c m ((P.read v z).encode x) = some rep := by
  obtain ⟨rep, result, bits, effect, time, probes, _, run⟩ :=
    vertex_report_supported A M linked P trees jobs spec v z x order base grammar src G offset m
      visits native realized hook readOnly c here top stack length sp endReg one ready resident
      zero above hsrc hdst hbase hgrammar hg
  exact ⟨rep, result, bits, effect, time, probes, run⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
