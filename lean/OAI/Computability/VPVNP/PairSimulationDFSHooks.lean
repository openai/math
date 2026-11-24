import OAI.Computability.VPVNP.PairSimulationDFS
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Linking final-vertex work to the native traversal

A local vertex routine may consume private choices and update its scratch
arrays, including the histogram above the stack. The dispatcher pops its
descriptor address and gives it control. Its return resumes the stored child
scan. This composition accounts separately for the routine's actual trace
and the traversal's reads, with the same unused stream suffix throughout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DFS

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private copyRegs headerEvents from OAI.Computability.VPVNP.PairSimulationDFS

variable {w p r k : ℕ}

/-- The portion of private memory at word addresses greater than or equal to the exclusive
stack end. Local visit routines use these cells for arguments and accumulated histogram
entries. -/
abbrev Scratch (w endAddr : ℕ) := {a : Word w // endAddr ≤ a.val} → Word w

/-- Restrict a machine's private memory to addresses at or above the stack end, giving the
scratch state passed to a local visit. -/
def scratch (endAddr : ℕ) (priv : Word w → Word w) : Scratch w endAddr := fun a => priv a.val

/-- One specified path through the site routine. Distinct items can have
the same address and update the same exponent, with their separate traces. -/
structure VisitPath (w endAddr : ℕ) where
  /-- Descriptor address this visit expects in the dispatcher's node register after the stack
  pop. -/
  node : Word w
  /-- Chronological RAM events of this local visit. They determine its consumed choice bits,
  instruction count and external probes in the combined traversal. -/
  trace : List (Event w)
  /-- Precondition on the incoming scratch contents for this particular visit path. Successive
  visits test it after applying the preceding paths' updates. -/
  enabled : Scratch w endAddr → Prop
  /-- Scratch contents produced on successful return from the local routine. The next visit
  reads its prepared arguments and accumulated counts from this state. -/
  update : Scratch w endAddr → Scratch w endAddr

/-- The local arguments prepared by one occurrence must enable the next
occurrence. This allows malformed field assignments to reject. -/
def Ready {endAddr : ℕ} : List (VisitPath w endAddr) → Scratch w endAddr → Prop
  | [], _ => True
  | j :: js, s => j.enabled s ∧ Ready js (j.update s)

/-- The exact execution contract of an embedded vertex routine. Pending
stack cells are preserved until the dispatcher prepends its child list. -/
def VisitPath.Linked {endAddr : ℕ} (job : VisitPath w endAddr) (M : Machine w p r k)
    (visit ret : Fin p) (reg : Fin 9 ↪ Fin r) (m : Memory w) : Prop :=
  ∀ (c : Config w p r) (top : ℕ) (pending : List (Word w)),
    job.enabled (scratch endAddr c.privateMem) → c.pc = visit → c.reg (reg 7) = job.node → Represents c.privateMem top pending →
    top + pending.length = endAddr → c.reg (reg 5) = (top : Word w) → c.reg (reg 6) = (endAddr : Word w) → c.reg (reg 3) = 1 →
    ∃ out, out.pc = ret ∧ out.reg (reg 7) = job.node ∧ out.reg (reg 5) = (top : Word w) ∧
      out.reg (reg 6) = (endAddr : Word w) ∧ out.reg (reg 3) = 1 ∧ out.persistent = c.persistent ∧
      Represents out.privateMem top pending ∧ scratch endAddr out.privateMem = job.update (scratch endAddr c.privateMem) ∧
      ∀ fuel bs, execute M.program (fuel + job.trace.length) c m (choiceBits job.trace ++ bs) =
        (execute M.program fuel out m bs).map (fun r => ⟨job.trace ++ r.events,r.result⟩)

private theorem choiceBits_copy (m : Memory w) (src n : ℕ) : choiceBits (EndpointBits.events m src n) = [] := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih => simpa only [EndpointBits.events, List.cons_append, List.nil_append, choiceBits] using ih _

private theorem length_copy (m : Memory w) (src n : ℕ) : (EndpointBits.events m src n).length = 5*n+1 := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih => simp [EndpointBits.events,ih]; omega

private theorem probes_append (a b : List (Event w)) : countProbes (a++b) = countProbes a + countProbes b := by
  induction a with
  | nil => simp [countProbes]
  | cons e a ih => cases e <;> simp [countProbes,ih,Nat.add_comm,Nat.add_left_comm]

/-- For a fixed chosen native path at each visit, control overhead adds no
choice bits and each state update acts on the previous routine's scratch.
The theorem includes the exact length and probe count on the combined path. -/
theorem execute_linked_visits_supported {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p}
    (hl : Linked M pc reg visit (arcPC 0) done) (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0))
    {m : Memory w} {endAddr : ℕ} {pending nodes : List (Word w)} {control : List (Event w)}
    (visits : Visits m endAddr pending nodes control)
    (jobs : List (VisitPath w endAddr)) (hjobs : jobs.map VisitPath.node = nodes)
    (hook : ∀ job ∈ jobs, job.Linked M visit (pc 3) reg m)
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1)
    (ready : Ready jobs (scratch endAddr c.privateMem)) :
    ∃ out es, out.pc = done ∧ out.persistent = c.persistent ∧ out.reg (reg 6) = (endAddr : Word w) ∧
      ((∀ j ∈ jobs, after m j.trace = m) → after m es = m) ∧
      (∀ ev ∈ es, ev ∈ control ∨ ∃ j ∈ jobs, ev ∈ j.trace) ∧
      scratch endAddr out.privateMem = jobs.foldl (fun s j => j.update s) (scratch endAddr c.privateMem) ∧
      choiceBits es = jobs.flatMap (fun j => choiceBits j.trace) ∧
      es.length = control.length + (jobs.map fun j => j.trace.length).sum ∧
      countProbes es = countProbes control + (jobs.map fun j => countProbes j.trace).sum ∧
      ∀ fuel bs, execute M.program (fuel+es.length) c m (choiceBits es ++ bs) =
        (execute M.program fuel out m bs).map (fun r => ⟨es++r.events,r.result⟩) := by
  induction visits generalizing c top jobs with
  | nil =>
    cases jobs with
    | cons j js => simp at hjobs
    | nil =>
      have htop : top = endAddr := by simpa using hptr
      exact ⟨{c with pc := done}, [.tick], rfl,rfl,he,(fun _ => rfl),(fun _ h => Or.inl h),rfl,rfl,rfl,rfl,
        fun fuel bs => execute_empty hl c hc (by rw [ht,he,htop]) fuel m bs⟩
  | @cons node pending kids nodes src es row fits rest ih =>
    cases jobs with
    | nil => simp at hjobs
    | cons j js =>
      obtain ⟨hj,hjs⟩ := List.cons.inj hjobs
      obtain ⟨popped,hpc,hsp,hnode,hreg,hmemPop,hstate,hstack',hpop⟩ :=
        execute_pop hl c hc top node pending hstack ht (hptr ▸ he) h1
      have hp1 := (hreg (reg 3) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
      have hp6 := (hreg (reg 6) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans he
      obtain ⟨back,hback,hnode',hsp',hend',hone',hstate',hstack'',hupdate,hcall⟩ :=
        hook j List.mem_cons_self popped (top+1) pending (by rw [hmemPop]; exact ready.1) hpc (hnode.trans hj.symm) hstack'
          (by simp only [List.length_cons] at hptr; omega) hsp hp6 hp1
      have hs : kids.length ≤ top+1 := by simp only [List.length_cons] at hptr; omega
      obtain ⟨next,hpc',ht',he',h1',hp',hm,stackNext,hkids⟩ :=
        execute_children hl ha back hback m node.val src (top+1) kids pending row hstack''
          (hnode'.trans (hj.trans (by simp))) hsp' hone' hs
      have ptrNext : top+1-kids.length+(kids++pending).length = endAddr := by
        simp only [List.length_append]; simp only [List.length_cons] at hptr; omega
      have aux : scratch endAddr next.privateMem = scratch endAddr back.privateMem := by
        funext a
        rw [hm]
        change EndpointBits.copySlice _ _ _ _ _ a.val = _
        have bound := a.prop
        unfold EndpointBits.copySlice
        rw [ite_eq_right (by simp only [List.length_append] at ptrNext; omega)]
        rfl
      obtain ⟨out,tail,hout,hper,regEnd,memTail,support,hfinish,hbits,hsteps,hprobes,hex⟩ := ih js hjs
        (fun q hq => hook q (List.mem_cons_of_mem _ hq)) next hpc' _ stackNext ptrNext ht' (he'.trans hend') h1'
        (by rw [aux,hupdate,hmemPop]; exact ready.2)
      let tick3 : List (Event w) := [.tick,.tick,.tick]
      let field := headerEvents w node.val src kids.length ++ EndpointBits.events m src kids.length
      let all := tick3 ++ j.trace ++ field ++ tail
      have bf : choiceBits field = [] := by simp [field,
        headerEvents, choiceBits, choiceBits_copy]
      have fl : field.length = 5*kids.length+7 := by simp [field,headerEvents,length_copy]
      have ab : choiceBits all = choiceBits j.trace ++ choiceBits tail := by
        simp [all, tick3, PrimedInputRAM.Flow.choiceBits_append, choiceBits, bf]
      refine ⟨out,all,hout,hper.trans (hp'.trans (hstate'.trans hstate)),regEnd,?_,?_,?_,?_,?_,?_,?_⟩
      · intro stay
        have copyKeeps (src count : ℕ) : after m (EndpointBits.events m src count) = m := by
          induction count generalizing src with
          | zero => rfl
          | succ n ih => exact ih (src+1)
        have headerKeeps : after m (headerEvents w node.val src kids.length) = m := rfl
        have append (a b : List (Event w)) : after m (a++b) = after (after m a) b := List.foldl_append
        rw [show all = tick3 ++ (j.trace ++ ((headerEvents w node.val src kids.length ++ EndpointBits.events m src kids.length) ++ tail)) by simp [all,field,List.append_assoc],
          append,show after m tick3 = m from rfl,append,stay _ List.mem_cons_self,append,append,headerKeeps,
          copyKeeps,memTail (fun q h => stay _ (List.mem_cons_of_mem _ h))]
      · intro ev hev
        have rest := support ev
        simp only [all, field, tick3, List.mem_append] at hev
        simp only [List.mem_append]
        rcases hev with ((h | h) | (h | h)) | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inr ⟨j,List.mem_cons_self,h⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inl (Or.inr h))
        · rcases rest h with last | ⟨j',member,hit⟩
          · exact Or.inl (Or.inr last)
          · exact Or.inr ⟨j',List.mem_cons_of_mem _ member,hit⟩
      · simpa only [List.foldl_cons, aux, hupdate, hmemPop] using hfinish
      · simp only [List.flatMap_cons, ab, hbits]
      · simp only [all, field, List.length_append, hsteps, List.map_cons, List.sum_cons]
        dsimp [tick3]
        omega
      · simp only [all,field,probes_append,hprobes,List.map_cons,List.sum_cons]
        dsimp [tick3,countProbes]
        omega
      · intro fuel bs
        rw [ab, List.append_assoc]
        have hn : fuel+all.length = ((fuel+tail.length + (5*kids.length+7)) + j.trace.length) + 3 := by
          simp only [all,List.length_append,fl]; dsimp [tick3]; omega
        rw [hn,hpop,hcall,hkids,hex]
        simp [Option.map_map,Function.comp_def,all,tick3,field,List.append_assoc]

/-- The framed traversal, forgetting the support of its event list. -/
theorem execute_linked_visits_framed {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p}
    (hl : Linked M pc reg visit (arcPC 0) done) (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0))
    {m : Memory w} {endAddr : ℕ} {pending nodes : List (Word w)} {control : List (Event w)}
    (visits : Visits m endAddr pending nodes control)
    (jobs : List (VisitPath w endAddr)) (hjobs : jobs.map VisitPath.node = nodes)
    (hook : ∀ job ∈ jobs, job.Linked M visit (pc 3) reg m)
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1)
    (ready : Ready jobs (scratch endAddr c.privateMem)) :
    ∃ out es, out.pc = done ∧ out.persistent = c.persistent ∧ out.reg (reg 6) = (endAddr : Word w) ∧
      ((∀ j ∈ jobs, after m j.trace = m) → after m es = m) ∧
      scratch endAddr out.privateMem = jobs.foldl (fun s j => j.update s) (scratch endAddr c.privateMem) ∧
      choiceBits es = jobs.flatMap (fun j => choiceBits j.trace) ∧
      es.length = control.length + (jobs.map fun j => j.trace.length).sum ∧
      countProbes es = countProbes control + (jobs.map fun j => countProbes j.trace).sum ∧
      ∀ fuel bs, execute M.program (fuel+es.length) c m (choiceBits es ++ bs) =
        (execute M.program fuel out m bs).map (fun r => ⟨es++r.events,r.result⟩) := by
  obtain ⟨out, es, pc', state, endReg, mem, _, rest⟩ :=
    execute_linked_visits_supported hl ha visits jobs hjobs hook c hc top hstack hptr ht he h1 ready
  exact ⟨out, es, pc', state, endReg, mem, rest⟩

/-- The original traversal statement, with the scratch, event, and cost
projections used by callers that do not inspect the ending stack register. -/
theorem execute_linked_visits {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p}
    (hl : Linked M pc reg visit (arcPC 0) done) (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0))
    {m : Memory w} {endAddr : ℕ} {pending nodes : List (Word w)} {control : List (Event w)}
    (visits : Visits m endAddr pending nodes control)
    (jobs : List (VisitPath w endAddr)) (hjobs : jobs.map VisitPath.node = nodes)
    (hook : ∀ job ∈ jobs, job.Linked M visit (pc 3) reg m)
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1)
    (ready : Ready jobs (scratch endAddr c.privateMem)) :
    ∃ out es, out.pc = done ∧ out.persistent = c.persistent ∧
      scratch endAddr out.privateMem = jobs.foldl (fun s j => j.update s) (scratch endAddr c.privateMem) ∧
      choiceBits es = jobs.flatMap (fun j => choiceBits j.trace) ∧
      es.length = control.length + (jobs.map fun j => j.trace.length).sum ∧
      countProbes es = countProbes control + (jobs.map fun j => countProbes j.trace).sum ∧
      ∀ fuel bs, execute M.program (fuel+es.length) c m (choiceBits es ++ bs) =
        (execute M.program fuel out m bs).map (fun r => ⟨es++r.events,r.result⟩) := by
  obtain ⟨out,es,pc,state,_,_,rest⟩ :=
    execute_linked_visits_framed hl ha visits jobs hjobs hook c hc top hstack hptr ht he h1 ready
  exact ⟨out,es,pc,state,rest⟩

end PairSimulation.DFS

end VPVNP
end Computability
end OAI
