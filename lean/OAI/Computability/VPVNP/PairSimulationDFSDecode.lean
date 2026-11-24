import OAI.Computability.VPVNP.PairSimulationDFSHooks

/-!
# Exact-use decoding of linked depth-first calls

For a fixed descriptor tree the node order is deterministic. A local reader
may reject its remaining stream, or consume a prefix and return the updated
scratch state. If the linked local instructions realize each successful
prefix and reject failed reads, the complete native traversal accepts
exactly the strings that decode through all sites with empty suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DFS

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private copyRegs from OAI.Computability.VPVNP.PairSimulationDFS

variable {w p r k : ℕ}

/-- Some fuel suffices to reach an accepting or returning native instruction. -/
def Returns (M : Machine w p r k) (c : Config w p r) (m : Memory w) (bs : List Bool) : Prop :=
  ∃ fuel rep, execute M.program fuel c m bs = some rep

private theorem guessed_addFuel {C : Type*} {P : Program w C} {f : ℕ} {c : C} {es : List (Event w)}
    {res : Option (Word w)} (h : Guessed P f c es res) (extra : ℕ) :
    Guessed P (extra + f) c es res := by
  induction h with
  | done h => exact .done h
  | step h _ ih => exact .step h ih
  | branch h _ ih => exact .branch h ih
  | read h _ ih => exact .read h ih
  | write h _ ih => exact .write h ih

private theorem returns_prefix {M : Machine w p r k} {c d : Config w p r} {m : Memory w}
    {bs tail : List Bool} {n : ℕ} {append : Report w → Report w}
    (h : ∀ f, execute M.program (f + n) c m bs = (execute M.program f d m tail).map append) :
    Returns M c m bs ↔ Returns M d m tail := by
  constructor
  · rintro ⟨f,rep,he⟩
    obtain ⟨hg,hc,hb⟩ := execute_iff.mp he
    have big := execute_iff.mpr ⟨guessed_addFuel hg n,hc,hb⟩
    rw [Nat.add_comm n f,h] at big
    obtain ⟨out,ho,_⟩ := Option.map_eq_some_iff.mp big
    exact ⟨f,out,ho⟩
  · rintro ⟨f,rep,he⟩
    exact ⟨f+n,append rep,by rw [h,he]; rfl⟩

/-- Branch parser for the descriptor indicated by the top stack word. The
argument data are the caller's scratch above the reserved stack interval. -/
structure HookParser (w endAddr : ℕ) where
  /-- Read one descriptor visit from its node address, the current private scratch and the
  remaining choice bits. A successful read returns the selected visit path and unused
  suffix. -/
  read : Word w → Scratch w endAddr → List Bool → Option (VisitPath w endAddr × List Bool)

/-- Decode the nodes in traversal order. After each successful read, apply that visit's scratch
update and pass its unused bits to the next node. A failed read rejects the entire list. -/
def HookParser.decode {endAddr : ℕ} (P : HookParser w endAddr) :
    List (Word w) → Scratch w endAddr → List Bool → Option (Scratch w endAddr × List Bool)
  | [], s, bs => some (s,bs)
  | n :: ns, s, bs => do
    let (job,tail) ← P.read n s bs
    P.decode ns (job.update s) tail

/-- The failed-read obligation applies on any incident bits or scratch
state, including field combinations incompatible across an older wire. -/
structure HookParser.Exact {endAddr : ℕ} (P : HookParser w endAddr) (M : Machine w p r k)
    (visit ret : Fin p) (reg : Fin 9 ↪ Fin r) (m : Memory w) : Prop where
  success : ∀ node s bs job tail, P.read node s bs = some (job,tail) →
    job.node = node ∧ job.enabled s ∧ bs = choiceBits job.trace ++ tail ∧
      job.Linked M visit ret reg m
  reject : ∀ node bs (c : Config w p r) top pending,
    c.pc = visit → c.reg (reg 7) = node → Represents c.privateMem top pending →
    top + pending.length = endAddr → c.reg (reg 5) = (top : Word w) → c.reg (reg 6) = (endAddr : Word w) → c.reg (reg 3) = 1 →
    P.read node (scratch endAddr c.privateMem) bs = none → ¬ Returns M c m bs

/-- Local equivalence on the supplied argument states at a genuine descriptor
address. The domain can record the private pointer layout and the canonical
bit words written by the parent without constraining the bit values. -/
structure HookParser.ExactOn {endAddr : ℕ} (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop) (M : Machine w p r k)
    (visit ret : Fin p) (reg : Fin 9 ↪ Fin r) (m : Memory w) : Prop where
  success : ∀ node s, domain node s → ∀ bs job tail, P.read node s bs = some (job,tail) →
    job.node = node ∧ job.enabled s ∧ bs = choiceBits job.trace ++ tail ∧
      job.Linked M visit ret reg m
  reject : ∀ node bs (c : Config w p r) top pending, domain node (scratch endAddr c.privateMem) →
    c.pc = visit → c.reg (reg 7) = node → Represents c.privateMem top pending →
    top + pending.length = endAddr → c.reg (reg 5) = (top : Word w) → c.reg (reg 6) = (endAddr : Word w) → c.reg (reg 3) = 1 →
    P.read node (scratch endAddr c.privateMem) bs = none → ¬ Returns M c m bs

/-- The invariant is needed at the current visit and, on success, at every
visit reached from its updated scratch state and unconsumed branch suffix. -/
def HookParser.ValidAlong {endAddr : ℕ} (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop) :
    List (Word w) → Scratch w endAddr → List Bool → Prop
  | [], _, _ => True
  | n :: ns, s, bs => domain n s ∧ ∀ job tail, P.read n s bs = some (job,tail) →
      P.ValidAlong domain ns (job.update s) tail

theorem HookParser.validAlong_of_forall {endAddr : ℕ} (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop) (ns : List (Word w))
    (all : ∀ n ∈ ns, ∀ s, domain n s) (s : Scratch w endAddr) (bs : List Bool) :
    P.ValidAlong domain ns s bs := by
  induction ns generalizing s bs with
  | nil => trivial
  | cons n ns ih => exact ⟨all n List.mem_cons_self s, fun job tail _ =>
      ih (fun n hn => all n (List.mem_cons_of_mem _ hn)) (job.update s) tail⟩

/-- Both directions of the native whole-call characterization, for
a terminal continuation that requires exact consumption of the bit stream.
The proof also handles zero-child rows and zero-bit local checks. -/
theorem returns_iff_decode_on {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p} (hl : Linked M pc reg visit (arcPC 0) done)
    (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0)) {m : Memory w} {endAddr : ℕ}
    {pending nodes : List (Word w)} {es : List (Event w)}
    (visits : Visits m endAddr pending nodes es)
    (P : HookParser w endAddr) {domain : Word w → Scratch w endAddr → Prop}
    (exactHook : P.ExactOn domain M visit (pc 3) reg m)
    (terminal : ∀ (c : Config w p r) bs, c.pc = done → (Returns M c m bs ↔ bs = []))
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1) (bs : List Bool)
    (valid : P.ValidAlong domain nodes (scratch endAddr c.privateMem) bs) :
    Returns M c m bs ↔ ∃ out, P.decode nodes (scratch endAddr c.privateMem) bs = some (out,[]) := by
  induction visits generalizing c top bs with
  | nil =>
    have htop : top = endAddr := by simpa using hptr
    rw [returns_prefix (fun f => execute_empty hl c hc (by rw [ht,he,htop]) f m bs),
      terminal _ _ rfl]
    simp [HookParser.decode]
  | @cons node pending kids nodes src es row fits rest ih =>
    obtain ⟨popped,hpc,hsp,hnode,hreg,hpopMem,hstate,hstack',hpop⟩ :=
      execute_pop hl c hc top node pending hstack ht (hptr ▸ he) h1
    have hp1 :=
      (hreg (reg 3) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
    have hp6 :=
      (hreg (reg 6) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans he
    rw [returns_prefix fun f => hpop f m bs]
    cases read : P.read node (scratch endAddr c.privateMem) bs with
    | none =>
      have hn := exactHook.reject node bs popped (top+1) pending (hpopMem ▸ valid.1)
        hpc hnode hstack'
          (by simp only [List.length_cons] at hptr; omega) hsp hp6 hp1
        (by rw [hpopMem]; exact read)
      simp [HookParser.decode,read,hn]
    | some q =>
      obtain ⟨job,tail⟩ := q
      obtain ⟨haddr,hen,hbits,hook⟩ := exactHook.success _ _ valid.1 _ _ _ read
      obtain ⟨back,hback,hnode',hsp',hend',hone',hstate',hstack'',hupdate,hcall⟩ :=
        hook popped (top+1) pending (hpopMem ▸ hen) hpc (hnode.trans haddr.symm) hstack'
          (by simp only [List.length_cons] at hptr; omega) hsp hp6 hp1
      have hreturn : Returns M popped m bs ↔ Returns M back m tail := by
        rw [hbits]
        exact returns_prefix (fun f => hcall f tail)
      have hs : kids.length ≤ top+1 := by simp only [List.length_cons] at hptr; omega
      obtain ⟨next,hpc',ht',he',h1',_,hm,stackNext,hkids⟩ :=
        execute_children hl ha back hback m node.val src (top+1) kids pending row hstack''
          (hnode'.trans (haddr.trans (by simp))) hsp' hone' hs
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
      have validNext : P.ValidAlong domain nodes (scratch endAddr next.privateMem) tail := by
        rw [aux, hupdate, hpopMem]
        exact valid.2 _ _ read
      rw [hreturn,returns_prefix fun f => hkids f tail,
        ih next hpc' _ stackNext ptrNext ht' (he'.trans hend') h1' tail validNext,
        aux,hupdate,hpopMem]
      simp [HookParser.decode,read]

/-- Both directions of the native whole-call characterization, for
a terminal continuation that requires exact consumption of the bit stream.
The proof also handles zero-child rows and zero-bit local checks. -/
theorem returns_iff_decode {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p} (hl : Linked M pc reg visit (arcPC 0) done)
    (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0)) {m : Memory w} {endAddr : ℕ}
    {pending nodes : List (Word w)} {es : List (Event w)}
    (visits : Visits m endAddr pending nodes es)
    (P : HookParser w endAddr) (exactHook : P.Exact M visit (pc 3) reg m)
    (terminal : ∀ (c : Config w p r) bs, c.pc = done → (Returns M c m bs ↔ bs = []))
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1) (bs : List Bool) :
    Returns M c m bs ↔ ∃ out, P.decode nodes (scratch endAddr c.privateMem) bs = some (out,[]) := by
  have exactOn : P.ExactOn (fun _ _ => True) M visit (pc 3) reg m :=
    ⟨fun node s _ => exactHook.success node s,
      fun node bs c top pending _ => exactHook.reject node bs c top pending⟩
  exact returns_iff_decode_on hl ha visits P exactOn terminal c hc top hstack hptr ht he h1 bs
    (P.validAlong_of_forall _ nodes (fun _ _ _ => trivial) _ bs)

end PairSimulation.DFS

end VPVNP
end Computability
end OAI
