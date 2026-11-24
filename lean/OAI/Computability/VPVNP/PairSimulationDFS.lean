import OAI.Computability.VPVNP.PairSimulationEndpointBits
import OAI.Computability.VPVNP.PairSimulationHistory

/-!
# Traversing stored child lists inside a final-vertex burst

The private stack grows downward. After a vertex has been popped, a contiguous
private interval immediately before the pending suffix receives its child
descriptor addresses in increasing list order. This uses one external read per
child and leaves the pending suffix and the rest of private memory untouched.
The next pop therefore visits the first child.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DFS

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- The live stack, from the first pending visit through the last. -/
def Represents (priv : Word w → Word w) (top : ℕ) (xs : List (Word w)) : Prop :=
  top + xs.length < 2^w ∧ ∀ i : Fin xs.length, priv (word w (top+i.val)) = xs[i.val]

theorem represents_cons {priv : Word w → Word w} {top : ℕ} {x : Word w} {xs : List (Word w)}
    (h : Represents priv top (x :: xs)) : priv (word w top) = x ∧ Represents priv (top+1) xs := by
  refine ⟨by simpa using h.2 0, by simpa [Nat.add_assoc, Nat.add_comm 1] using h.1, ?_⟩
  intro i
  have hi : i.val+1 < (x::xs).length := by simp
  simpa [Nat.add_assoc, Nat.add_comm 1] using h.2 ⟨i.val+1, hi⟩

/-- The stored count and row pointer of a descriptor. -/
def Row (m : Memory w) (node src : ℕ) (kids : List (Word w)) : Prop :=
  node+1 < 2^w ∧ src+kids.length < 2^w ∧
  m node = word w src ∧ m (node+1) = word w kids.length ∧ ∀ i : Fin kids.length, m (src+i.val) = kids[i.val]

private theorem copy_children {m : Memory w} {node src top : ℕ} {xs kids : List (Word w)}
    {priv : Word w → Word w} (hstack : Represents priv top xs) (hr : Row m node src kids)
    (hspace : kids.length ≤ top) :
    Represents (EndpointBits.copySlice m src (top - kids.length) kids.length priv) (top - kids.length) (kids ++ xs) := by
  obtain ⟨hfit, hcells⟩ := hstack
  obtain ⟨_, _, _, _, hk⟩ := hr
  have htop : top - kids.length + kids.length = top := Nat.sub_add_cancel hspace
  constructor
  · rw [List.length_append, ← Nat.add_assoc, htop]; exact hfit
  · intro i
    have hi : i.val < kids.length + xs.length := by simpa using i.isLt
    have ha : top - kids.length + i.val < 2^w := by omega
    unfold EndpointBits.copySlice
    simp only [val_word ha]
    by_cases h : i.val < kids.length
    · rw [ite_eq_left (by omega), List.getElem_append_left h]
      simpa using hk ⟨i.val,h⟩
    · rw [ite_eq_right (by omega), List.getElem_append_right (by omega)]
      have he : top - kids.length + i.val = top + (i.val-kids.length) := by omega
      rw [he]
      exact hcells ⟨i.val-kids.length, by omega⟩

/-- Registers 0–4 are shared with the contiguous copy loop. Registers 5–8
hold the stack top, stack end, popped descriptor, and child count. -/
def instruction (pc : Fin 9 → Fin p) (reg : Fin 9 ↪ Fin r) (visit copy done : Fin p) : Fin 9 → Instr w p r k :=
  ![.jumpEq (reg 5) (reg 6) done (pc 1), .loadPrivate (reg 7) (reg 5) (pc 2),
    .binary .add (reg 5) (reg 5) (reg 3) visit,
    .readExternal (reg 0) (reg 7) (pc 4), .binary .add (reg 4) (reg 7) (reg 3) (pc 5),
    .readExternal (reg 8) (reg 4) (pc 6), .binary .sub (reg 5) (reg 5) (reg 8) (pc 7),
    .copy (reg 2) (reg 5) (pc 8), .binary .add (reg 1) (reg 0) (reg 8) copy]

theorem resize_instruction (pc : Fin 9 → Fin p) (reg : Fin 9 ↪ Fin r) (visit copy done : Fin p) (i : Fin 9) :
    (instruction (w := 1) (k := k) pc reg visit copy done i).resize w = instruction pc reg visit copy done i := by
  fin_cases i <;> rfl

/-- Require the nine dispatcher instructions at the specified program counters and registers.
They pop a node, transfer control to `visit`, prepare its child interval for `copy`, and
jump to `done` on an empty stack. -/
def Linked (M : Machine w p r k) (pc : Fin 9 → Fin p) (reg : Fin 9 ↪ Fin r)
    (visit copy done : Fin p) := ∀ i, M.code (pc i) = instruction pc reg visit copy done i

variable {M : Machine w p r k} {pc : Fin 9 → Fin p} {reg : Fin 9 ↪ Fin r} {visit copy done : Fin p}

private theorem step_at (h : Linked M pc reg visit copy done) (c : Config w p r) (i : Fin 9)
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg visit copy done i).run M.publicData c := by
  simp [Machine.program, hc, h i]

private abbrev copyRegs (reg : Fin 9 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 4).trans reg

/-- The empty stack enters the continuation with one deterministic test. -/
theorem execute_empty (hl : Linked M pc reg visit copy done) (c : Config w p r) (hc : c.pc = pc 0)
    (he : c.reg (reg 5) = c.reg (reg 6)) (fuel : ℕ) (m : Memory w) (bs : List Bool) :
    execute M.program (fuel+1) c m bs =
      (execute M.program fuel {c with pc := done} m bs).map (Report.prepend .tick) := by
  have hs : M.program.step c = .localStep {c with pc := done} := by
    rw [step_at hl c 0 hc]
    simp [instruction, Instr.run, he]
  simp only [execute, hs]

/-- One pop selects the descriptor at the top and passes the remaining stack
to the vertex code. This step consumes no binary choice or external probe. -/
theorem execute_pop (hl : Linked M pc reg visit copy done) (c : Config w p r) (hc : c.pc = pc 0)
    (top : ℕ) (x : Word w) (xs : List (Word w)) (hstack : Represents c.privateMem top (x::xs))
    (ht : c.reg (reg 5) = word w top) (he : c.reg (reg 6) = word w (top+(x::xs).length))
    (h1 : c.reg (reg 3) = 1) :
    ∃ out, out.pc = visit ∧ out.reg (reg 5) = word w (top+1) ∧ out.reg (reg 7) = x ∧
      (∀ i, i ≠ reg 5 → i ≠ reg 7 → out.reg i = c.reg i) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ Represents out.privateMem (top+1) xs ∧
      ∀ fuel m bs, execute M.program (fuel+3) c m bs =
        (execute M.program fuel out m bs).map (fun r => ⟨[.tick,.tick,.tick] ++ r.events,r.result⟩) := by
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 7) x
  let out := c₂.put visit (reg 5) (word w (top+1))
  have hn : c.reg (reg 5) ≠ c.reg (reg 6) := by
    rw [ht,he]
    intro h
    have hf := hstack.1
    have hh := congrArg Fin.val h
    rw [val_word (by omega : top < 2^w), val_word hf] at hh
    simp at hh
  have hs₀ : M.program.step c = .localStep c₁ := by rw [step_at hl c 0 hc]; simp [instruction, Instr.run, hn,c₁]
  have hs₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl c₁ 1 rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 7) (c.privateMem (c.reg (reg 5)))) = _
    rw [ht, (represents_cons hstack).1]
  have hs₂ : M.program.step c₂ = .localStep out := by
    rw [step_at hl c₂ 2 rfl]
    change CallAction.localStep (c₂.put visit (reg 5) (c₂.reg (reg 5) + c₂.reg (reg 3))) = _
    simp [c₂,c₁,Config.put,ht,h1,out,word]
  refine ⟨out,rfl,by simp [out],by simp [out,c₂,Config.put],?_,rfl,rfl,(represents_cons hstack).2,?_⟩
  · intro i h5 h7
    simp [out,c₂,c₁,Config.put,Function.update_of_ne h5,Function.update_of_ne h7]
  · intro fuel m bs
    simp [execute, hs₀, hs₁, hs₂, Option.map_map, Function.comp_def, Report.prepend]

private def prepared (c : Config w p r) (pc : Fin 9 → Fin p) (reg : Fin 9 ↪ Fin r)
    (copy : Fin p) (node src top count : ℕ) : Config w p r :=
  let c₄ := c.put (pc 4) (reg 0) (word w src)
  let c₅ := c₄.put (pc 5) (reg 4) (word w (node+1))
  let c₆ := c₅.put (pc 6) (reg 8) (word w count)
  let c₇ := c₆.put (pc 7) (reg 5) (word w (top-count))
  let c₈ := c₇.put (pc 8) (reg 2) (word w (top-count))
  c₈.put copy (reg 1) (word w (src+count))

private def headerEvents (w node src count : ℕ) : List (Event w) :=
  [.read (word w node) (word w src), .tick, .read (word w (node+1)) (word w count), .tick, .tick, .tick]

private theorem prepare_execute (hl : Linked M pc reg visit copy done) (c : Config w p r) (hc : c.pc = pc 3)
    (m : Memory w) (node src top : ℕ) (kids : List (Word w)) (hr : Row m node src kids)
    (hnode : c.reg (reg 7) = word w node) (ht : c.reg (reg 5) = word w top)
    (hone : c.reg (reg 3) = 1) (space : kids.length ≤ top) (fuel : ℕ) (bs : List Bool) :
    execute M.program (fuel+6) c m bs =
      (execute M.program fuel (prepared c pc reg copy node src top kids.length) m bs).map
        (fun rep => ⟨headerEvents w node src kids.length ++ rep.events, rep.result⟩) := by
  let c₄ := c.put (pc 4) (reg 0) (word w src)
  let c₅ := c₄.put (pc 5) (reg 4) (word w (node+1))
  let c₆ := c₅.put (pc 6) (reg 8) (word w kids.length)
  let c₇ := c₆.put (pc 7) (reg 5) (word w (top-kids.length))
  let c₈ := c₇.put (pc 8) (reg 2) (word w (top-kids.length))
  have s₃ : M.program.step c = .read (word w node) (fun t => c.put (pc 4) (reg 0) t) := by
    rw [step_at hl c 3 hc]; simp [instruction,Instr.run,hnode]
  have s₄ : M.program.step c₄ = .localStep c₅ := by
    rw [step_at hl c₄ 4 rfl]
    change CallAction.localStep (c₄.put (pc 5) (reg 4) (c₄.reg (reg 7) + c₄.reg (reg 3))) = _
    simp [c₄,c₅,Config.put,hnode,hone,word]
  have s₅ : M.program.step c₅ = .read (word w (node+1)) (fun t => c₅.put (pc 6) (reg 8) t) := by
    rw [step_at hl c₅ 5 rfl]; simp [instruction, Instr.run,c₅]
  have s₆ : M.program.step c₆ = .localStep c₇ := by
    rw [step_at hl c₆ 6 rfl]
    change CallAction.localStep (c₆.put (pc 7) (reg 5) (c₆.reg (reg 5) - c₆.reg (reg 8))) = _
    simp [c₄,c₅,c₆,c₇,Config.put,ht,word,Nat.cast_sub space]
  have s₇ : M.program.step c₇ = .localStep c₈ := by
    rw [step_at hl c₇ 7 rfl]; simp [instruction,Instr.run,c₇,c₈]
  have s₈ : M.program.step c₈ = .localStep (prepared c pc reg copy node src top kids.length) := by
    rw [step_at hl c₈ 8 rfl]
    change CallAction.localStep (c₈.put copy (reg 1) (c₈.reg (reg 0) + c₈.reg (reg 8))) = _
    simp [c₈,c₇,c₆,c₅,c₄,Config.put,prepared,word]
  have read₃ : m (word w node).val = word w src := by rw [val_word (by have := hr.1; omega : node < 2^w)]; exact hr.2.2.1
  have read₅ : m (word w (node+1)).val = word w kids.length := by rw [val_word hr.1]; exact hr.2.2.2.1
  have eq₄ : c.put (pc 4) (reg 0) (word w src) = c₄ := rfl
  have eq₆ : c₅.put (pc 6) (reg 8) (word w kids.length) = c₆ := rfl
  simp only [execute, s₃, read₃, eq₄, s₄, s₅, read₅, eq₆, s₆, s₇, s₈]
  simp [Option.map_map, Function.comp_def, Report.prepend, headerEvents]

/-- The descriptor header costs two probes, and the loop fetches each child
address once. The returned stack begins with the complete ordered child
list, followed by the original pending vertices. -/
theorem execute_children {arcPC : Fin 5 → Fin p} (hl : Linked M pc reg visit (arcPC 0) done)
    (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0)) (c : Config w p r) (hc : c.pc = pc 3)
    (m : Memory w) (node src top : ℕ) (kids pending : List (Word w))
    (hr : Row m node src kids) (hstack : Represents c.privateMem top pending)
    (hnode : c.reg (reg 7) = word w node) (ht : c.reg (reg 5) = word w top)
    (h1 : c.reg (reg 3) = 1) (hspace : kids.length ≤ top) :
    ∃ out, out.pc = pc 0 ∧ out.reg (reg 5) = word w (top-kids.length) ∧
      out.reg (reg 6) = c.reg (reg 6) ∧ out.reg (reg 3) = 1 ∧ out.persistent = c.persistent ∧
      out.privateMem = EndpointBits.copySlice m src (top-kids.length) kids.length c.privateMem ∧
      Represents out.privateMem (top-kids.length) (kids ++ pending) ∧
      ∀ fuel bs, execute M.program (fuel + (5*kids.length+7)) c m bs =
        (execute M.program fuel out m bs).map (fun rep =>
          ⟨headerEvents w node src kids.length ++ EndpointBits.events m src kids.length ++ rep.events, rep.result⟩) := by
  let start := prepared c pc reg (arcPC 0) node src top kids.length
  have htop : top - kids.length + kids.length = top := Nat.sub_add_cancel hspace
  have fit : top - kids.length + kids.length < 2^w := by rw [htop]; have := hstack.1; omega
  obtain ⟨out,hpc,hpriv,_,_,other,hmem,hex⟩ := EndpointBits.execute_arc ha start rfl m src (top-kids.length)
    kids.length hr.2.1 fit
    (by change start.reg (reg 0) = _; simp [start,prepared,Config.put])
    (by change start.reg (reg 1) = _; simp [start,prepared,Config.put])
    (by change start.reg (reg 2) = _; simp [start,prepared,Config.put])
    (by change start.reg (reg 3) = _; simp [start,prepared,Config.put,h1])
  have memEq : out.privateMem = EndpointBits.copySlice m src (top-kids.length) kids.length c.privateMem := hmem
  refine ⟨out,hpc,?_,?_,?_,hpriv,memEq,memEq ▸ copy_children hstack hr hspace,?_⟩
  · rw [other (reg 5) (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))]
    simp [start,prepared,Config.put]
  · rw [other (reg 6) (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))]
    simp [start,prepared,Config.put]
  · rw [other (reg 3) (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))]
    simp [start,prepared,Config.put,h1]
  · intro fuel bs
    rw [show fuel + (5*kids.length+7) = (fuel+5*kids.length+1)+6 by omega,
      prepare_execute hl c hc m node src top kids hr hnode ht h1 hspace]
    change (execute M.program (fuel+5*kids.length+1) start m bs).map _ = _
    rw [hex]
    simp [Option.map_map,Function.comp_def]

theorem children_probes (m : Memory w) (node src count : ℕ) :
    countProbes (headerEvents w node src count ++ EndpointBits.events m src count) = 2 + count := by
  simp [headerEvents, countProbes, EndpointBits.probes, Nat.add_comm, Nat.add_left_comm]

/-- A terminating descent through the actual rows in external memory.
The list index retains the order of every visit, including multiple visits
to equal descriptor addresses if the input rows contain duplicates. -/
inductive Visits (m : Memory w) (endAddr : ℕ) :
    List (Word w) → List (Word w) → List (Event w) → Prop
  | nil : Visits m endAddr [] [] [.tick]
  | cons {node : Word w} {pending kids nodes : List (Word w)} {src : ℕ} {es : List (Event w)}
      (row : Row m node.val src kids) (fits : kids.length + pending.length ≤ endAddr)
      (rest : Visits m endAddr (kids ++ pending) nodes es) :
      Visits m endAddr (node :: pending) (node :: nodes)
        ([.tick,.tick,.tick] ++ headerEvents w node.val src kids.length ++
          EndpointBits.events m src kids.length ++ es)

/-- All visits of a finite traversal are realized by the fixed RAM
dispatcher when the entry hook immediately returns to the child-row scan.
The continuation may use all remaining fuel and arbitrary branch bits. -/
theorem execute_visits {arcPC : Fin 5 → Fin p}
    (hl : Linked M pc reg (pc 3) (arcPC 0) done)
    (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0))
    {m : Memory w} {endAddr : ℕ} {pending nodes : List (Word w)} {es : List (Event w)}
    (visits : Visits m endAddr pending nodes es) (c : Config w p r) (hc : c.pc = pc 0)
    (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = word w top)
    (he : c.reg (reg 6) = word w endAddr) (h1 : c.reg (reg 3) = 1) :
    ∃ out, out.pc = done ∧ out.reg (reg 5) = word w endAddr ∧ out.persistent = c.persistent ∧
      ∀ fuel bs, execute M.program (fuel + es.length) c m bs =
        (execute M.program fuel out m bs).map (fun r => ⟨es ++ r.events, r.result⟩) := by
  induction visits generalizing c top with
  | nil =>
    have htop : top = endAddr := by simpa using hptr
    refine ⟨{c with pc := done}, rfl, htop ▸ ht, rfl, ?_⟩
    intro fuel bs
    exact execute_empty hl c hc (by rw [ht,he,htop]) fuel m bs
  | @cons node pending kids nodes src es row fits rest ih =>
    obtain ⟨popped,hpc,hsp,hnode,hreg,hmemory,hstate,hstack',hpop⟩ :=
      execute_pop hl c hc top node pending hstack ht (hptr ▸ he) h1
    have hp1 := (hreg (reg 3) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
    have hp6 := (hreg (reg 6) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans he
    have hs : kids.length ≤ top+1 := by simp only [List.length_cons] at hptr; omega
    obtain ⟨next,hpc',ht',he',h1',hp',_,stackNext,hkids⟩ :=
      execute_children hl ha popped hpc m node.val src (top+1) kids pending row hstack'
        (hnode.trans (by simp [word])) hsp hp1 hs
    have ptrNext : top + 1 - kids.length + (kids ++ pending).length = endAddr := by
      simp only [List.length_append]; simp only [List.length_cons] at hptr; omega
    obtain ⟨out,hout,htout,hstateout,hex⟩ :=
      ih next hpc' _ stackNext ptrNext ht' (he'.trans hp6) h1'
    refine ⟨out,hout,htout,hstateout.trans (hp'.trans hstate),?_⟩
    intro fuel bs
    have hlen (m : Memory w) (src n : ℕ) : (EndpointBits.events m src n).length = 5*n+1 := by
      induction n generalizing src with
      | zero => rfl
      | succ n ih => simp [EndpointBits.events,ih]; omega
    rw [show fuel + (([.tick,.tick,.tick] : List (Event w)) ++ headerEvents w node.val src kids.length ++
        EndpointBits.events m src kids.length ++ es).length =
        ((fuel+es.length) + (5*kids.length+7)) + 3 by
      simp only [List.length_append, headerEvents, List.length_cons, List.length_nil, hlen]; omega]
    rw [hpop, hkids, hex]
    simp [Option.map_map, Function.comp_def, List.append_assoc]

end PairSimulation.DFS

end VPVNP
end Computability
end OAI
