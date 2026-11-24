import OAI.Computability.VPVNP.PairSimulationDFSDecode
import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-!
# Dispatching an ordered history visit by its recorded role

The common DFS pop leaves the absolute descriptor address in register 7.
A single external word lookup selects the cursor leaf, six-party shrinking,
or degree-refresh entry routine. The six instructions preserve the
private stack, histogram, pending suffix and the node address itself.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeDispatch

open BurstRAM BurstRAM.PrivateRAM DFS
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {w p r k : ℕ}

/-- The three handlers for a visited DFS node are the cursor leaf, the six-party shrink step
and the degree refresh step. -/
inductive Role
  | leaf | shrink | refresh
  deriving DecidableEq

/-- Decodes the stored role word. Zero selects the leaf handler, one selects shrink, and every
other value selects refresh. -/
def role (tag : Word w) : Role :=
  if tag = 0 then .leaf else if tag = 1 then .shrink else .refresh

/-- Fetch the role word from the side table indexed by the absolute
descriptor address. Only two temporary registers are modified. -/
def instruction (pc : Fin 6 → Fin p) (reg : Fin 9 ↪ Fin r) (field : Fin k)
    (entry : Role → Fin p) : Fin 6 → Instr w p r k :=
  ![.publicWord (reg 0) field (pc 1), .binary .add (reg 0) (reg 0) (reg 7) (pc 2),
    .readExternal (reg 0) (reg 0) (pc 3), .constant (reg 1) 0 (pc 4),
    .jumpEq (reg 0) (reg 1) (entry .leaf) (pc 5),
    .jumpEq (reg 0) (reg 3) (entry .shrink) (entry .refresh)]

theorem resize_instruction (pc : Fin 6 → Fin p) (reg : Fin 9 ↪ Fin r) (field : Fin k)
    (entry : Role → Fin p) (i : Fin 6) :
    (instruction (w := 1) pc reg field entry i).resize w = instruction pc reg field entry i := by
  fin_cases i <;> rfl

/-- Requires the machine to contain all six dispatcher instructions at the specified program
counters, with the supplied register placement, role-table offset operand and handler entry
points. -/
def Linked (M : Machine w p r k) (pc : Fin 6 → Fin p) (reg : Fin 9 ↪ Fin r) (field : Fin k)
    (entry : Role → Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc reg field entry i

/-- Trace for dispatching one node. The external read is at offset + node, and a nonzero tag
takes one further tick to distinguish shrink from refresh. -/
def events (m : Memory w) (offset node : Word w) : List (Event w) :=
  let a := offset + node
  let tag := m a.val
  [.tick, .tick, .read a tag, .tick, .tick] ++ if tag = 0 then [] else [.tick]

theorem events_cost (m : Memory w) (offset node : Word w) :
    countProbes (events m offset node) = 1 ∧ (events m offset node).length ≤ 6 ∧
      choiceBits (events m offset node) = [] := by
  by_cases hz : m (offset+node).val = 0 <;> simp [events, hz, countProbes, choiceBits]

variable {M : Machine w p r k} {pc : Fin 6 → Fin p} {reg : Fin 9 ↪ Fin r} {field : Fin k}
    {entry : Role → Fin p}

private theorem step_at (hl : Linked M pc reg field entry) (i : Fin 6) (c : Config w p r)
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg field entry i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- The common five rows after the offset load work for either a public
word or a base obtained from the terminal geometry record. -/
theorem enter_loaded (offset : Word w) (c : Config w p r)
    (first : M.program.step c = .localStep (c.put (pc 1) (reg 0) offset))
    (later : ∀ i : Fin 6, i ≠ 0 → M.code (pc i) = instruction pc reg field entry i)
    (h1 : c.reg (reg 3) = 1) (m : Memory w) :
    let node := c.reg (reg 7)
    let tag := m (offset+node).val
    ∃ out, out.pc = entry (role tag) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ (∀ j, j ≠ reg 0 → j ≠ reg 1 → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+(events m offset node).length) c m bs =
        (execute M.program fuel out m bs).map
          (fun rep => ⟨events m offset node ++ rep.events,rep.result⟩) := by
  intro node tag
  have step (i : Fin 6) (hi : i ≠ 0) (d : Config w p r) (hd : d.pc = pc i) :
      M.program.step d = (instruction pc reg field entry i).run M.publicData d := by
    change (M.code d.pc).run _ _ = _
    rw [hd, later i hi]
  let a := offset+node
  let c₁ := c.put (pc 1) (reg 0) offset
  let c₂ := c₁.put (pc 2) (reg 0) a
  let c₃ := c₂.put (pc 3) (reg 0) tag
  let c₄ := c₃.put (pc 4) (reg 1) 0
  let leave (j : Fin p) := {c₄ with pc := j}
  let pre : List (Event w) := [.tick,.tick,.read a tag,.tick,.tick]
  have s₀ : M.program.step c = .localStep c₁ := first
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step 1 (by decide) c₁ rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 0) (c₁.reg (reg 0)+c₁.reg (reg 7))) = _
    simp [c₁,c₂,a,node,Config.put]
  have s₂ : M.program.step c₂ = .read a (fun v => c₂.put (pc 3) (reg 0) v) := by
    rw [step 2 (by decide) c₂ rfl]
    change CallAction.read (c₂.reg (reg 0)) _ = _
    exact congrArg (fun t => CallAction.read t _) (Config.put_same ..)
  have s₃ : M.program.step c₃ = .localStep c₄ := step 3 (by decide) c₃ rfl
  have s₄ : M.program.step c₄ = .localStep (leave (if tag=0 then entry .leaf else pc 5)) := by
    rw [step 4 (by decide) c₄ rfl]
    change CallAction.localStep {c₄ with pc := if c₄.reg (reg 0) = c₄.reg (reg 1) then _ else _} = _
    simp [c₄,c₃,leave,Config.put]
  have finish {q : Fin p} {es : List (Event w)}
      (h : ReadPrefix M m (leave (if tag=0 then entry .leaf else pc 5)) es (leave q)) :
      ReadPrefix M m c (pre++es) (leave q) :=
    ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.read a s₂
      (ReadPrefix.tick s₃ (ReadPrefix.tick s₄ h))))
  let q := entry (role tag)
  have h : ReadPrefix M m c (events m offset node) (leave q) := by
    by_cases hz : tag = 0
    · have hq : (if tag=0 then entry .leaf else pc 5) = q := by simp [hz,q,role]
      have he : events m offset node = pre++[] := by
        change pre ++ (if tag = 0 then [] else [.tick]) = _
        rw [ite_eq_left hz]
      rw [he]
      apply finish
      rw [hq]
      exact ReadPrefix.nil _
    · have s₅ : M.program.step (leave (pc 5)) = .localStep (leave q) := by
        rw [step 5 (by decide) (leave (pc 5)) rfl]
        change CallAction.localStep {leave (pc 5) with pc :=
          (if (leave (pc 5)).reg (reg 0) = (leave (pc 5)).reg (reg 3) then entry .shrink
          else entry .refresh)} = _
        dsimp only [leave, c₄, c₃, c₂, c₁, Config.put, q, role]
        simp [hz,h1]
        split <;> rfl
      have he : events m offset node = pre++[.tick] := by
        change pre ++ (if tag = 0 then [] else [.tick]) = _
        rw [ite_eq_right hz]
      rw [he]
      apply finish
      rw [ite_eq_right hz]
      exact ReadPrefix.tick s₅ (ReadPrefix.nil _)
  refine ⟨leave q, rfl, rfl, rfl, ?_, ReadPrefix.execute h⟩
  intro j hj₀ hj₁
  simp [leave,c₄,c₃,c₂,c₁,Config.put,Function.update_of_ne hj₀,Function.update_of_ne hj₁]

/-- The fetched word selects the corresponding native continuation without
consuming any of the remaining private choices. -/
theorem enter (hl : Linked M pc reg field entry) (c : Config w p r) (hc : c.pc = pc 0)
    (h1 : c.reg (reg 3) = 1) (m : Memory w) :
    let offset := M.publicData field
    let node := c.reg (reg 7)
    let tag := m (offset+node).val
    ∃ out, out.pc = entry (role tag) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ (∀ j, j ≠ reg 0 → j ≠ reg 1 → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+(events m offset node).length) c m bs =
        (execute M.program fuel out m bs).map
          (fun rep => ⟨events m offset node ++ rep.events,rep.result⟩) :=
  enter_loaded (M.publicData field) c (step_at hl 0 c hc) (fun i _ => hl i) h1 m

/-- Parser of the actual dispatch opcode, retaining its deterministic
prefix in the visit path. -/
def parser {endAddr : ℕ} (handlers : Role → HookParser w endAddr) (m : Memory w)
    (offset : Word w) : HookParser w endAddr where
  read node s bs := ((handlers (role (m (offset+node).val))).read node s bs).map fun (job,tail) =>
    ({job with trace := events m offset node ++ job.trace},tail)

/-- Exact leaf, shrink and refresh handlers at their native entry labels
compose with the fixed role router, on successful reads and rejection. -/
theorem parser_exactOn {endAddr : ℕ} {domain : Word w → Scratch w endAddr → Prop}
    (hl : Linked M pc reg field entry) (ret : Fin p)
    (m : Memory w) (handlers : Role → HookParser w endAddr)
    (h : ∀ i, (handlers i).ExactOn
      (fun node s => domain node s ∧ role (m (M.publicData field + node).val) = i)
      M (entry i) ret reg m) :
    (parser handlers m (M.publicData field)).ExactOn domain M (pc 0) ret reg m := by
  let offset := M.publicData field
  constructor
  · intro node s hd bs job tail result
    let i := role (m (offset+node).val)
    obtain ⟨⟨j, rest⟩, read, eq⟩ := Option.map_eq_some_iff.mp result
    cases eq
    obtain ⟨hnode, hen, hbs, body⟩ := (h i).success node s ⟨hd, rfl⟩ bs j tail read
    refine ⟨hnode, hen, ?_, ?_⟩
    · simpa only [PrimedInputRAM.Flow.choiceBits_append,
        (events_cost m (M.publicData field) node).2.2,
        List.nil_append] using hbs
    · intro c top pending enabled hc hn hs hend ht he h1
      obtain ⟨mid, hm, mem, persist, regs, run⟩ := enter hl c hc h1 m
      rw [hn, hnode] at hm run
      have kept (i : Fin 9) (hi : i ≠ 0) (hi' : i ≠ 1) :=
        regs (reg i) (reg.injective.ne hi) (reg.injective.ne hi')
      obtain ⟨out, hp, hn', ht', he', h1', pst, st, upd, work⟩ := body mid top pending
        (mem ▸ enabled) hm ((kept 7 (by decide) (by decide)).trans hn) (mem ▸ hs) hend
        ((kept 5 (by decide) (by decide)).trans ht) ((kept 6 (by decide) (by decide)).trans he)
        ((kept 3 (by decide) (by decide)).trans h1)
      refine ⟨out,hp,hn',ht',he',h1',pst.trans persist,st,mem ▸ upd,?_⟩
      intro fuel suffix
      simp only [PrimedInputRAM.Flow.choiceBits_append,
        (events_cost m (M.publicData field) node).2.2, List.nil_append,
        List.length_append]
      rw [show fuel + ((events m offset node).length+j.trace.length) =
        (fuel+j.trace.length)+(events m offset node).length by omega, run, work]
      simp only [Option.map_map, Function.comp_def, List.append_assoc]
  · intro node bs c top pending hd hc hn hs hend ht he h1 fail
    let i := role (m (offset+node).val)
    have read : (handlers i).read node (scratch endAddr c.privateMem) bs = none :=
      Option.map_eq_none_iff.mp fail
    obtain ⟨mid, hm, mem, _, regs, run⟩ := enter hl c hc h1 m
    rw [hn] at hm run
    have kept (i : Fin 9) (hi : i ≠ 0) (hi' : i ≠ 1) :=
      regs (reg i) (reg.injective.ne hi) (reg.injective.ne hi')
    have reject := (h i).reject node bs mid top pending ⟨mem ▸ hd, rfl⟩ hm
      ((kept 7 (by decide) (by decide)).trans hn) (mem ▸ hs) hend
      ((kept 5 (by decide) (by decide)).trans ht) ((kept 6 (by decide) (by decide)).trans he)
      ((kept 3 (by decide) (by decide)).trans h1) (mem ▸ read)
    exact fun ok => reject ((returns_prefix (fun fuel => run fuel bs)).mp ok)

/-- Exact leaf, shrink and refresh handlers at their native entry labels
compose with the fixed role router, on successful reads and rejection. -/
theorem parser_exact {endAddr : ℕ}
    (hl : Linked M pc reg field entry) (ret : Fin p)
    (m : Memory w) (handlers : Role → HookParser w endAddr)
    (h : ∀ i, (handlers i).Exact M (entry i) ret reg m) :
    (parser handlers m (M.publicData field)).Exact M (pc 0) ret reg m := by
  have h' := parser_exactOn (domain := fun _ _ => True) hl ret m handlers
    (fun i => ⟨fun node s _ => (h i).success node s,
      fun node bs c top pending _ => (h i).reject node bs c top pending⟩)
  exact ⟨fun node s => h'.success node s trivial,
    fun node bs c top pending => h'.reject node bs c top pending trivial⟩

end PairSimulation.NodeDispatch

end VPVNP
end Computability
end OAI
