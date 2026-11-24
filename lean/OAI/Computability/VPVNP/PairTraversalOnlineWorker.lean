import OAI.Computability.VPVNP.CompressorFlowRebase
import OAI.Computability.VPVNP.PairTraversalLeafWorker
import OAI.Computability.VPVNP.PairTraversalSiteWorker
import OAI.Computability.VPVNP.PairTraversalRoleNative

/-!
# Running traversal workers with the selected layer's directory words

A leaf, a placement fiber and a role tag are written by fixed programs. At
their online entry the current site ordinal and the layout words are in
registers. Each former parameter or state load becomes a single private copy.
The emitted events, memory image and branch bits agree with the original
worker, including every iteration of the fiber scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.OnlineWorker

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM PrimedCounter
open scoped Fin.CommRing

variable {w r k R : ℕ}

private def opAt (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R) :
    Op r k → Op R 11
  | .publicWord dst i => .copy (reg dst) (bank i)
  | op => CompressorRecords.Rebased.opAt reg (fun _ => 0) arg op

open private restrict_update from OAI.Computability.VPVNP.PrimedCounterRename

private theorem effect (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R) (op : Op r k)
    (data : Fin 11 → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w) :
    ((opAt reg bank arg op).effect data state rs mem).map (fun (e, r', m') => (e, r' ∘ reg, m')) =
      op.effect (rs ∘ bank) (rs arg) (rs ∘ reg) mem := by
  cases op <;> simp [opAt, CompressorRecords.Rebased.opAt, renameOp, Op.effect,
    restrict_update, Function.comp_apply]

/-- Replace the component's public inputs and persistent input with register reads. -/
def code (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R) : Flow r k → Flow R 11
  | .line op => .line (opAt reg bank arg op)
  | .seq a b => .seq (code reg bank arg a) (code reg bank arg b)
  | .ifEq x y a b => .ifEq (reg x) (reg y) (code reg bank arg a) (code reg bank arg b)
  | .ifLt x y a b => .ifLt (reg x) (reg y) (code reg bank arg a) (code reg bank arg b)
  | .branch a b => .branch (code reg bank arg a) (code reg bank arg b)
  | .whileLt x y a => .whileLt (reg x) (reg y) (code reg bank arg a)

private theorem line_outside (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R)
    (op : Op r k) (data : Fin 11 → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w)
    {e out m'} (he : (opAt reg bank arg op).effect data state rs mem = some (e, out, m'))
    (j : Fin R) (hj : j ∉ Set.range reg) : out j = rs j := by
  have hn (i : Fin r) : j ≠ reg i := fun hh => hj ⟨i, hh.symm⟩
  cases op <;> simp only [opAt, CompressorRecords.Rebased.opAt, renameOp, Op.effect] at he
  all_goals first | split at he | skip
  all_goals first | contradiction | (cases Option.some.inj he; simp [Function.update_of_ne (hn _)])

/-- Lift a worker derivation to a call with runtime directory words. The
outer machine retains its persistent state and every register outside the scratch bank. -/
theorem liftExec (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R)
    (hbank : ∀ j, bank j ∉ Set.range reg) (harg : arg ∉ Set.range reg)
    (data : Fin 11 → Word w) {params : Fin k → Word w} {state site : Word w}
    {a : Flow r k} {small m es out m'}
    (he : Flow.Exec params site a small m es out m') (rs : Regs w R)
    (hr : rs ∘ reg = small) (hp : rs ∘ bank = params) (hs : rs arg = site) :
    ∃ rs', Flow.Exec data state (code reg bank arg a) rs m es rs' m' ∧
      rs' ∘ reg = out ∧ ∀ j, j ∉ Set.range reg → rs' j = rs j := by
  induction he generalizing rs with
  | @line op small m e small' m' h =>
    have hx := effect reg bank arg op data state rs m
    rw [hr, hp, hs, h] at hx
    obtain ⟨⟨ev, rs', m''⟩, hh, heq⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨rfl, heq, rfl⟩ := Prod.mk.inj heq
    exact ⟨rs', .line hh, rfl, line_outside reg bank arg op data state rs m hh⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨mid, hm, he, ho⟩ := ih₁ rs hr hp hs
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he
      ((funext fun j => ho (bank j) (hbank j)).trans hp) ((ho arg harg).trans hs)
    exact ⟨out, .seq hm hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr hp hs
    rw [← hr] at ht
    first | exact ⟨out, .ifEqYes ht ho, he, hh⟩ | exact ⟨out, .ifEqNo ht ho, he, hh⟩
          | exact ⟨out, .ifLtYes ht ho, he, hh⟩ | exact ⟨out, .ifLtNo ht ho, he, hh⟩
  | branchYes _ ih | branchNo _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr hp hs
    first | exact ⟨out, .branchYes ho, he, hh⟩ | exact ⟨out, .branchNo ho, he, hh⟩
  | whileDone ht =>
    rw [← hr] at ht
    exact ⟨rs, .whileDone ht, hr, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    obtain ⟨mid, hb, he, ho⟩ := ih₁ rs hr hp hs
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he
      ((funext fun j => ho (bank j) (hbank j)).trans hp) ((ho arg harg).trans hs)
    rw [← hr] at ht
    exact ⟨out, .whileStep ht hb hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩

/-- Conversely, every successful enclosing execution restricts to a genuine
execution of the original program. Both directions include the exact event log. -/
theorem restrictExec (reg : Fin r ↪ Fin R) (bank : Fin k → Fin R) (arg : Fin R)
    (hbank : ∀ j, bank j ∉ Set.range reg) (outside : arg ∉ Set.range reg) (data : Fin 11 → Word w)
    {state : Word w} (a : Flow r k) {rs m es out m'}
    (he : Flow.Exec data state (code reg bank arg a) rs m es out m') :
    Flow.Exec (rs ∘ bank) (rs arg) a (rs ∘ reg) m es (out ∘ reg) m' ∧
      ∀ j, j ∉ Set.range reg → out j = rs j := by
  generalize hcmd : code reg bank arg a = cmd at he
  induction he generalizing a with
  | @line op rs m e out m' h =>
    cases a <;> simp only [code, reduceCtorEq, Flow.line.injEq] at hcmd
    subst op
    constructor
    · apply Flow.Exec.line
      rw [← effect reg bank arg _ data state rs m, h]
      rfl
    · exact line_outside reg bank arg _ data state rs m h
  | seq _ _ ih₁ ih₂ =>
    cases a <;> simp only [code, reduceCtorEq, Flow.seq.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ ha
    obtain ⟨h₂, o₂⟩ := ih₂ _ hb
    rw [o₁ arg outside, show _ ∘ bank = _ ∘ bank from funext (fun j => o₁ (bank j) (hbank j))] at h₂
    exact ⟨.seq h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    cases a <;> simp only [code, reduceCtorEq, Flow.ifEq.injEq, Flow.ifLt.injEq] at hcmd
    obtain ⟨rfl, rfl, ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifEqYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifEqNo ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifLtYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifLtNo ht h, ho⟩
  | branchYes _ ih | branchNo _ ih =>
    cases a <;> simp only [code, reduceCtorEq, Flow.branch.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.branchYes h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.branchNo h, ho⟩
  | whileDone ht =>
    cases a <;> simp only [code, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, _⟩ := hcmd
    exact ⟨.whileDone ht, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    cases a <;> simp only [code, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, rfl⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ rfl
    obtain ⟨h₂, o₂⟩ := ih₂ (.whileLt _ _ _) rfl
    rw [o₁ arg outside, show _ ∘ bank = _ ∘ bank from funext (fun j => o₁ (bank j) (hbank j))] at h₂
    exact ⟨.whileStep ht h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩

/-- The three workers share at most seven scratch registers, six directory
words and the site cursor. The enclosing machine can reserve more registers. -/
structure Allocation (R : ℕ) where
  /-- Embed the seven registers available for a traversal worker's scratch calculations. -/
  scratch : Fin 7 ↪ Fin R
  /-- Assign each of the worker's six runtime bank words to its enclosing register. -/
  bank : Fin 6 → Fin R
  /-- Register holding the current site ordinal for the installed worker. -/
  site : Fin R
  bankOutside : ∀ j, bank j ∉ Set.range scratch
  siteOutside : site ∉ Set.range scratch

namespace Allocation

/-- Scratch registers occupy positions 0 through 6. The six layout words
occupy positions 7 through 12 and the site cursor occupies position 13. -/
def «prefix» (room : 14 ≤ R) : Allocation R where
  scratch := Fin.castLEEmb (by omega)
  bank j := ⟨7 + j.val, by have := j.isLt; omega⟩
  site := ⟨13, by omega⟩
  bankOutside j := by
    rintro ⟨i, e⟩
    have := congrArg Fin.val e
    change i.val = 7 + j.val at this
    omega
  siteOutside := by
    rintro ⟨i, e⟩
    have := congrArg Fin.val e
    change i.val = 13 at this
    omega

variable (A : Allocation R)

/-- Restrict the seven-register scratch embedding to the smaller bank required by a particular
worker. -/
def regs {n : ℕ} (h : n ≤ 7) : Fin n ↪ Fin R := (Fin.castLEEmb h).trans A.scratch

/-- Select a prefix of the six runtime bank words for a worker with fewer parameters. -/
def words {n : ℕ} (h : n ≤ 6) : Fin n → Fin R := A.bank ∘ Fin.castLE h

/-- Install the leaf-row writer with its allocated scratch registers, directory words, and site
ordinal. -/
def leaf : Flow R 11 :=
  code (A.regs (by decide)) (A.words (by decide)) A.site LeafWorker.program

/-- Install the preimage-fiber row writer using the full scratch and public parameter banks. -/
def fiber : Flow R 11 := code A.scratch A.bank A.site SiteWorker.program

/-- Install the role-tag writer for a single selected site using the corresponding smaller
register banks. -/
def role : Flow R 11 := code (A.regs (by decide)) (A.words (by decide)) A.site
  (lines TraversalRoles.Native.visit (by decide))

private theorem regs_outside {n : ℕ} (h : n ≤ 7) {j : Fin R} (hj : j ∉ Set.range A.scratch) :
    j ∉ Set.range (A.regs h) := fun ⟨i, hi⟩ => hj ⟨i.castLE h, hi⟩

private theorem small_lift {n k : ℕ} (hn : n ≤ 7) (hk : k ≤ 6) (data : Fin 11 → Word w)
    {pub : Fin k → Word w} {state site : Word w} {a : Flow n k} {m es out m'} (rs : Regs w R)
    (hp : rs ∘ A.words hk = pub) (hs : rs A.site = site)
    (he : Flow.Exec pub site a (rs ∘ A.regs hn) m es out m') :
    ∃ rs', Flow.Exec data state (code (A.regs hn) (A.words hk) A.site a) rs m es rs' m' ∧
      rs' ∘ A.regs hn = out ∧ ∀ j, j ∉ Set.range A.scratch → rs' j = rs j := by
  obtain ⟨rs', run, endAt, unchanged⟩ := liftExec (A.regs hn) (A.words hk) A.site
    (fun i => A.regs_outside hn (A.bankOutside (i.castLE hk))) (A.regs_outside hn A.siteOutside)
    data he rs rfl hp hs
  exact ⟨rs', run, endAt, fun j hj => unchanged j (A.regs_outside hn hj)⟩

open private events ops from OAI.Computability.VPVNP.PairTraversalLeafWorker

/-- The two header writes in chronological order, with their private ticks. -/
def leafEvents (node : Word w) : List (Event w) := events node

/-- The linked leaf body accepts arbitrary scratch contents and uses the
runtime base and stride. Its successor is in scratch register zero. -/
theorem leaf_exec (data : Fin 11 → Word w) (state : Word w) (rs : Regs w R)
    (m : Memory w) (cap base i : ℕ)
    (hp : rs ∘ A.words (by decide) = LeafWorker.directory w cap base)
    (hs : rs A.site = (i : Word w)) :
    let n : Word w := (address cap base i : Word w)
    ∃ out, Flow.Exec data state A.leaf rs m (leafEvents n) out
        (writeMemory (writeMemory m n (n + 2)) (n + 1) 0) ∧
      out (A.scratch 0) = ((i + 1 : ℕ) : Word w) ∧
      countProbes (leafEvents n) = 2 ∧ (leafEvents n).length = 13 ∧
      choiceBits (leafEvents n) = [] ∧ ∀ j, j ∉ Set.range A.scratch → out j = rs j := by
  intro n
  have body : ∃ out, Flow.Exec (LeafWorker.directory w cap base) (i : Word w)
      LeafWorker.program (rs ∘ A.regs (by decide)) m (leafEvents n) out
      (writeMemory (writeMemory m n (n + 2)) (n + 1) 0) ∧
      out 0 = ((i + 1 : ℕ) : Word w) := by
    simp only [LeafWorker.program, Admin.exec_lines_iff_trace]
    simp (config := { decide := true }) [ops, trace, Op.effect, BinaryOp.eval, Function.update,
      LeafWorker.directory, address, n, Nat.cast_add, Nat.cast_mul, leafEvents, events]
  obtain ⟨small, he, ret⟩ := body
  obtain ⟨out, run, hregs, ho⟩ := A.small_lift (by decide) (by decide) data rs hp hs he
  exact ⟨out, run, (congrFun hregs 0).trans ret, rfl, rfl, rfl, ho⟩

/-- The tag worker writes the computed role address and advances scratch
register zero. The preloaded tag can vary between sites. -/
theorem role_exec (data : Fin 11 → Word w) (state site : Word w) (rs : Regs w R)
    (m : Memory w) (pub : Fin 4 → Word w) (hp : rs ∘ A.words (by decide) = pub)
    (hs : rs A.site = site) :
    let es := TraversalRoles.Native.events pub site
    ∃ out, Flow.Exec data state A.role rs m es out (after m es) ∧
      out (A.scratch 0) = site + 1 ∧ countProbes es = 1 ∧ es.length = 11 ∧
      choiceBits es = [] ∧ ∀ j, j ∉ Set.range A.scratch → out j = rs j := by
  intro es
  have body : ∃ out, Flow.Exec pub site (lines TraversalRoles.Native.visit (by decide))
      (rs ∘ A.regs (by decide)) m es out (after m es) ∧ out 0 = site + 1 := by
    simp only [Admin.exec_lines_iff_trace]
    simp (config := { decide := true }) [TraversalRoles.Native.visit, TraversalRoles.Native.events,
      es, trace, Op.effect, BinaryOp.eval, Function.update, after, BurstRAM.update]
  obtain ⟨small, he, ret⟩ := body
  obtain ⟨out, run, hregs, ho⟩ := A.small_lift (by decide) (by decide) data rs hp hs he
  exact ⟨out, run, (congrFun hregs 0).trans ret, rfl, rfl, rfl, ho⟩

open private worker_exec headerMemory from OAI.Computability.VPVNP.PairTraversalSiteWorker

/-- Translate the complete current placement fiber. The node headers cost
three probes and every child contributes one read and one write. -/
theorem fiber_exec (data : Fin 11 → Word w) (state site : Word w) (rs : Regs w R)
    (m : Memory w) (pub : Fin 6 → Word w) (hp : rs ∘ A.bank = pub) (hsite : rs A.site = site)
    (src node count : ℕ) (hs : SiteWorker.source pub site = (src : Word w))
    (hn : SiteWorker.node pub site = (node : Word w))
    (hc : (m (SiteWorker.counter pub site).val).val = count)
    (before : src + count ≤ node) (fit : node + 2 + count < 2 ^ w) :
    let image := DescriptorRows.passMemory m node src (node + 2) (SiteWorker.counter pub site)
      (pub 3) (pub 5) count
    ∃ es out, Flow.Exec data state A.fiber rs m es out image ∧ out (A.scratch 6) = site + 1 ∧
      countProbes es = 2 * count + 3 ∧ es.length = 7 * count + 24 ∧ choiceBits es = [] ∧
      ∀ j, j ∉ Set.range A.scratch → out j = rs j := by
  intro image
  obtain ⟨es, small, body, ret, probes, steps, bits⟩ := worker_exec pub site m src node count
    hs hn hc before fit (rs ∘ A.scratch)
  obtain ⟨out, run, hregs, ho⟩ := liftExec A.scratch A.bank A.site A.bankOutside A.siteOutside data
    body rs rfl hp hsite (state := state)
  refine ⟨es, out, ?_, (congrFun hregs 6).trans ret, probes, steps, bits, ho⟩
  have hi : DescriptorRows.rowMemory src (node + 2) count (pub 3) (pub 5)
      (headerMemory pub site m) = image := by
    change DescriptorRows.rowMemory _ _ _ _ _ (writeMemory (writeMemory m (SiteWorker.node pub site)
      (SiteWorker.node pub site + 2)) (SiteWorker.node pub site + 1)
      (m (SiteWorker.counter pub site).val)) = image
    rw [hn]
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, image] using
      DescriptorRows.headers_then_scan m node src (SiteWorker.counter pub site) (pub 3) (pub 5)
        count before fit
  rw [← hi]
  exact run

end Allocation

/-- Compile the worker followed by the caller's continuation in one instruction
table. The continuation receives exactly the worker's final registers, external
memory, unused fuel and unused choice bits. -/
theorem execute_then (body tail : Flow R 11) (ret : Option (Fin R))
    (pub : Fin 11 → Word w) (state : Word w) (priv : Word w → Word w) {rs m es out m'}
    (run : Flow.Exec pub state body rs m es out m') (bits : List Bool) (fuel : ℕ) :
    let whole := body.seq tail
    let M := (whole.template ret).instantiate w pub
    execute M.program (es.length + fuel) ⟨M.entry, state, rs, priv⟩ m (choiceBits es ++ bits) =
      (execute M.program fuel ⟨whole.pc (.inr tail.entry), state, out, priv⟩ m' bits).map
        (Flow.prependEvents es) := by
  let whole := body.seq tail
  let M := (whole.template ret).instantiate w pub
  have linked := (Flow.template_linked whole ret pub).seqLeft
  have reject : M.code whole.rejectPC = .reject := by
    simp [M, Template.instantiate, Flow.template_reject, Instr.resize]
  exact run.execute linked reject priv fuel bits

end PairSimulation.TraversalRows.OnlineWorker

end VPVNP
end Computability
end OAI
