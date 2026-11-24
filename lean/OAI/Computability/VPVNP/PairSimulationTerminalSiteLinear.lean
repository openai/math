import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-! # Straight-line rows for initializing a final site's private DFS stack -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalSiteStart

open BurstRAM PrivateRAM
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-- Logical registers for the terminal-site entry code, partitioned into nine DFS slots, eleven
saved bootstrap slots and three working slots. -/
abbrev Reg := Fin 9 ⊕ (Fin 11 ⊕ Fin 3)

/-- Selects a DFS register in the site-entry bank. The bootstrap uses this bank to set the
stack top and end for the pending root visit. -/
abbrev dfs (i : Fin 9) : Reg := .inl i
/-- Selects a bootstrap register holding values needed by later stages, including the site
ordinal, root descriptor and endpoint table addresses. -/
abbrev saved (i : Fin 11) : Reg := .inr (.inl i)
/-- Selects one of the three working registers available for intermediate site-entry
calculations such as header offsets and the root row address. -/
abbrev work (i : Fin 3) : Reg := .inr (.inr i)

/-- One straight-line operation on the symbolic site-entry registers. Operations include public
and state inputs, word arithmetic, external reads and private loads or stores. -/
inductive Line where
  | lit (dst : Reg) (value : Fin 32)
  | pub (dst : Reg) (i : Fin 11)
  | state (dst : Reg)
  | copy (dst src : Reg)
  | bin (op : BinaryOp) (dst lhs rhs : Reg)
  | read (dst addr : Reg)
  | load (dst addr : Reg)
  | store (addr src : Reg)

variable {w p r k : ℕ}

/-- Translates one symbolic line to a native RAM instruction using the supplied physical
registers, public ports and successor label. -/
def Line.emit (reg : Reg → Fin r) (pub : Fin 11 → Fin k) (next : Fin p) : Line → Instr w p r k
  | .lit i n => .constant (reg i) (n.val : Word w) next
  | .pub i j => .publicWord (reg i) (pub j) next
  | .state i => .stateWord (reg i) next
  | .copy i j => .copy (reg i) (reg j) next
  | .bin op i x y => .binary op (reg i) (reg x) (reg y) next
  | .read i a => .readExternal (reg i) (reg a) next
  | .load i a => .loadPrivate (reg i) (reg a) next
  | .store a i => .storePrivate (reg a) (reg i) next

theorem Line.resize_emit (reg : Reg → Fin r) (pub : Fin 11 → Fin k) (next : Fin p) (l : Line) :
    (Line.emit (w := 5) reg pub next l).resize w = Line.emit reg pub next l := by
  cases l <;> try rfl
  rename_i n
  change Instr.constant _ (Fin.ofNat _ (n.val % 32)) _ = Instr.constant _ (n.val : Word w) _
  rw [Nat.mod_eq_of_lt n.isLt]; rfl

/-- Evaluate a straight-line fragment with the same address reads and private stores as the RAM. -/
def eval (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) :
    List Line → (Reg → Word w) → (Word w → Word w) → List (Event w) × (Reg → Word w) × (Word w → Word w)
  | [], b, priv => ([], b, priv)
  | op :: ops, b, priv =>
    let (e, bank, mem) := match op with
      | .lit i n => (Event.tick, Function.update b i (n.val : Word w), priv)
      | .pub i j => (.tick, Function.update b i (pub j), priv)
      | .state i => (.tick, Function.update b i st, priv)
      | .copy i j => (.tick, Function.update b i (b j), priv)
      | .bin f i x y => (.tick, Function.update b i (f.eval (b x) (b y)), priv)
      | .read i a => (.read (b a) (m (b a).val), Function.update b i (m (b a).val), priv)
      | .load i a => (.tick, Function.update b i (priv (b a)), priv)
      | .store a i => (.tick, b, Function.update priv (b a) (b i))
    let (es, out, mem') := eval pub st m ops bank mem
    (e :: es, out, mem')

private theorem update_comp (reg : Reg ↪ Fin r) (b : Fin r → Word w) (i : Reg) (v : Word w) :
    Function.update b (reg i) v ∘ reg = Function.update (b ∘ reg) i v := by
  funext j
  by_cases h : j = i <;> simp [Function.comp_apply, h]

/-- Execute the emitted rows at arbitrary labels, leaving the live bank and
private memory computed by `eval`. -/
private theorem linear_walk (M : Machine w p r k) (reg : Reg ↪ Fin r) (pub : Fin 11 → Fin k) (m : Memory w)
    (ls : List Line) (pc : Fin (ls.length+1) → Fin p)
    (hl : ∀ i : Fin ls.length, M.code (pc i.castSucc) = Line.emit reg pub (pc i.succ) ls[i])
    (c : Config w p r) (hc : c.pc = pc 0) :
    let v := eval (M.publicData ∘ pub) c.persistent m ls (c.reg ∘ reg) c.privateMem
    ∃ out, out.pc = pc (Fin.last ls.length) ∧ out.persistent = c.persistent ∧
      out.reg ∘ reg = v.2.1 ∧ out.privateMem = v.2.2 ∧
      (∀ j, (∀ i, reg i ≠ j) → out.reg j = c.reg j) ∧ ReadPrefix M m c v.1 out := by
  induction ls generalizing c with
  | nil => exact ⟨c, hc, rfl, rfl, rfl, fun _ _ => rfl, ReadPrefix.nil _⟩
  | cons op ops ih =>
    let next := pc (Fin.succ 0)
    have row := hl 0
    change M.code (pc 0) = Line.emit reg pub next op at row
    have hs : M.program.step c = (Line.emit reg pub next op).run M.publicData c := by
      simp only [Machine.program, hc, row]
    have tail (mid : Config w p r) (hn : mid.pc = next) :=
      ih (fun i => pc i.succ) (fun i => hl i.succ) mid hn
    cases op
    case store a i =>
      let mid := c.store next (c.reg (reg a)) (c.reg (reg i))
      obtain ⟨out, hpc, hp, hr, hm, hf, h⟩ := tail mid rfl
      exact ⟨out,hpc,hp,hr,hm,hf,ReadPrefix.tick hs h⟩
    case read i a =>
      let mid := c.put next (reg i) (m (c.reg (reg a)).val)
      obtain ⟨out, hpc, hp, hr, hm, hf, h⟩ := tail mid rfl
      refine ⟨out,hpc,hp,?_,?_,?_,?_⟩
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using hr
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using hm
      · intro j hj
        exact (hf j hj).trans (Function.update_of_ne (hj i).symm ..)
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using ReadPrefix.read (c.reg (reg a)) hs h
    case' lit i n => let mid := c.put next (reg i) (n.val : Word w)
    case' pub i j => let mid := c.put next (reg i) (M.publicData (pub j))
    case' state i => let mid := c.put next (reg i) c.persistent
    case' copy i j => let mid := c.put next (reg i) (c.reg (reg j))
    case' load i a => let mid := c.put next (reg i) (c.privateMem (c.reg (reg a)))
    case' bin f i x y => let mid := c.put next (reg i) (f.eval (c.reg (reg x)) (c.reg (reg y)))
    all_goals
      have step : M.program.step c = .localStep mid := hs
      obtain ⟨out,hpc,hp,hr,hm,hf,h⟩ := tail mid rfl
      refine ⟨out,hpc,hp,?_,?_,?_,?_⟩
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using hr
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using hm
      · intro j hj
        exact (hf j hj).trans (Function.update_of_ne (hj i).symm ..)
      · simpa only [mid, Config.put, update_comp, eval, Function.comp_apply] using ReadPrefix.tick step h

theorem linear_run_framed (M : Machine w p r k) (reg : Reg ↪ Fin r) (pub : Fin 11 → Fin k) (m : Memory w)
    (ls : List Line) (pc : Fin (ls.length+1) → Fin p)
    (hl : ∀ i : Fin ls.length, M.code (pc i.castSucc) = Line.emit reg pub (pc i.succ) ls[i])
    (c : Config w p r) (hc : c.pc = pc 0) :
    let v := eval (M.publicData ∘ pub) c.persistent m ls (c.reg ∘ reg) c.privateMem
    ∃ out, out.pc = pc (Fin.last ls.length) ∧ out.persistent = c.persistent ∧
      out.reg ∘ reg = v.2.1 ∧ out.privateMem = v.2.2 ∧
      (∀ j, (∀ i, reg i ≠ j) → out.reg j = c.reg j) ∧ ∀ fuel bs,
      execute M.program (fuel+v.1.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep => ⟨v.1 ++ rep.events, rep.result⟩) := by
  obtain ⟨out, hp, hst, hr, hm, hf, h⟩ := linear_walk M reg pub m ls pc hl c hc
  exact ⟨out,hp,hst,hr,hm,hf,ReadPrefix.execute h⟩

theorem linear_run (M : Machine w p r k) (reg : Reg ↪ Fin r) (pub : Fin 11 → Fin k) (m : Memory w)
    (ls : List Line) (pc : Fin (ls.length+1) → Fin p)
    (hl : ∀ i : Fin ls.length, M.code (pc i.castSucc) = Line.emit reg pub (pc i.succ) ls[i])
    (c : Config w p r) (hc : c.pc = pc 0) :
    let v := eval (M.publicData ∘ pub) c.persistent m ls (c.reg ∘ reg) c.privateMem
    ∃ out, out.pc = pc (Fin.last ls.length) ∧ out.persistent = c.persistent ∧
      out.reg ∘ reg = v.2.1 ∧ out.privateMem = v.2.2 ∧ ∀ fuel bs,
      execute M.program (fuel+v.1.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep => ⟨v.1 ++ rep.events, rep.result⟩) := by
  obtain ⟨out, hp, hst, hr, hm, _, h⟩ := linear_walk M reg pub m ls pc hl c hc
  exact ⟨out,hp,hst,hr,hm,ReadPrefix.execute h⟩

end PairSimulation.TerminalSiteStart

end VPVNP
end Computability
end OAI
