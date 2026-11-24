import OAI.Computability.VPVNP.PairShrinkRoleChild
import OAI.Computability.VPVNP.PairNodeChildSegment

/-!
# The child decoder in the hosted shrinking segment

Before the descriptor header, the hosted program fills its slot-ordinal bank.
The initializer contributes one tick per ordinal and carries all argument
buffers, the protected DFS stack and the full remaining tape into the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.BankChild

open BurstRAM BurstRAM.PrivateRAM DFS Compression CompressorRecords NodeArguments
open NodeArguments.ChildScan
open scoped Fin.CommRing

variable {a g w p r k endAddr : ℕ} {X : State a g}
  {M : Machine w p r k} {m : Memory w} {dfs : Fin 9 ↪ Fin r}

theorem initializer_realizes {pc : Fin (2 ^ a) → Fin p} {bank : Fin (2 ^ a) ↪ Fin r}
    {done : Fin p} (init : ChildBankInit.Linked M pc bank done)
    (apart : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ∉ Set.range bank)
    {pre post : Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = pc 0)
    (finish : ∀ node c d, pre node c → d.pc = done →
      (ChildSlots.Names.bank bank).Valid M d → d.persistent = c.persistent →
      d.privateMem = c.privateMem → (∀ i, i ∉ Set.range bank → d.reg i = c.reg i) → post node d) :
    Realizes (endAddr := endAddr) (Setup.ticks (2 ^ a)).reader M m dfs pre (fun _ => post) := by
  apply Setup.realizes
  intro node c h
  obtain ⟨d, pc, state, mem, ready, keep, run⟩ := ChildBankInit.native init m c (start node c h)
  exact ⟨d, finish node c d h pc ready state mem keep,
    ⟨fun i hi => keep _ (apart i hi), fun i _ => congrFun mem i, state⟩, congrArg _ mem, run⟩

variable (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
  (desc : Word w → ChildArguments.Descriptor w X)

/-- Run the fixed child-register setup ticks, then decode the placed old-site arguments from
the selected child directory and choice tape. -/
noncomputable def reader : Reader w endAddr (List (Child X)) :=
  ShrinkRole.bind (Setup.ticks (2 ^ a)).reader fun _ => ChildArguments.reader A T m older cap desc

theorem splitBits : Splits (endAddr := endAddr) (reader A T m older cap desc) :=
  (Setup.ticks (2 ^ a)).splits.bind fun _ _ _ _ _ _ h =>
    ChildArguments.splitBits A T m older cap desc h

open ChildCode.RegisterBank (segment initPC bank loc regs)

variable {A T m older cap desc}

/-- Native realization from the first instruction of the installed eleven-operand
segment. A successful scan stores the decoded packets in order and preserves every
register outside the segment's local allocation. -/
theorem realizes {M : Machine w p r 11} {dfs : Fin 9 ↪ Fin r}
    (pc : Fin (segment a).count → Fin p) (saved : VertexImage.Saved ↪ Fin r)
    (prv : Fin (segment a).privateRegs ↪ Fin r) (ret : Fin p)
    (rows : ∀ j, M.code (pc j) = ((segment a).row pc dfs saved prv ret j).resize w)
    (apart : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → ∀ j, dfs i ≠ prv j)
    (rep : T.ActualColumns X m) (strideFit : cap + 2 < 2 ^ w)
    {pre : Word w → Config w p r → Prop} {post : List (Child X) → Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c →
      c.pc = pc (segment a).entry ∧ c.reg (regs prv 7) = node ∧
      c.reg (regs prv 8) = (desc node).directoryBase ∧
      ChildArguments.Resident A T m older cap endAddr node (desc node))
    (finish : ∀ node c d xs, pre node c → xs.map Child.site = (desc node).sites → d.pc = ret →
      d.persistent = c.persistent →
      d.privateMem = storePackets A (xs.map (Child.packet X older cap)) c.privateMem →
      (∀ i, i ∉ Set.range prv → d.reg i = c.reg i) → post xs node d) :
    Realizes (endAddr := endAddr) (reader A T m older cap desc) M m dfs pre post := by
  obtain ⟨init, code⟩ := ChildCode.RegisterBank.segment_linked M pc dfs saved prv ret rows
  obtain ⟨hh, hl⟩ := ChildCode.linkedWith M (loc pc) (regs prv) (.bank (bank prv)) ret code
  let header := ChildCode.headerPC (loc pc)
  let input := ChildArguments.Entry A T m older cap desc header (regs prv) M
    (.bank (bank prv)) endAddr
  let mid (node : Word w) (d : Config w p r) : Prop := input node d ∧
    ∃ c, pre node c ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ i, i ∉ Set.range (bank prv) → d.reg i = c.reg i
  have sep (j : Fin 16) : regs prv j ∉ Set.range (bank prv) := fun ⟨i, he⟩ =>
    ChildCode.RegisterBank.bank_apart prv i j he
  have boot : Realizes (endAddr := endAddr) (Setup.ticks (2 ^ a)).reader M m dfs pre
      (fun _ => mid) := by
    apply initializer_realizes init (fun i hi ⟨j, eqn⟩ => apart i hi _ eqn.symm)
      (fun node c hc => (start node c hc).1)
    intro node c d hc hd names state mem keep
    obtain ⟨_, parent, directory, resident⟩ := start node c hc
    exact ⟨⟨hd, (keep _ (sep 7)).trans parent, (keep _ (sep 8)).trans directory, names, resident⟩,
      c, hc, mem, state, keep⟩
  apply boot.bind
  intro _
  apply ChildArguments.realizesWith hh hl (ChildCode.RegisterBank.bank_apart prv) rep strideFit
    (fun i hi j => apart i hi _) (fun _ _ h => h.1)
  intro node d z xs h sites done state mem keep
  obtain ⟨_, c, hc, dm, ds, before⟩ := h
  refine finish node c z xs hc sites done (state.trans ds) (dm ▸ mem) ?_
  intro i hi
  have free (j : Fin 16) : i ≠ regs prv j := fun e => hi ⟨_, e.symm⟩
  exact (keep _ (fun j _ => free j) (by simp [mutableRegs, free])).trans
    (before i fun ⟨j, eqn⟩ => hi ⟨_, eqn⟩)

end PairSimulation.ShrinkRole.BankChild

end VPVNP
end Computability
end OAI
