import OAI.Computability.VPVNP.PairSimulationMapHandlerExact
import OAI.Computability.VPVNP.PairSimulationMapHandlerOperand
import OAI.Computability.VPVNP.PairShrinkRoleStages

/-!
# The physical map handler preserves the DFS stack and role registers

All writable arrays of a prepared map call start above the exclusive end
of the saved stack. Successful visits therefore update only the upper scratch
according to the exact action. Unsuccessful visits execute to a rejecting opcode.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerOperand

open MotifSelector MotifGrid MotifBlocks MotifConversion MapConstants MotifEntry
open BurstRAM BurstRAM.PrivateRAM CompressorRecords.PhaseRecipe MapHandlerImage
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t shared p r w : ℕ}
  (F : MapHandlerImage.Family B t shared) (hp : ∀ i, 0 < p₀ i) (I : LocalHistory.EntryInput B)
  (X : Workspace F hp I (w := w)) (endAddr : ℕ)

/-- Numerical placement of every interval written by the handler. -/
structure Bounds (descriptor : BurstRAM.Word w) : Prop where
  descriptorBase : endAddr ≤ descriptor.val
  selectorBase : endAddr ≤ X.source
  labelBase : endAddr ≤ X.target
  histogramBase : endAddr ≤ X.hist
  directoryBase : endAddr ≤ X.directory.val
  directoryRoom : X.directory.val +
    (MapPortAgreement.ports G I.party (layout F hp I).core.edgeOrder).length ≤ 2 ^ w

variable {F hp I X endAddr}

theorem Bounds.below {descriptor : BurstRAM.Word w} (h : Bounds F hp I X endAddr descriptor)
    (a : BurstRAM.Word w) (ha : a.val < endAddr) :
    a.val < descriptor.val ∧
    MapCallSetup.Outside (layout F hp I).core
      ((layout F hp I).corePC (layout F hp I).locations) X a := by
  refine ⟨ha.trans_le h.descriptorBase, ⟨.inl (ha.trans_le h.selectorBase),
    .inl (ha.trans_le h.labelBase), ?_⟩, ?_⟩
  · intro l eqn
    have val := congrArg Fin.val eqn
    change a.val = (X.hist + l.val) % (2 ^ w) at val
    rw [Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt _).trans_le X.histogramFit)] at val
    exact (ha.trans_le h.histogramBase).not_ge (val ▸ Nat.le_add_right ..)
  · intro i eqn
    have cast : (X.directory.val : BurstRAM.Word w) = X.directory :=
      Fin.ext (Nat.mod_eq_of_lt X.directory.isLt)
    have same : X.directory + (i.val : BurstRAM.Word w) =
        ((X.directory.val + i.val : ℕ) : BurstRAM.Word w) := by rw [Nat.cast_add, cast]
    have val := congrArg Fin.val (eqn.trans same)
    change a.val = (X.directory.val + i.val) % (2 ^ w) at val
    rw [Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le h.directoryRoom)] at val
    exact (ha.trans_le h.directoryBase).not_ge (val ▸ Nat.le_add_right ..)

variable (F hp I) (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (common : Fin shared ↪ Fin r) (c : Config w p r) (m : BurstRAM.Memory w)

/-- Run the exact action on the saved scratch. The caller receives its complete
register banks and the lower stack prefix, alongside the actual histogram readback. -/
theorem Prepared.action_native (pc : F.Address → Fin p) (own : F.PrivateReg ↪ Fin r)
    (advance : Fin p) (M : Machine w p r 11) (installed : ∀ a,
      M.code (pc a) = (F.text pc dfs saved common own advance a).resize w)
    (banks : F.Apart dfs saved common own) (hw : widthThreshold B ≤ w)
    (X : Workspace F hp I) (endAddr : ℕ) (initial : DFS.Scratch w endAddr)
    (incoming : DFS.scratch endAddr c.privateMem = initial) (hpc : c.pc = F.target pc (index hp I))
    (prepared : Prepared F hp I dfs saved common c m X)
    (bounds : Bounds F hp I X endAddr (addr F hp I dfs saved common c m)) :
    let a := addr F hp I dfs saved common c m
    let L := layout F hp I
    match F.action hp I hw (pub F hp I dfs saved common c) (state F hp I dfs saved common c)
      m X endAddr initial with
    | none => ∀ bs, ¬ DFS.Returns M c m bs
    | some (es, updated) => ∃ out, NodeArguments.ChildScan.Prefix M m c out [] es ∧
      out.pc = advance ∧ ShrinkRole.Frame dfs endAddr c out ∧
      (∀ i, out.reg (dfs i) = c.reg (dfs i)) ∧
      (∀ i, out.reg (saved i) = c.reg (saved i)) ∧
      (∀ i, out.reg (common i) = c.reg (common i)) ∧
      (∀ q, q.val < a.val ∨ a.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val →
        MapCallSetup.Outside L.core (L.corePC L.locations) X q →
          out.privateMem q = c.privateMem q) ∧
      (∀ l : Fin t, out.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
        c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) +
        (((names F hp I).getD []).count l : BurstRAM.Word w)) ∧
      DFS.scratch endAddr out.privateMem = updated := by
  dsimp only
  let result := F.action hp I hw (pub F hp I dfs saved common c) (state F hp I dfs saved common c)
    m X endAddr initial
  have run := F.action_native pc dfs saved common own advance M installed banks hp I hw c m X
    endAddr initial incoming hpc prepared.fit prepared.fields prepared.resident prepared.histogram
    prepared.directory
  cases eqn : result with
  | none =>
    dsimp only [result] at eqn
    rw [eqn] at run ⊢
    exact run
  | some pair =>
    obtain ⟨es, updated⟩ := pair
    dsimp only [result] at eqn
    rw [eqn] at run ⊢
    obtain ⟨out, path, exit, per, regs, mem, counts, scratch⟩ := run
    have keep (i) : out.reg (dfs i) = c.reg (dfs i) := regs _ fun _ ↦ (banks.dfs _ i).symm
    have lower (q : BurstRAM.Word w) (hq : q.val < endAddr) : out.privateMem q = c.privateMem q :=
      mem _ (.inl (bounds.below q hq).1) (bounds.below q hq).2
    exact ⟨out, path, exit, ⟨fun i _ ↦ keep i, lower, per⟩, keep,
      fun i ↦ regs _ fun _ ↦ (banks.saved _ i).symm, fun i ↦ regs _ fun _ ↦ (banks.shared _ i).symm,
      mem, counts, scratch⟩

end PairSimulation.MapHandlerOperand

end VPVNP
end Computability
end OAI
