import OAI.Computability.VPVNP.PairSimulationMapDriver

/-!
# Register preservation across all selected row calls

The controller can carry an arbitrary collection of exterior registers
through dispatch, the selected row and the label store. A later width check
or histogram flush may therefore use operands prepared before the copy loop.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapDriver.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {S : Type*} {w p r k u : ℕ} (P : MapDriver.Program S p r k)

/-- All the saved registers retain their initial words. -/
def Saved (save : Fin r → Prop) (initial c : Config w p r) : Prop :=
  ∀ j, save j → c.reg j = initial.reg j

/-- The four registers modified by the driver's own instructions are excluded.
The selected rows supply their own preservation proof. -/
def OutsideWrites (save : Fin r → Prop) : Prop :=
  ∀ j, save j → j ≠ P.reg 0 ∧ j ≠ P.reg 2 ∧ j ≠ P.reg 4 ∧ j ≠ P.reg 5

/-- The row contract with a register frame carried from an arbitrary initial state. -/
def FramedRows (M : Machine w p r k) (θ : Fin u → S) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (cap : ℕ) (save : Fin r → Prop) : Prop :=
  ∀ initial, P.RowRuns M θ labelWord (fun n c ↦ inv n c ∧ Saved save initial c) cap

/-- Exact row calls preserving a chosen exterior register set. -/
def FramedRowsWith (θ : Fin u → S) (rowSteps : Fin u → ℕ) (M : Machine w p r k)
    (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (cap : ℕ) (save : Fin r → Prop) : Prop :=
  ∀ initial, P.RowRunsWith M θ labelWord (fun n c ↦ inv n c ∧ Saved save initial c) cap
    (fun i n ↦ n = rowSteps i)

theorem FramedRowsWith.forget {M : Machine w p r k} {θ : Fin u → S} {steps : Fin u → ℕ}
    {labelWord : Fin u → Word w} {inv : ℕ → Config w p r → Prop} {cap : ℕ} {save : Fin r → Prop}
    (h : P.FramedRowsWith θ steps M labelWord inv cap save) :
    P.FramedRows M θ labelWord inv cap save := by
  intro initial i c pc ready
  obtain ⟨n, out, bound, _, path⟩ := h initial i c pc ready
  exact ⟨n, out, bound, path⟩

theorem FramedRows.forget {M : Machine w p r k} {θ : Fin u → S}
    {labelWord : Fin u → Word w} {inv : ℕ → Config w p r → Prop} {cap : ℕ}
    {save : Fin r → Prop} (rows : P.FramedRows M θ labelWord inv cap save) :
    P.RowRuns M θ labelWord inv cap := by
  intro i c hc hi
  obtain ⟨n, d, bound, pre, pc, label, hr, controls, mem, per⟩ :=
    rows c i c hc ⟨hi, fun _ _ ↦ rfl⟩
  exact ⟨n, d, bound, pre, pc, label, hr.1, controls, mem, per⟩

private theorem stable_saved {inv : ℕ → Config w p r → Prop} {dest u : ℕ}
    {save : Fin r → Prop} (stable : P.Stable inv dest u) (keep : P.OutsideWrites save)
    (initial : Config w p r) :
    P.Stable (fun n c ↦ inv n c ∧ Saved save initial c) dest u := by
  intro n c d h regs mem per
  refine ⟨stable n c d h.1 regs mem per, fun j hj ↦ ?_⟩
  obtain ⟨h0, h2, h4, h5⟩ := keep j hj
  exact (regs j h0 h2 h4 h5).trans (h.2 j hj)

/-- Both the complete label slice and all exterior operands are available
on entry to the linked final-width checker. -/
theorem native_framed {M : Machine w p r k} (link : P.Linked M)
    (inj : Function.Injective (M.publicData ∘ P.port))
    (θ : Fin u → S) (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)
    (save : Fin r → Prop) (keep : P.OutsideWrites save)
    (rows : P.FramedRows M θ labelWord inv cap save) (hs : src + u < 2 ^ w)
    (hd : dest + u < 2 ^ w) (sep : src + u ≤ dest ∨ dest + u ≤ src)
    (c : Config w p r) (ready : P.Ready M θ labelWord src dest 0 c) (h0 : inv 0 c) :
    ∃ ticks d, ticks ≤ P.visitCap cap * u + 1 ∧ Prefix M c (List.replicate ticks .tick) d ∧
      d.pc = P.checkWidths ∧ inv u d ∧ Saved save c d ∧
      (∀ i : Fin u, d.privateMem ((dest + i.val : ℕ) : Word w) = labelWord i) ∧
      (∀ a : Word w, a.val < dest ∨ dest + u ≤ a.val → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  obtain ⟨n, d, budget, pre, pc, hr, labels, mem, per⟩ :=
    native link inj θ member labelWord (fun i d ↦ inv i d ∧ Saved save c d)
      src dest cap (stable_saved P stable keep c) (rows c) hs hd sep c ready ⟨h0, fun _ _ ↦ rfl⟩
  exact ⟨n, d, budget, pre, pc, hr.1, hr.2, labels, mem, per⟩

end PairSimulation.MapDriver.Program

end VPVNP
end Computability
end OAI
