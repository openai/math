import OAI.Computability.VPVNP.PairSimulationLeafImagePreparation
import OAI.Computability.VPVNP.PairSimulationLeafReadback
import OAI.Computability.VPVNP.PairSimulationLeafArena

/-! # Exact cursor-leaf role of the bounded terminal-site simulator -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafVisit

open BurstRAM PrivateRAM CursorNetwork CursorRouting LeafHandler LeafStartup DFS
open Filter
open scoped Fin.CommRing

set_option synthInstance.maxSize 10000

variable {w p r k : ℕ} {A : PrimedInputRAM.Lengths} {n a H s : ℕ}
  {Q : PrimedInputRAM.Layout A n a H w} (D : PrimedCounter.Data Q s)
  {b l e degree pad endAddr : ℕ} [NeZero (b+l)] (hD : 1 < b+l) (hd : 2+pad=2^degree)
  (budget : ProcessorBudget n (b+l) e w) (R : LeafArena.Regions) (cap : ℕ)
  (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)

variable {M : Machine w p r k} (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r)
    (pub : LeafImage.Pub → Fin k) (ret : Fin p) (m : Memory w)

/-- The DFS leaf parser for the concrete instruction image, using its public address fields,
physical argument buffers, stack layout, and interpreter clock. -/
noncomputable def leafParser (clock : ℕ) : HookParser w endAddr :=
  parser D budget.tags budget.capFits (storage R fit)
    (loaded D budget R fit (fields (M := M) pub) m) clock

/-- The finite table implements the entire cursor factor at each genuine
leaf with the parent's supplied half-wires. The header, routing, private
input banks and accepting choice interpreter all belong to its execution. -/
theorem image_exact (clock : ℕ) (link : LeafImage.Linked pc reg pub ret M)
    (op : LeafFront.Operands (LeafImage.front pc reg pub ret) M m D R b l cap)
    (hsize : M.publicData (pub .size) = (n : Word w)) (lo : endAddr ≤ R.arguments.start)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ clock)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length + clock ≤ n^40) :
    (leafParser (endAddr := endAddr) (M := M) D budget R fit pub m clock).ExactOn
      (Domain (e := e) D hD hd R cap (fields (M := M) pub)) M (pc (.address 0)) ret (LeafImage.dfsReg reg) m := by
  have sourceRoom (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j :=
    (Nat.le_add_right _ clock).trans (room v buf j)
  have prep := preparation D hD hd budget R cap fit pc reg pub ret m link op hsize lo sourceRoom
  exact parser_exactOn D budget.tags budget.capFits (storage R fit) _ clock prep link.stack
    (by have := budget.tags; omega) (LeafImage.dfs_ne_stack reg)
    (R.stack_above_dfs _ _ fit lo) (fun _ _ _ => time _ _) (fun _ _ _ => room _ _)

/-- The source clock and stack space in the exactness theorem hold
eventually with the actual auxiliary machine's private cutoff. -/
theorem eventually_resources :
    ∀ᶠ n : ℕ in atTop, ∀ d e w [NeZero d] (budget : ProcessorBudget n d e w)
      (A : PrimedInputRAM.Lengths) (a H s : ℕ) (Q : PrimedInputRAM.Layout A n a H w) (D : PrimedCounter.Data Q s),
      D.fuel ≤ n^10 → ∀ (v : Position d) (buf : Buffers d (2^e) w),
      steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ n^39 ∧
        ∀ j, (auxiliaryBank D budget.tags budget.capFits v buf j).length+n^39 ≤ n^40 := by
  filter_upwards [eventually_steps 52, eventually_ge_atTop 128] with n bound hn
  intro d e w _ budget A a H s Q D hf v buf
  let x := auxiliary D budget.tags budget.capFits v buf
  refine ⟨bound d e w x budget hf,fun j => ?_⟩
  have h₁ := bank_length_le x 52 hn budget hf D.pub j
  have h₂ := Nat.pow_le_pow_right (by omega : 1 ≤ n) (by decide : 12 ≤ 39)
  have h₃ : 2*n^39 ≤ n^40 := by rw [pow_succ' n 39]; exact Nat.mul_le_mul_right _ (by omega)
  change (bank 52 x D.pub j).length+n^39 ≤ n^40
  omega

end PairSimulation.LeafVisit

end VPVNP
end Computability
end OAI
