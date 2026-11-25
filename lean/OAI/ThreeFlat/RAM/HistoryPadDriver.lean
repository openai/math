import OAI.ThreeFlat.RAM.HistoryPadScan
import OAI.ThreeFlat.RAM.ExpressionScan

namespace OAI
/-! # A native variable-length sweep for fixed-shape metadata padding -/

namespace ThreeFlat.RAM.HistoryPadDriver

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorScan DescriptorExpr HistoryPadScan Fin.CommRing

variable {w k p r : ℕ}

private def headerTerm (base : Fin k) (j : Word w) : Term w k 1 :=
  (Term.binary .add (.parameter base) (.literal j)).load

/-- The four header words are the absolute start of padding, forced row count, first hidden
bit address and forced-zero table ID. They are read anew from the selected slot. -/
def term (base : Fin k) : Term w k 1 := padTailWord.instantiate
  ![Term.binary .sub (.result 0) (headerTerm base 0), headerTerm base 1,
    headerTerm base 2, headerTerm base 3]

set_option maxRecDepth 4096 in
theorem term_binds (base : Fin k) : (term (w:=w) base).binds = 29 := by
  simp only [term,Term.binds_instantiate,binds_padTailWord,Fin.sum_univ_succ]
  rfl

def header (base : Word w) (m : Memory w) (j : Fin 4) : Word w :=
  m (base + (j.val : Word w)).val

theorem term_eval (base : Fin k) (params : Fin k → Word w) (m : Memory w)
    (vs : Fin 1 → Word w) :
    (term base).eval params m vs = padWord (vs 0 - header (params base) m 0)
      (header (params base) m 1) (header (params base) m 2) (header (params base) m 3) := by
  rw [term,Term.eval_instantiate,eval_padTailWord]
  simp [headerTerm,header,BinaryOp.eval,Term.eval]

def word (lo : ℕ) (force first tag : Word w) (a : ℕ) :=
  padWord ((a : Word w)-(lo : Word w)) force first tag

/-- With a header outside the output segment, the installed descriptor and loop
write exactly n words at their absolute destination, including for an empty suffix. -/
theorem generate_padding (M : Machine w p r k) (reg : Fin 4 ↪ Fin r) (L : Labels p)
    (loop : Installed M reg L) (base : Fin k) (loc : Fin (term (w:=w) base).labels → Fin p)
    (tmp : Fin (term (w:=w) base).binds ↪ Fin r) (fresh : ∀ i j, reg i ≠ tmp j)
    (entry : loc (term (w:=w) base).first = L.describe)
    (rom : ∀ i, M.code (loc i) = (term (w:=w) base).emit loc (fun _ => reg 0) tmp (reg 2) L.store i)
    (lo n : ℕ) (force first tag : Word w) (c : Config w p r) (input : Memory w)
    (control : ∀ j : Fin 4, header (M.publicData base) input j = ![(lo : Word w),force,first,tag] j)
    (separate : ∀ j : Fin 4, let a := (M.publicData base+(j.val : Word w)).val; a < lo ∨ lo+n ≤ a)
    (atGuard : c.pc = L.guard) (start : (c.reg (reg 0)).val = lo)
    (stop : (c.reg (reg 1)).val = lo+n) (unit : c.reg (reg 3) = 1) :
    ∃ steps ≤ 1+62*n, ∃ out : Config w p r, out.pc = L.exit ∧
      advance M.program steps c input = some (out, fillSegment lo n (word lo force first tag) input) := by
  let e := term (w:=w) base
  let valid := scanInvariant (p:=p) reg lo (lo+n) input
  have desc : Describes M reg L e.steps (word lo force first tag) valid := by
    apply describes_expression M reg L e loc tmp fresh entry rom lo (lo+n) input (word lo force first tag)
    intro a m _ _ h
    have same (j : Fin 4) : header (M.publicData base) m j = ![(lo : Word w),force,first,tag] j :=
      (h _ (separate j)).trans (control j)
    change (term base).eval M.publicData m (fun _ => a) = word lo force first tag a.val
    rw [term_eval, same 0, same 1, same 2, same 3]
    simp [word]
  have ok : valid c input := ⟨unit,start.ge,stop,fun _ _ => rfl⟩
  obtain ⟨steps,bound,out,hpc,run⟩ := generate M reg L loop _ _ valid desc n c input atGuard ok
    (by rw [start,stop])
  refine ⟨steps,?_,out,hpc,?_⟩
  · simpa [e,Term.steps_eq,term_binds,Nat.mul_comm] using bound
  · simpa [start] using run

end ThreeFlat.RAM.HistoryPadDriver

end OAI
