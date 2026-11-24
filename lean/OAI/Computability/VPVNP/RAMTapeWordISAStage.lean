import OAI.Computability.VPVNP.RAMTapeWordISA
import OAI.Computability.VPVNP.RAMTapeWordISAClear

/-!
# Register-level execution of the binary word instructions

The dispatcher stages both operands in separate stacks before executing the
arithmetic kernel. This supports every alias among the two input registers and
the destination. The result is written back, and the finite bank of temporary
stacks is cleared before the instruction returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open TapeWord BurstRAM PrivateRAM

variable {r k w : ℕ} {op : BinaryOp}

/-- Map a local arithmetic stack to its reserved work port in the simulated instruction
machine. -/
def kernelPort (routine : Kernel op) (i : routine.K) : Port r k :=
  .work ((routine.index i).castLE (by decide))

private theorem kernelPort_inj (routine : Kernel op) :
    Function.Injective (kernelPort (r := r) (k := k) routine) := by
  intro i j h
  apply routine.index_injective
  exact Fin.ext (congrArg (Fin.val : Fin 16 → ℕ) (Port.work.inj h))

private theorem kernel_safe (routine : Kernel op) (i : routine.K) :
    copySafe (kernelPort (r := r) (k := k) routine i) := by
  have h := (routine.index i).isLt
  constructor <;> intro he <;> apply Port.work.inj at he <;>
    apply congrArg Fin.val at he <;> change (routine.index i).val = _ at he <;> omega

private theorem reg_safe (i : Fin r) : copySafe (Port.reg i : Port r k) := by simp [copySafe]

/-- Execute the binary opcode's fixed stack program on the designated arithmetic work ports. -/
def arithmeticKernel (op : BinaryOp) : FiniteRoutine (Port r k) :=
  let routine := wordKernel op
  .ofStackCode routine.code (kernelPort routine) routine.entry routine.accepts

/-- All sixteen scratch ports cleared before control returns from the simulated instruction. -/
def workPorts (r k : ℕ) : List (Port r k) := List.ofFn (Port.work : Fin 16 → Port r k)

/-- A finite routine whose entry and control depend only on the opcode and
three register indices. Word width affects only the stack contents. -/
def binary (op : BinaryOp) (dst lhs rhs : Fin r) : FiniteRoutine (Port r k) :=
  let routine := wordKernel op
  let stageL := loadOperand (.reg lhs) (kernelPort routine routine.lhs)
  let stageR := loadOperand (.reg rhs) (kernelPort routine routine.rhs)
  let result := loadOperand (kernelPort routine routine.out) (.reg dst)
  ((((stageL.followedBy stageR).followedBy (arithmeticKernel op)).followedBy result).followedBy
    (clearList (workPorts r k)))

private theorem install_operands (routine : Kernel op) (s : Stacks (Port r k)) (x y : List Bool)
    (h : ∀ i, s (.work i) = []) :
    installStacks (kernelPort routine) s (operandStacks routine.lhs routine.rhs x y) =
      Function.update (Function.update s (kernelPort routine routine.lhs) x)
        (kernelPort routine routine.rhs) y := by
  let p : routine.K → Port r k := kernelPort routine
  have hi : Function.Injective p := kernelPort_inj routine
  change installStacks p s _ = Function.update (Function.update s (p routine.lhs) x) (p routine.rhs) y
  funext j
  by_cases hm : ∃ i, p i = j
  · obtain ⟨i, rfl⟩ := hm
    rw [installStacks_at hi]
    have hpi : s (p i) = [] := h _
    by_cases he : i = routine.lhs
    · subst i
      simp [operandStacks, Function.update_of_ne (hi.ne routine.lhs_ne_rhs)]
    · by_cases hf : i = routine.rhs
      · subst i
        simp [operandStacks, he]
      · simp [operandStacks, he, hf, Function.update_of_ne (hi.ne he), Function.update_of_ne (hi.ne hf), hpi]
  · have hl : j ≠ p routine.lhs := fun he => hm ⟨_, he.symm⟩
    have hr : j ≠ p routine.rhs := fun he => hm ⟨_, he.symm⟩
    rw [installStacks_outside _ _ (not_exists.mp hm), Function.update_of_ne hr, Function.update_of_ne hl]

private theorem clear_result (routine : Kernel op) (final : Stacks routine.K)
    (s : Stacks (Port r k)) (hwork : ∀ i, s (.work i) = []) (dst : Fin r) (value : List Bool) :
    cleared (workPorts r k) (Function.update (installStacks (kernelPort routine) s final) (.reg dst) value) =
      Function.update s (.reg dst) value := by
  funext j
  by_cases hm : j ∈ workPorts r k
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    simp [cleared, hm, hwork]
  · simp only [cleared, hm, ↓reduceIte]
    by_cases he : j = .reg dst
    · subst j
      simp
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      exact installStacks_outside _ _ fun i eq => hm (List.mem_ofFn.mpr ⟨_, eq⟩)

/-- Every binary opcode restores the architectural bank with exactly its
destination register updated. The bound covers staging, arithmetic, writeback
and cleanup of all sixteen work stacks, even for division by zero. -/
theorem binary_runs (op : BinaryOp) (dst lhs rhs : Fin r) (pub : Fin k → Word w)
    (persistent : Word w) (reg : Fin r → Word w) (log : WriteLog w) :
    ∃ t ≤ 100 * (w + 1)^2, (binary op dst lhs rhs).Runs t (bank pub persistent reg log)
      (bank pub persistent (Function.update reg dst (op.eval (reg lhs) (reg rhs))) log) := by
  let routine := wordKernel op
  let p : routine.K → Port r k := kernelPort routine
  have hi : Function.Injective p := kernelPort_inj routine
  have safe : ∀ i, copySafe (p i) := kernel_safe routine
  let s := bank pub persistent reg log
  let a := reg lhs
  let b := reg rhs
  let s₁ := Function.update s (p routine.lhs) (wordBits a)
  let s₂ := Function.update s₁ (p routine.rhs) (wordBits b)
  have h1 : (loadOperand (.reg lhs) (p routine.lhs)).Runs (7*w+3) s s₁ := by
    simpa [s, s₁, p, kernelPort, bank, a] using loadOperand_runs (src := .reg lhs) (dst := p routine.lhs)
      (by simp [p, kernelPort]) (reg_safe _) (safe _) s rfl rfl
  have h₁ : p routine.rhs ≠ p routine.lhs := hi.ne routine.lhs_ne_rhs.symm
  have s14 : s₁ (.work 14) = [] := Function.update_of_ne (safe _).1.symm ..
  have s15 : s₁ (.work 15) = [] := Function.update_of_ne (safe _).2.symm ..
  have h2 : (loadOperand (.reg rhs) (p routine.rhs)).Runs (7*w+3) s₁ s₂ := by
    have hs : s₁ (.reg rhs) = wordBits b := Function.update_of_ne (by simp [p, kernelPort]) ..
    have hd : s₁ (p routine.rhs) = [] := Function.update_of_ne h₁ ..
    simpa only [hs, hd, List.length_nil, Nat.zero_add, length_wordBits] using
      loadOperand_runs (src := .reg rhs) (dst := p routine.rhs) (by simp [p, kernelPort])
        (reg_safe _) (safe _) s₁ s14 s15
  obtain ⟨n, q, final, hn, run, hexit, hout, hbound⟩ := routine.run a b
  let s₃ := installStacks p s final
  have h3 : (arithmeticKernel op).Runs n s₂ s₃ := by
    have hr := FiniteRoutine.runs_ofStackCode hi (normal := routine.accepts) (wordKernel_entry op)
      ((routine.accepts_iff _).mpr hexit) (fun u hu => by rw [(routine.accepts_iff _).mp hu]; rfl) s run
    rw [install_operands routine s _ _ (fun _ => rfl)] at hr
    exact hr
  have hread : s₃ (p routine.out) = wordBits (op.eval a b) :=
    (installStacks_at hi s final _).trans hout
  have hdst : s₃ (.reg dst) = wordBits (reg dst) :=
    installStacks_outside _ _ (by simp [p, kernelPort])
  have h14 : s₃ (.work 14) = [] := installStacks_outside _ _ (fun i => (safe i).1)
  have h15 : s₃ (.work 15) = [] := installStacks_outside _ _ (fun i => (safe i).2)
  let s₄ := Function.update s₃ (.reg dst) (wordBits (op.eval a b))
  have h4 : (loadOperand (p routine.out) (.reg dst)).Runs (8*w+3) s₃ s₄ := by
    have hr := loadOperand_runs (src := p routine.out) (dst := .reg dst) (by simp [p, kernelPort])
      (safe _) (reg_safe _) s₃ h14 h15
    rw [hread, hdst, length_wordBits, length_wordBits] at hr
    convert hr using 1
    omega
  have hspace (j : Port r k) (hj : j ∈ workPorts r k) : (s₄ j).length ≤ w := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    change ((Function.update s₃ (.reg dst) _) (.work i)).length ≤ w
    rw [Function.update_of_ne (by simp)]
    by_cases hm : ∃ u, p u = .work i
    · obtain ⟨u, he⟩ := hm
      rw [← he, show s₃ (p u) = final u from installStacks_at hi ..]
      exact hbound u
    · rw [show s₃ (.work i) = s (.work i) from installStacks_outside _ _ (not_exists.mp hm)]
      exact Nat.zero_le _
  obtain ⟨m, hm, h5⟩ := clearList_runs (workPorts r k) s₄ w hspace
  have htarget : cleared (workPorts r k) s₄ =
      bank pub persistent (Function.update reg dst (op.eval a b)) log :=
    (clear_result routine final s (fun _ => rfl) dst _).trans (bank_updateReg ..)
  rw [htarget] at h5
  have result := (((h1.followedBy h2).followedBy h3).followedBy h4).followedBy h5
  refine ⟨_, ?_, result⟩
  simp only [workPorts, List.length_ofFn] at hm
  ring_nf at hn ⊢
  omega

end RAMTape.ISA

end VPVNP
end Computability
end OAI
