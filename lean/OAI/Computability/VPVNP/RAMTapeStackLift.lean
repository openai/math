import OAI.Computability.VPVNP.RAMTapeStacks

/-!
# Installing a stack routine in a larger machine

Stack labels may be renamed into any disjoint set of ports. Control labels
may name states of the caller. Deterministic executions can be installed even
when a terminal state of the subroutine is used as a continuation by the caller.
Only the installed stacks can change during such an execution.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

variable {K L Q R : Type*}

/-- Relabel the stack and control references of an instruction, preserving its operation and
its halt verdict. -/
@[simp] def StackOp.rename (ports : K → L) (labels : Q → R) : StackOp K Q → StackOp L R
  | .push k b q => .push (ports k) b (labels q)
  | .pop k f => .pop (ports k) (labels ∘ f)
  | .goto q => .goto (labels q)
  | .choose a b => .choose (labels a) (labels b)
  | .halt b => .halt b

/-- A source `halt` can be a return boundary for the linked machine. -/
@[simp] def StackOp.returns : StackOp K Q → Bool
  | .halt _ => true
  | _ => false

/-- Replace the stacks at installed ports and retain the ambient values at all
other labels. The injection hypothesis is used in the restriction theorems. -/
noncomputable def installStacks (ports : K → L) (base : Stacks L) (small : Stacks K) : Stacks L :=
  fun l => open Classical in if h : ∃ k, ports k = l then small h.choose else base l

@[simp] theorem installStacks_at {ports : K → L} (hp : Function.Injective ports)
    (base : Stacks L) (small : Stacks K) (k : K) :
    installStacks ports base small (ports k) = small k := by
  unfold installStacks
  split
  · rename_i h
    rw [hp h.choose_spec]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

theorem installStacks_outside {ports : K → L} (base : Stacks L) (small : Stacks K) {l : L}
    (hl : ∀ k, ports k ≠ l) : installStacks ports base small l = base l := by
  simp [installStacks, not_exists.mpr hl]

theorem installStacks_eq {ports : K → L} (hp : Function.Injective ports) (base : Stacks L)
    (small : Stacks K) (he : ∀ k, base (ports k) = small k) :
    installStacks ports base small = base := by
  funext l
  by_cases hm : ∃ k, ports k = l
  · obtain ⟨k, rfl⟩ := hm
    rw [installStacks_at hp, he]
  · exact installStacks_outside _ _ (not_exists.mp hm)

theorem installStacks_update [DecidableEq K] [DecidableEq L] {ports : K → L}
    (hp : Function.Injective ports) (base : Stacks L) (small : Stacks K) (k : K) (v : List Bool) :
    Function.update (installStacks ports base small) (ports k) v =
      installStacks ports base (Function.update small k v) := by
  funext l
  by_cases hm : ∃ j, ports j = l
  · obtain ⟨j, rfl⟩ := hm
    by_cases hj : j = k
    · subst j
      simp [installStacks_at hp]
    · simp [Function.update_of_ne (fun h => hj (hp h)), Function.update_of_ne hj, installStacks_at hp]
  · have hl := not_exists.mp hm
    rw [Function.update_of_ne (Ne.symm (hl k)), installStacks_outside _ _ hl,
      installStacks_outside _ _ hl]

variable [DecidableEq K] [DecidableEq L]

/-- Lift one deterministic source instruction with exactly the same cost. -/
theorem StackStep.lift {src : StackCode K Q} {target : StackCode L R} {q s q' s'}
    (run : StackStep src q s q' s') (ports : K → L) (hp : Function.Injective ports) (labels : Q → R)
    (base : Stacks L) (hc : ∀ u, (src u).returns = false → target (labels u) = (src u).rename ports labels) :
    StackStep target (labels q) (installStacks ports base s) (labels q') (installStacks ports base s') := by
  cases run with
  | push h =>
    have he := hc q (by simp [h])
    rw [h, StackOp.rename] at he
    simpa only [installStacks_at hp, installStacks_update hp] using
      (StackStep.push (s := installStacks ports base s) he)
  | pop h =>
    have he := hc q (by simp [h])
    rw [h, StackOp.rename] at he
    simpa only [Function.comp_apply, installStacks_at hp, installStacks_update hp] using
      (StackStep.pop (s := installStacks ports base s) he)
  | goto h => exact .goto ((hc _ (by simp [h])).trans (by simp [h]))

/-- Linking preserves each step and each ambient stack outside the routine.
No control equality is required at the final state if it returns. -/
theorem StackRuns.lift {src : StackCode K Q} {target : StackCode L R} {n q s q' s'}
    (run : StackRuns src n q s q' s') (ports : K → L) (hp : Function.Injective ports) (labels : Q → R)
    (base : Stacks L) (hc : ∀ u, (src u).returns = false → target (labels u) = (src u).rename ports labels) :
    StackRuns target n (labels q) (installStacks ports base s) (labels q') (installStacks ports base s') := by
  induction run with
  | nil => exact .nil ..
  | cons hs _ ih => exact .cons (hs.lift ports hp labels base hc) ih

/-- If all rows, including halts and choices, are renamed, the bounded path
counts agree on every installed stack. Control names need only agree on the
states used by the source. -/
theorem stackPaths_lift {src : StackCode K Q} {target : StackCode L R} (ports : K → L)
    (hp : Function.Injective ports) (labels : Q → R) (base : Stacks L)
    (hc : ∀ q, target (labels q) = (src q).rename ports labels) (n : ℕ) (q : Q) (s : Stacks K) :
    stackPaths target n (labels q) (installStacks ports base s) = stackPaths src n q s := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    rw [stackPaths, hc, stackPaths]
    cases src q <;> simp only [StackOp.rename, Function.comp_apply, installStacks_at hp,
      installStacks_update hp, ih]

end RAMTape

end VPVNP
end Computability
end OAI
