import OAI.Computability.BorderVNP.FragmentBucketPrefixSteps
import OAI.Computability.BorderVNP.FragmentBucketLoop

/-! # Executing stable counting-sort header construction in linear work -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Clear and count the histogram, reset the accumulator, then prefix-scan the cells. -/
def prefixProgram : Code := (forEach 10 4 clearStep).seq ((forEach 10 3 countStep).seq
  ((Code.constant 15 0).seq (forEach 10 4 scanStep)))

private theorem reset_preserves {l : Layout} {before z : NatState} (p : l.Preserved before z)
    (pub : Arg → ℕ) {r : Reg} (hr : 8 ≤ r.val) :
    l.Preserved before ((Code.constant r 0).fixedEval pub z) :=
  preserved_fixed p _ _ (by simpa [Code.protects] using hr) (fun _ _ _ => rfl)

private theorem run_clear {l : Layout} {w : ℕ} (fit : l.Fits w)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {before : NatState} (preserved : l.Preserved before (.ofWords s m)) :
    BoundedRun pub mac (forEach 10 4 clearStep) s m (2+l.cells*(clearStep.slots+1)) (fun z =>
      l.Preserved before z ∧ ∀ c : Fin l.cells, z.mem (l.countAddr c.val) = 0) := by
  let I := fun (i : ℕ) (z : NatState) => l.Preserved before z ∧ z.reg 10 = i ∧
    ∀ c : Fin l.cells, c.val < i → z.mem (l.countAddr c.val) = 0
  apply (forEach_run pub mac 10 4 clearStep l.cells clearStep.slots I s m ?_ ?_ ?_).mono le_rfl
  · intro z h
    exact ⟨h.1,fun c => h.2.2 c c.isLt⟩
  · refine ⟨reset_preserves preserved _ (by decide), ?_, fun c hc => by omega⟩
    simp [Code.fixedEval, Code.evalNat]
  · intro i z h
    exact ⟨h.2.1,h.1.ready.2.2.1⟩
  · intro c t mt h
    apply (clearStep_run fit c pub mac t mt h.1 h.2.1).mono le_rfl
    rintro z ⟨p, idx, mem⟩
    refine ⟨p,idx,fun d hd => ?_⟩
    by_cases same : d = c
    · subst d; rw [mem, Function.update_self]
    · have ne : d.val ≠ c.val := fun he => same (Fin.ext he)
      rw [mem, Function.update_of_ne (show l.countAddr d.val ≠ l.countAddr c.val by
        unfold Layout.countAddr; omega)]
      exact h.2.2 d (by omega)

private theorem run_count {l : Layout} {w : ℕ} (fit : l.Fits w)
    (tag : Fin l.rows → Fin l.cells) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {before : NatState}
    (input : ∀ i, before.mem (l.quads+4*i.val) = (tag i).val)
    (preserved : l.Preserved before (.ofWords s m))
    (cleared : ∀ c : Fin l.cells, readings m (l.countAddr c.val) = 0) :
    BoundedRun pub mac (forEach 10 3 countStep) s m (2+l.rows*(countStep.slots+1)) (fun z =>
      l.Preserved before z ∧ ∀ c : Fin l.cells, z.mem (l.countAddr c.val) = count tag c) := by
  let I := fun (i : ℕ) (z : NatState) => l.Preserved before z ∧ z.reg 10 = i ∧
    ∀ c : Fin l.cells, z.mem (l.countAddr c.val) = prior tag i c
  apply (forEach_run pub mac 10 3 countStep l.rows countStep.slots I s m ?_ ?_ ?_).mono le_rfl
  · intro z h
    exact ⟨h.1,fun c => (h.2.2 c).trans (prior_end tag c)⟩
  · refine ⟨reset_preserves preserved _ (by decide), ?_, fun c => (cleared c).trans (prior_zero tag c).symm⟩
    simp [Code.fixedEval, Code.evalNat]
  · intro i z h
    exact ⟨h.2.1,h.1.ready.2.1⟩
  · intro i t mt h
    have hcell : readings mt (l.quads+4*i.val) = (tag i).val := by
      have hi := i.isLt
      apply (h.1.frame _ ?_ ?_).trans (input i)
      · rcases fit.qp with hp|hp <;> omega
      · rcases fit.qc with hc|hc <;> omega
    apply (countStep_run fit tag i pub mac t mt h.1 h.2.1 hcell (h.2.2 _)).mono le_rfl
    rintro z ⟨p,idx,mem⟩
    refine ⟨p,idx,fun c => ?_⟩
    rw [prior_step, mem]
    by_cases same : tag i = c
    · subst c; simp
    · have ne : c.val ≠ (tag i).val := fun he => same (Fin.ext he.symm)
      rw [Function.update_of_ne (show l.countAddr c.val ≠ l.countAddr (tag i).val by
        unfold Layout.countAddr; omega), ite_eq_right same, Nat.add_zero]
      exact h.2.2 c

private theorem run_scan {l : Layout} {w : ℕ} (fit : l.Fits w)
    (tag : Fin l.rows → Fin l.cells) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {before : NatState} (preserved : l.Preserved before (.ofWords s m))
    (counts : ∀ c : Fin l.cells, readings m (l.countAddr c.val) = count tag c) :
    BoundedRun pub mac ((Code.constant 15 0).seq (forEach 10 4 scanStep)) s m
      (1+(2+l.cells*(scanStep.slots+1))) (l.PrefixReady tag before) := by
  let I := fun (i : ℕ) (z : NatState) => l.Preserved before z ∧ z.reg 10 = i ∧ z.reg 15 = start tag i ∧
    (∀ c : Fin l.cells, z.mem (l.countAddr c.val) = count tag c) ∧
    ∀ c : Fin l.cells, c.val < i → z.mem (l.startAddr c.val) = start tag c.val ∧
      z.mem (l.cursors+c.val) = start tag c.val
  apply ((Code.constant 15 0).runFixed pub mac s m (by simp [Code.fixedSafe, Code.safeReadOnly])).seq
  intro t mt eq
  apply (forEach_run pub mac 10 4 scanStep l.cells scanStep.slots I t mt ?_ ?_ ?_).mono le_rfl
  · intro z h
    exact ⟨h.1, h.2.2.2.1, fun c => (h.2.2.2.2 c c.isLt).1, fun c => (h.2.2.2.2 c c.isLt).2⟩
  · rw [eq]
    refine ⟨reset_preserves (reset_preserves preserved _ (by decide)) _ (by decide), ?_, ?_, counts,
      fun c hc => by omega⟩
    · simp [Code.fixedEval, Code.evalNat]
    · simp (config := {decide := true}) [Code.fixedEval, Code.evalNat, start_zero]
  · intro i z h
    exact ⟨h.2.1, h.1.ready.2.2.1⟩
  · intro c u mu h
    apply (scanStep_run fit tag c pub mac u mu h.1 h.2.1 h.2.2.1 (h.2.2.2.1 c)).mono le_rfl
    rintro z ⟨p,idx,acc,mem⟩
    have hc := c.isLt
    refine ⟨p,idx,acc,?_,?_⟩
    · intro d
      have hd := d.isLt
      have apartC : l.countAddr d.val ≠ l.cursors+c.val := by
        unfold Layout.countAddr
        rcases fit.pc with hh|hh <;> omega
      rw [mem, Function.update_of_ne apartC, Function.update_of_ne
        (show l.countAddr d.val ≠ l.startAddr c.val by unfold Layout.countAddr Layout.startAddr; omega)]
      exact h.2.2.2.1 d
    · intro d hd
      have lim := d.isLt
      have apartS : l.startAddr d.val ≠ l.cursors+c.val := by
        unfold Layout.startAddr
        rcases fit.pc with hh|hh <;> omega
      rw [mem, Function.update_of_ne apartS]
      by_cases same : d = c
      · subst d; simp
      · have ne : d.val ≠ c.val := fun he => same (Fin.ext he)
        have apartD : l.cursors+d.val ≠ l.startAddr c.val := by
          unfold Layout.startAddr
          rcases fit.pc with hh|hh <;> omega
        rw [Function.update_of_ne (show l.startAddr d.val ≠ l.startAddr c.val by unfold Layout.startAddr; omega),
          Function.update_of_ne (show l.cursors+d.val ≠ l.cursors+c.val by omega),
          Function.update_of_ne apartD]
        exact h.2.2.2.2 d (by omega)

/-- The three native passes initialize every directory pair and scatter cursor in linear work.
The source quadruples, output triple arena, and all other caller memory are preserved. -/
theorem prefixProgram_run {w : ℕ} (l : Layout) (fit : l.Fits w)
    (tag : Fin l.rows → Fin l.cells) (payload : Fin l.rows → Fin 3 → ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ready : l.Ready (.ofWords s m)) (input : l.Input tag payload (readings m)) :
    BoundedRun pub mac prefixProgram s m (7+19*l.cells+13*l.rows)
      (l.PrefixReady tag (.ofWords s m)) := by
  let before := NatState.ofWords s m
  have p : l.Preserved before before := ⟨ready, rfl, fun _ _ _ => rfl⟩
  have hr := (run_clear fit pub mac s m p).seq (fun t mt h =>
    (run_count fit tag pub mac t mt input.cell h.1 h.2).seq (fun u mu h' =>
      run_scan fit tag pub mac u mu h'.1 h'.2))
  apply hr.mono _ (fun _ h => h)
  change (2+l.cells*(7+1))+((2+l.rows*(12+1))+(1+(2+l.cells*(10+1)))) ≤ _
  omega

end FragmentBucket

end BorderVNP
end Computability
end OAI
