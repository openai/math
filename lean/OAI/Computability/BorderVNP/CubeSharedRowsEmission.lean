import OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-! # Complete native shared-row emission, including the public record count -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Commit the output cursor to the transmission-count field of the common frame. -/
def commit : Code := .block [.publicWord 62 0,.constant 63 13,.binary .add 62 62 63,.store 62 15]

/-- All native instructions needed after the data records have been written. -/
def program : Code := .seq setup (.seq pass commit)

/-- Clock for setup, quadratic symbol-pair traversal, and the count commit. -/
def budget (groups : ℕ) :=
  setup.slots + (3+groups*(3+groups*(loadFields.slots+storeFields.slots+1)+1) + commit.slots)

/-- The final count, all genuine shared records, and the retained prefix and outside contents. -/
structure Layout.Emitted (l : Layout) (before after : ℕ → ℕ) : Prop where
  /-- Count of data records and of all distinct symbol pairs together. -/
  count : after (l.frame+13) = l.dataCount+l.groups.choose 2
  /-- All seven words as actually consumed by the transmission scheduler. -/
  rows : ∀ t < l.groups, ∀ s < t, ∀ j : Fin 7,
    after (l.address (l.rowIndex s t)+j.val) = l.row before s t j
  /-- Addresses outside the shared suffix retain their values, except the count field itself. -/
  outside : ∀ x, x ≠ l.frame+13 →
    (x < l.address l.dataCount ∨ l.address (l.dataCount+l.groups.choose 2) ≤ x) → after x = before x

private theorem run_commit {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) (hf : (pub 0).val = l.frame)
    (bank : Bank w) (m : Memory w) (out : OuterState l before l.groups (.ofWords bank m)) :
    BoundedRun pub macros commit bank m commit.slots (fun z => l.Emitted before z.mem) := by
  have hp : readings pub 0 = l.frame := hf
  have hc : (bank 15).val = l.dataCount+l.groups.choose 2 := by
    change (NatState.ofWords bank m).reg 15 = _
    simpa only [Layout.rowIndex,Nat.add_zero] using out.cursor
  have addr : l.frame+13 < 2^w := by have := fit.headers.1; omega
  have safe : commit.fixedSafe w (readings pub) (.ofWords bank m) := by
    simp (config := {decide := true}) [commit,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
      Code.evalNat,addressOpFits,hp,addr]
    omega
  apply (commit.runFixed pub macros bank m safe).mono le_rfl
  rintro z rfl
  have written : (commit.fixedEval (readings pub) (.ofWords bank m)).mem =
      Function.update (readings m) (l.frame+13) (l.dataCount+l.groups.choose 2) := by
    simp (config := {decide := true}) [commit,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,readings,hf,hc]
  rw [written]
  refine ⟨Function.update_self ..,?_,?_⟩
  · intro t ht s hs j
    have lo : l.dataCount ≤ l.rowIndex s t := by dsimp [Layout.rowIndex]; omega
    have hi := l.index_lt hs ht
    have hsep := fit.separate t ht s hs (l.frame+13) (by simp)
    have distinct : l.address (l.rowIndex s t)+j.val ≠ l.frame+13 := by
      dsimp [Layout.address] at *
      have := j.isLt
      omega
    rw [Function.update_of_ne distinct]
    exact out.image.rows t ht s hs (by simpa only [Layout.rowIndex,Nat.add_zero] using hi) j
  · intro x hx ho
    rw [Function.update_of_ne hx]
    apply out.image.outside
    simpa only [Layout.rowIndex,Nat.add_zero] using ho

/-- The complete fixed program appends every distinct-symbol pair once and records the new count.
The measured native clock is independent of the number of packets and the number of bits. -/
theorem run_program {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (bank : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : (pub 0).val = l.frame) (fields : l.Fields (readings m)) :
    BoundedRun pub macros program bank m (budget l.groups) (fun z => l.Emitted (readings m) z.mem) := by
  apply (run_setup pub macros l bank m fit hf fields).seq
  intro u mu hu
  have hm : readings mu = readings m := hu.2
  apply (run_pass pub macros l u mu (hm.symm ▸ fit) hu.1).seq
  intro v mv hv
  apply run_commit pub macros l (readings m) fit hf v mv
  rw [← hm]
  exact hv

/-- An absolute square-alphabet budget for this public preparation, including empty and singleton alphabets. -/
theorem budget_le (groups : ℕ) :
    budget groups ≤ (setup.slots+loadFields.slots+storeFields.slots+commit.slots+9)*(groups+1)^2 := by
  dsimp [budget]
  nlinarith [Nat.zero_le (setup.slots*groups),Nat.zero_le (setup.slots*groups^2),
    Nat.zero_le (commit.slots*groups),Nat.zero_le (commit.slots*groups^2),
    Nat.zero_le (loadFields.slots*groups),Nat.zero_le (storeFields.slots*groups)]

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
