import OAI.Computability.BorderVNP.FragmentBucketLoop
import OAI.Computability.BorderVNP.FragmentBucketOrder

/-! # The fixed ordinary word-RAM scatter of one sparse interval triple -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Load the four source words before storing the three payload words. The cell
cursor is the next record index inside its stable bucket. -/
def scatterStep : Code := .block [
  .constant 24 4,.binary .mul 14 24 13,.binary .add 14 2 14,.load 15 14,
  .binary .add 16 7 15,.load 17 16,.constant 24 3,.binary .mul 18 24 17,.binary .add 18 6 18,
  .constant 11 1,.binary .add 14 14 11,.load 19 14,.binary .add 14 14 11,.load 20 14,
  .binary .add 14 14 11,.load 21 14,
  .store 18 19,.binary .add 18 18 11,.store 18 20,.binary .add 18 18 11,.store 18 21,
  .binary .add 17 17 11,.store 16 17,.binary .add 13 13 11]

/-- The complete shared memory image of one iteration. -/
def scatterWrites (mem : ℕ → ℕ) (base cursor next : ℕ) (p : Fin 3 → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update mem base (p 0))
    (base+1) (p 1)) (base+2) (p 2)) cursor next

private theorem fit_addresses {l : Layout} {w : ℕ} (fit : l.Fits w) (i next : Fin l.rows) (c : Fin l.cells) :
    l.quads+4*i.val+3 < 2^w ∧ l.triples+3*next.val+2 < 2^w ∧ l.cursors+c.val < 2^w := by
  have hi := i.isLt; have hn := next.isLt; have hc := c.isLt
  obtain ⟨_,_,_,q,_,t,u,_⟩ := fit
  omega

variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
variable (l : Layout) (tag : Fin l.rows → Fin l.cells) (payload : Fin l.rows → Fin 3 → ℕ)

/-- Actual bounded native execution of one scatter row. All persistent registers
and all memory outside its four stores retain their previous values. -/
theorem scatterStep_run (fit : l.Fits w) (i : Fin l.rows) (s : Bank w) (m : Memory w)
    (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i.val)
    (input : l.Input tag payload (readings m))
    (cursor : readings m (l.cursors+(tag i).val) = (dest tag i).val) :
    BoundedRun pub macros scatterStep s m scatterStep.slots (fun z =>
      z.reg 13 = i.val+1 ∧ (∀ j : Reg, j.val < 10 → z.reg j = (s j).val) ∧
      z.mem = scatterWrites (readings m) (l.triples+3*(dest tag i).val) (l.cursors+(tag i).val)
        ((dest tag i).val+1) (payload i)) := by
  obtain ⟨hq,_,_,_,ht,hc⟩ := ready
  change readings s 2 = l.quads at hq
  change readings s 6 = l.triples at ht
  change readings s 7 = l.cursors at hc
  change readings s 13 = i.val at idx
  have tagRead := input.cell i
  have f0 : readings m (l.quads+(4*i.val+1)) = payload i 0 := by simpa [Nat.add_assoc] using input.field i 0
  have f1 : readings m (l.quads+(4*i.val+2)) = payload i 1 := by simpa [Nat.add_assoc] using input.field i 1
  have f2 : readings m (l.quads+(4*i.val+3)) = payload i 2 := by simpa [Nat.add_assoc] using input.field i 2
  obtain ⟨qin,tin,cin⟩ := fit_addresses fit i (dest tag i) (tag i)
  have rowFit := fit.rowCount
  have dw := (dest tag i).isLt
  have iw := i.isLt
  have cw := fit.literals
  have hw : w ≠ 0 := by rintro rfl; norm_num at cw
  have safe : scatterStep.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [scatterStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,NatState.ofWords,addressOp,addressOpFits,hq,ht,hc,idx,tagRead,cursor,hw]
    repeat' apply And.intro <;> omega
  apply (scatterStep.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨?_,fun j hj => scatterStep.fixedEval_protected (readings pub) (.ofWords s m) (by decide : scatterStep.protects 10 = true) j hj,?_⟩
  · simp (config := {decide := true}) [scatterStep,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,
      addressOp,idx]
  · simp (config := {decide := true}) [scatterStep,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,
      addressOp,hq,ht,hc,idx,tagRead,cursor,f0,f1,f2,scatterWrites,Nat.add_assoc]

end FragmentBucket

end BorderVNP
end Computability
end OAI
