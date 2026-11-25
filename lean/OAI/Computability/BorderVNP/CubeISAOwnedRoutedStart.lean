import OAI.Computability.BorderVNP.CubeSharedRowsSetup
import OAI.Computability.BorderVNP.CubeISAOwnedTrace
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Opening the routed selector and crossing streams of a physical symbol row

The team chooses its ordered endpoint view using the local grouping symbol,
then uses the strict row's fixed selector-prefix length to locate the start
of its crossing bits. Both pointers are computed from the installed frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube.SharedRows

/-- Fetch the two pair-bank parameters and secondary selector width, select
the opposite endpoint, and form the two chronological source cursors. -/
def routedStart : Code := .block [
  readFrame 31 62 63 85, readFrame 32 62 63 86, readFrame 27 62 63 63, indirect 34 6,
  .ifEq 3 14 (.copy 33 15) (.copy 33 14),
  .binary .mul 36 3 10, .binary .add 36 36 33, .binary .mul 36 32 36,
  .binary .add 36 31 36, .binary .add 37 36 34]

private theorem headerRead (dst : Reg) (p : Arg → ℕ) (z : NatState) :
    (indirect dst 6).fixedEval p z =
      ⟨Function.update (Function.update (Function.update z.reg 63 6) 62 (z.reg 27+6))
        dst (z.mem (z.reg 27+6)),z.mem⟩ := by
  simp (config := {decide := true}) [indirect,Code.block,Code.fixedEval,Code.evalNat,addressOp]

/-- A team holding one side of a strict row obtains precisely the view address
in the native shared descriptor and its crossing suffix. The low packet-loop
registers and all shared words survive this preparation. -/
theorem routedStart_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (lo hi : Fin l.groups) (ordered : lo < hi)
    (upper : Bool) (fit : l.Fits w (readings m)) (fields : l.Fields (readings m))
    (frame : readings pub 0 = l.frame) (d : readings s 10 = l.groups)
    (small : readings s 14 = lo.val) (large : readings s 15 = hi.val)
    (own : readings s 3 = (if upper then hi else lo).val)
    (endFit : l.view (if upper then hi else lo).val (if upper then lo else hi).val + l.selectors < 2^w) :
    TraceRun pub mac routedStart s m [] routedStart.slots (fun t mt =>
      let view := l.view (if upper then hi else lo).val (if upper then lo else hi).val
      readings t 36 = view ∧ readings t 37 = view+l.selectors ∧ mt = m ∧
        ∀ j : Reg, j.val < 24 → t j = s j) := by
  let ownIndex := (if upper then hi else lo).val
  let peerIndex := (if upper then lo else hi).val
  have top : ownIndex*l.groups + peerIndex < l.groups*l.groups := by
    have ho : ownIndex < l.groups := Fin.isLt _
    have hp : peerIndex < l.groups := Fin.isLt _
    exact (Nat.add_lt_add_left hp _).trans_le (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right l.groups ho)
  have cmp : ((if upper then hi else lo).val = lo.val) ↔ upper = false := by
    cases upper <;> simp [Fin.ext_iff.symm,ordered.ne']
  have scan (f : Word 8) (dst : Reg) (z : NatState) (hf : f.val ≤ 86) :
      (readFrame dst 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe dst f _ z w (by rw [frame]; have := fit.headers.1; omega)
  have numeric : ownIndex*l.groups < 2^w ∧ ownIndex*l.groups+peerIndex < 2^w ∧
      l.stride*(ownIndex*l.groups+peerIndex) < 2^w ∧ l.view ownIndex peerIndex < 2^w := by
    have sq := fit.square
    change l.view ownIndex peerIndex + l.selectors < 2^w at endFit
    unfold Layout.view at endFit ⊢
    rw [pow_two] at sq
    omega
  have indirectSafe (z : NatState) (hz : z.reg 27 = l.header) :
      (indirect 34 6).fixedSafe w (readings pub) z := by
    have h6 := fit.headers.2
    simp (config := {decide := true}) [indirect,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,hz,h6]
    omega
  let st := NatState.ofWords s m
  have safe : routedStart.fixedSafe w (readings pub) st := by
    cases upper <;>
      simp (config := {decide := true}) [routedStart,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
        Code.evalNat,readFrame_fixedEval,headerRead,addressOpFits,addressOp,st,NatState.ofWords,frame,
        scan _ _ _ (by decide : (85 : Word 8).val ≤ 86),scan _ _ _ (by decide : (86 : Word 8).val ≤ 86),
        scan _ _ _ (by decide : (63 : Word 8).val ≤ 86),indirectSafe,fields.declaration,fields.views.1,
        fields.views.2,fields.header.2.2,d,small,large,own,Fin.ext_iff.symm,ordered.ne'] at * <;>
      simp_all [ownIndex,peerIndex,Layout.view]
  obtain ⟨es,t,mt,r,cap,eqn⟩ := routedStart.runFixed pub mac s m safe
  have ret : mt = m := by
    apply funext; intro addr; apply Fin.ext
    exact congrFun (congrArg NatState.mem eqn) addr |>.trans (by
      by_cases e : (NatState.ofWords s m).reg 3 = (NatState.ofWords s m).reg 14 <;>
        simp [routedStart,Code.block,Code.fixedEval,readFrame_fixedEval,headerRead,e] <;> rfl)
  have stable j (hj : j.val < 24) : t j = s j := by
    apply r.keepsReg
    exact (by decide : ∀ j : Reg, j.val < 24 → routedStart.keeps j = true) j hj
  have post : readings t 36 = l.view ownIndex peerIndex ∧
      readings t 37 = l.view ownIndex peerIndex+l.selectors := by
    change (NatState.ofWords t mt).reg 36 = _ ∧ (NatState.ofWords t mt).reg 37 = _
    rw [eqn]
    cases upper <;> simp (config := {decide := true}) [routedStart,Code.block,Code.fixedEval,Code.evalNat,
      readFrame_fixedEval,headerRead,addressOp,NatState.ofWords,ownIndex,peerIndex,Layout.view,frame,
      fields.declaration,fields.views.1,fields.views.2,fields.header.2.2,d,small,large,own,Fin.ext_iff.symm,ordered.ne']
  have signs := r.unsigned_events (by decide)
  exact ⟨es,t,mt,r,⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (signs e he).1,
    fun e he => (signs e he).2⟩,cap,post.1,post.2,ret,stable⟩

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
