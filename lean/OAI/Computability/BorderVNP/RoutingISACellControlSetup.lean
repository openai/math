import OAI.Computability.BorderVNP.RoutingISACellControlRows

/-! # Load the length-only cell control allocation header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open VPVNP.BurstRAM
open private indirect from OAI.Computability.BorderVNP.RoutingISACellControlRows

private theorem indirectEval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) :
    (indirect d f).fixedEval pub z = ⟨Function.update
      (Function.update (Function.update z.reg 63 f.val) 62 (z.reg 61+f.val)) d
      (z.mem (z.reg 61+f.val)),z.mem⟩ := by
  simp (config := {decide:=true}) [indirect,Code.block,Code.fixedEval,Code.evalNat,addressOp]

set_option maxHeartbeats 2200000 in
/-- The fixed setup recovers all registers directly from the extended shared frame. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (hp : (pub 0).val=l.frame) (f : l.Fields (readings m)) (fit : l.Room w) :
    BoundedRun pub mac setup s m setup.slots (fun z => l.Ready 0 0 z ∧ z.mem=readings m) := by
  have hf : readings pub 0=l.frame := hp
  obtain ⟨⟨t,c,b,o,eb,lp,mul,ctl⟩,⟨o4,ss,sd,cnt,mg,rp,o6,rg⟩⟩ := f
  have fs (d : Reg) (a : Word 8) (z : NatState) (ha : a.val ≤ 92) :
      (readFrame d 62 63 a).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe _ _ _ _ _ (by rw [hf]; have := fit.frame.1; omega)
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide:=true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      readFrame_fixedEval,indirect,addressOpFits,addressOp,NatState.ofWords,hf,o,eb,lp,mul,ctl,
      fs _ _ _ (by decide : (0 : Word 8).val ≤ 92),fs _ _ _ (by decide : (15 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (72 : Word 8).val ≤ 92),fs _ _ _ (by decide : (87 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (7 : Word 8).val ≤ 92),fs _ _ _ (by decide : (65 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (1 : Word 8).val ≤ 92),fs _ _ _ (by decide : (67 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (92 : Word 8).val ≤ 92)]
    have := fit.frame; have := fit.input
    have hw : 0 < w := by by_contra! h; have := Nat.eq_zero_of_le_zero h; subst w; norm_num at *
    have := Nat.one_lt_pow (by omega : w ≠ 0) (by decide : 1 < 2)
    omega
  apply (setup.runFixed pub mac s m safe).mono le_rfl
  rintro z rfl
  constructor
  · intro r h
    rcases r with ⟨r,hr⟩; change r < 20 at h
    interval_cases r <;> simp (config := {decide:=true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
      readFrame_fixedEval,indirectEval,NatState.ofWords,addressOp,Layout.regValue,hf,t,c,b,o,eb,lp,mul,ctl,o4,ss,sd,cnt,mg,rp,o6,rg]
  · simp [setup,Code.block,Code.fixedEval,readFrame_fixedEval,indirectEval,NatState.ofWords]

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
