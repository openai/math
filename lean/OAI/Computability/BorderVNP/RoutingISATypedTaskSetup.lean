import OAI.Computability.BorderVNP.RoutingISATypedTaskBuilder

/-! # Native setup for the owned cell-task table scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM
open private controlWord from OAI.Computability.BorderVNP.RoutingISATypedTaskBuilder

private theorem controlEval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) :
    (controlWord d f).fixedEval pub z = ⟨Function.update
      (Function.update (Function.update z.reg 63 f.val) 62 (z.reg 61+f.val)) d
        (z.mem (z.reg 61+f.val)),z.mem⟩ := by
  simp (config := {decide:=true}) [controlWord,Code.block,Code.fixedEval,Code.evalNat,addressOp]

set_option maxHeartbeats 2000000 in
/-- Load the public directory and allocation headers without writing any shared word. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (hp : (pub 0).val = l.frame) (fields : l.Fields (readings m)) (room : l.Room (readings m) w) :
    BoundedRun pub mac setup s m setup.slots (fun z => l.Ready 0 0 z ∧ z.mem=readings m) := by
  have hpub : readings pub 0 = l.frame := hp
  obtain ⟨⟨ft,fm,fc,fn,fb,fo,fr,fh⟩,⟨h0,h1,h2,h3,h4,h5,h6,h7⟩⟩ := fields
  have fs (d : Reg) (f : Word 8) (z : NatState) (hf : f.val ≤ 92) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe _ _ _ _ _ (by rw [hpub]; have := room.frame; omega)
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide:=true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,readFrame_fixedEval,addressOpFits,addressOp,NatState.ofWords,hpub,ft,fm,fc,fn,fb,fo,fr,fh,
      h0,h1,h2,h3,h4,h5,h6,
      fs _ _ _ (by decide : (0 : Word 8).val ≤ 92),fs _ _ _ (by decide : (15 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (14 : Word 8).val ≤ 92),fs _ _ _ (by decide : (72 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (87 : Word 8).val ≤ 92),fs _ _ _ (by decide : (7 : Word 8).val ≤ 92),
      fs _ _ _ (by decide : (92 : Word 8).val ≤ 92),fs _ _ _ (by decide : (89 : Word 8).val ≤ 92),controlWord]
    have := room.frame
    have := room.control
    have := room.sorted
    have := room.offsets
    have hw : 0 < w := by by_contra! z; have := Nat.eq_zero_of_le_zero z; subst w; norm_num at *
    have hpow := Nat.one_lt_pow (by omega : w ≠ 0) (by decide : 1 < 2)
    omega
  apply (setup.runFixed pub mac s m safe).mono le_rfl
  rintro z rfl
  constructor
  · intro r hr
    rcases r with ⟨r,hr'⟩
    change r < 20 at hr
    interval_cases r <;> simp (config := {decide:=true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
      readFrame_fixedEval,controlEval,NatState.ofWords,addressOp,Layout.regValue,hpub,ft,fm,fc,fn,fb,fo,fr,fh,h0,h1,h2,h3,h4,h5,h6,h7]
  · simp [setup,Code.block,Code.fixedEval,readFrame_fixedEval,controlEval,NatState.ofWords]

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
