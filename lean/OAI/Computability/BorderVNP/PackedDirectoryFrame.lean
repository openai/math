import OAI.Computability.BorderVNP.PackedDirectoryEval
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Frame setup and output-count publication for the public delivery directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (word word_val)

private theorem readFrame_fit {w : ℕ} (d : Reg) (f : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w pub mem s ↔ pub 0 + f.val < 2^w := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.safeReadOnly, Code.evalNat,addressOpFits]
  omega

/-- It suffices to fit the frame, the total candidate count and the full processor
stride. This ensures all intermediate loop-counter products fit as well. -/
theorem setup_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    let d := frameLayout pub mem
    0 < d.teams → 0 < d.processors → 0 < d.block →
    pub 0 + 70 < 2^w → d.candidates < 2^w → d.stride < 2^w →
    setup.safeReadOnly w pub mem s := by
  intro d ht hr hg hframe hc hs
  have hf : 0 < d.fields := Nat.zero_lt_succ _
  let count := d.teams*d.processors*d.fields
  let pieces := d.literal/d.block+2
  have hcount : 0 < count := by dsimp [count]; positivity
  have hpieces : 0 < pieces := Nat.zero_lt_succ _
  have one := Nat.le_mul_of_pos_right count hpieces
  have two := Nat.le_mul_of_pos_left pieces hcount
  have three := Nat.le_mul_of_pos_right (d.teams*d.processors) hf
  have four := Nat.le_mul_of_pos_left d.fields (Nat.mul_pos ht hr)
  have five := Nat.le_mul_of_pos_left d.literal hf
  dsimp only [count,pieces,d,frameLayout,Layout.candidates,Layout.stride] at *
  simp (config := { decide := true }) [setup,Code.block,Code.safeReadOnly,Code.evalNat,readFrameFixed,
    readFrame_fit,addressOpFits,addressOp]
  repeat' apply And.intro
  all_goals first | omega | (intro hw; subst w; simp at hframe)

/-- Publish the final count into the real frame word 9. The preceding loop advanced its
cursor by exactly seven words for each populated row. -/
theorem finish_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base rows : ℕ) (hstart : (s 21).val = base)
    (hend : (s 20).val = base+7*rows) (hframe : (pub 0).val+9 < 2^w) :
    ∃ es t, Runs pub macros finish s m es t
      (Function.update m ((pub 0).val+9) (word w rows)) ∧ traceCost es ≤ 7 := by
  have safe : finishCalc.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := { decide := true }) [finishCalc,Code.safeReadOnly,Code.evalNat,Code.block,
      addressOp,addressOpFits,readings,hstart,hend]
    omega
  obtain ⟨es,t,run,ct,values⟩ := finishCalc.runReadOnly pub macros m s safe
  have addr : (t 62).val = (pub 0).val+9 := by
    simpa (config := { decide := true }) [finishCalc,Code.block,Code.evalNat,readings,addressOp] using congrFun values 62
  have value : (t 40).val = rows := by
    simpa (config := { decide := true }) [finishCalc,Code.block,Code.evalNat,readings,addressOp,
      hstart,hend] using congrFun values 40
  have wordValue : t 40 = word w rows := Fin.ext (value.trans (word_val w rows (value ▸ (t 40).isLt)).symm)
  have store := Runs.store pub macros 62 40 t m
  rw [addr,wordValue] at store
  refine ⟨_,_,run.seq store,?_⟩
  rw [show traceCost (es++_) = traceCost es+1 from VPVNP.RAMBuckets.cost_append ..]
  change traceCost es ≤ 6 at ct
  omega

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
