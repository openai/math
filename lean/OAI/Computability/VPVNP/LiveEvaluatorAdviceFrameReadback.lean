import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrames
import OAI.Computability.VPVNP.CompressorRecordFrame

/-!
# Reading the published midpoint frames on the native machine

Every successful initializer call has the same empty choice stream and
the specified report. Its four output arrays are exactly the public
operand banks that the external-frame compiler fetches for later stages.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceFrames

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

private theorem store_no_choices {pub : FramePub w} {st : Word w}
    (ss : List (Option (Fin 32))) {rs m es out m'} (h : Flow.Exec pub st (storeFlow ss) rs m es out m') :
    choiceBits es = [] := by
  induction ss generalizing rs m es out m' with
  | nil => cases h with | line he => exact Flow.line_choices he
  | cons a ss ih =>
    cases a with
    | none =>
      cases h with
      | seq hl hr => cases hl with | line he => simp only [Flow.choiceBits_append, Flow.line_choices he, ih hr, List.nil_append]
    | some r =>
      cases h with
      | seq hl hr =>
        cases hl with
        | line he =>
          cases hr with
          | seq hi ht =>
            cases hi with
            | line hg => simp only [Flow.choiceBits_append, Flow.line_choices he, Flow.line_choices hg, ih ht, List.nil_append]

private theorem valid_body {pub : FramePub w} {st : Word w} {rs m es out m'}
    (h : Flow.Exec pub st body rs m es out m') :
    actualLength pub m ≤ pub 1 ∧ 0 < pub 2 ∧ choiceBits es = [] := by
  cases h with
  | seq hs hr =>
    obtain ⟨hcap,hw,hes,-,-⟩ := (setup_iff pub st rs m _ _ _).mp hs
    have hb : choiceBits (setupEvents pub m) = [] := rfl
    exact ⟨hcap,hw,by rw [Flow.choiceBits_append, hes, hb, store_no_choices _ hr]; rfl⟩

/-- Exact acceptance and report for any sufficient clock, including the native
surplus-choice rejection at the single-call stage exit. -/
theorem execute_frames_iff (pub : FramePub w) (st : Word w) (m : Memory w) (bs : List Bool)
    (fuel : ℕ) (hf : 83 ≤ fuel) (r : Report w) :
    let machine := template.instantiate w pub
    execute machine.program fuel (machine.program.start st) m bs = some r ↔
      actualLength pub m ≤ pub 1 ∧ 0 < pub 2 ∧ bs = [] ∧ r = ⟨events pub m,none⟩ := by
  have run (hcap : actualLength pub m ≤ pub 1) (hw : 0 < pub 2) :
      let machine := template.instantiate w pub
      execute machine.program fuel (machine.program.start st) m [] = some ⟨events pub m,none⟩ := by
    have h := (execute_frames pub st m hcap hw).1
    obtain ⟨out,mem,he,hr,hlen,hb⟩ := (Flow.template_execute_iff body none pub st _ _ m 83 [] _).mp h
    exact (Flow.template_execute_iff body none pub st _ _ m fuel [] _).mpr
      ⟨out,mem,he,hr,lt_of_lt_of_le hlen hf,hb⟩
  constructor
  · intro h
    obtain ⟨out,mem,he,-,-,hb⟩ := (Flow.template_execute_iff body none pub st _ _ m fuel bs r).mp h
    obtain ⟨hc,hw,hbits⟩ := valid_body he
    have hbs := hb.symm.trans hbits
    rw [hbs] at h
    exact ⟨hc,hw,hbs,Option.some.inj (h.symm.trans (run hc hw))⟩
  · rintro ⟨hc,hw,rfl,rfl⟩
    exact run hc hw

private theorem offsetData {k : ℕ} (base : Word w) (mem : Memory w) (offset : ℕ)
    (hfit : base.val+offset+k ≤ 2^w) (j : Fin k) :
    CompressorRecords.Frame.data (base + (offset : Word w)) mem j = mem (base.val+offset+j.val) := by
  have ho : offset < 2^w := by have := j.isLt; omega
  have hv : ((offset : Word w) : ℕ) = offset := Nat.mod_eq_of_lt ho
  have hbase : (base+(offset : Word w)).val = base.val+offset :=
    (Fin.val_add_eq_of_add_lt (by rw [hv]; have := j.isLt; omega)).trans (congrArg (base.val + ·) hv)
  rw [CompressorRecords.Frame.data_at _ _ (by rw [hbase]; exact hfit), hbase]

/-- The four operand banks seen through the exact loader used by `Frame.compile`. -/
theorem frameData (pub : FramePub w) (m : Memory w) (hw : 0 < w) (hf : (pub 3).val+22 ≤ 2^w) :
    let out := published pub m
    CompressorRecords.Frame.data (pub 3) out = prefixFrame pub m ∧
    CompressorRecords.Frame.data (pub 3+8) out = copyFrame pub m ∧
    CompressorRecords.Frame.data (pub 3+13) out = skeletonFrame pub m ∧
    CompressorRecords.Frame.data (pub 3+17) out = scatterFrame pub m := by
  obtain ⟨hP,hC,hS,hE⟩ := published_at pub m hw hf
  dsimp only
  refine ⟨funext (fun j => ?_), funext (fun j => ?_), funext (fun j => ?_), funext (fun j => ?_)⟩
  · exact (CompressorRecords.Frame.data_at _ _ (by omega) j).trans (hP j)
  · exact (offsetData _ _ 8 (by omega) j).trans (hC j)
  · exact (offsetData _ _ 13 (by omega) j).trans (hS j)
  · exact (offsetData _ _ 17 (by omega) j).trans (hE j)

end LiveEvaluatorAdviceFrames

end VPVNP
end Computability
end OAI
