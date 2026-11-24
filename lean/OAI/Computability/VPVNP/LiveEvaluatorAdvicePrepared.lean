import OAI.Computability.VPVNP.LiveEvaluatorAdviceDistribution
import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrameReadback
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackStage

/-!
# Preparing the evaluator's advice banks in physical memory

First the native packer reads the raw length. The next call validates it and
publishes four operand frames. The prefix packer takes its operands from the
first published frame, and the ordinal packer fills the lookup table. The
four stages run successively on the memory produced by their predecessors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM CutSchedule ChainAssignments LiveEvaluatorAdviceFrames
open scoped Fin.CommRing

variable {w t ordW a d h Δ : ℕ}

/-- The public operands and their allocated address intervals. The cursor
bounds cover the reset column as well as every data column. -/
structure PreparedLayout (lp : Fin 5 → Word w) (fp : FramePub w) (op : Fin 5 → Word w)
    (raw : List Bool) (t ordW : ℕ) : Prop where
  width : 4 ≤ w
  frameWidth : (fp 2).val = w
  rawFits : raw.length ≤ (fp 1).val
  lengthSource : (lp 0).val = (fp 0).val
  lengthDest : (lp 1).val = (fp 3).val+22
  lengthWidth : (lp 2).val = w
  lengthCount : (lp 3).val = w
  lengthRows : (lp 4).val = 1
  ordinalSource : (op 0).val = (fp 0).val+w+(fp 1).val
  ordinalDest : op 1 = fp 10
  ordinalWidth : (op 2).val = ordW
  ordinalFits : ordW ≤ w
  ordinalCount : (op 3).val = t*ordW
  ordinalRows : (op 4).val = t
  adviceBeforeFrame : (fp 0).val+w+(fp 1).val+t*ordW ≤ (fp 3).val
  frameBeforePrefix : (fp 3).val+23 ≤ (fp 4).val
  prefixBeforeOrder : (fp 4).val+(raw.length ⌈/⌉ w) ≤ (op 1).val
  orderFit : (op 1).val+t ≤ 2^w
  prefixCursorFit : (raw.length ⌈/⌉ w)*(w+1) < 2^w
  orderCursorFit : t*(ordW+1) < 2^w

/-- Memory after the initial length pack, whose only output is the length
at frame offset 22. -/
def lengthMemory (lp : Fin 5 → Word w) (raw : List Bool) (m : Memory w) : Memory w :=
  packMemory lp (lengthBits w raw) m (packCalls lp)

/-- Five dynamically published operands of the prefix stage. -/
def rawOperands (lp : Fin 5 → Word w) (fp : FramePub w) (raw : List Bool) (m : Memory w) :=
  prefixFrame fp (lengthMemory lp raw m)

/-- Memory after frame publication and prefix packing. -/
def rawMemory (lp : Fin 5 → Word w) (fp : FramePub w) (raw : List Bool) (m : Memory w) : Memory w :=
  let rp := rawOperands lp fp raw m
  packMemory rp raw (published fp (lengthMemory lp raw m)) (packCalls rp)

/-- Final memory of the four native stages. -/
def preparedAdviceMemory (lp : Fin 5 → Word w) (fp : FramePub w) (op : Fin 5 → Word w)
    (raw : List Bool) (values : Fin t → Word ordW) (m : Memory w) : Memory w :=
  packMemory op (ordinalBits values) (rawMemory lp fp raw m) (packCalls op)

variable {lp op : Fin 5 → Word w} {fp : FramePub w} {raw : List Bool}

private theorem frameFit (L : PreparedLayout lp fp op raw t ordW) : (fp 3).val+22 < 2^w :=
  lt_of_lt_of_le (by have := L.frameBeforePrefix; omega) (fp 4).isLt.le

/-- The frame program reads the newly packed length at its designated address. -/
theorem prepared_length (L : PreparedLayout lp fp op raw t ordW) (m : Memory w) :
    (actualLength fp (lengthMemory lp raw m)).val = raw.length := by
  rw [actualLength_at fp _ (frameFit L), ← L.lengthDest]
  exact packMemory_length lp raw m L.lengthWidth (by rw [L.lengthRows]; decide)
    (L.rawFits.trans_lt (fp 1).isLt)

private theorem rawSourceAddress (L : PreparedLayout lp fp op raw t ordW) (m : Memory w) :
    ((rawOperands lp fp raw m) 0).val = (fp 0).val+w := by
  change (fp 0+fp 2).val = _
  rw [Fin.val_add, L.frameWidth, Nat.mod_eq_of_lt (by have := L.adviceBeforeFrame; have := (fp 3).isLt; omega)]

theorem rawOperands_length (L : PreparedLayout lp fp op raw t ordW) (m : Memory w) :
    ((rawOperands lp fp raw m) 3).val = raw.length := prepared_length L m

theorem rawOperands_rows (L : PreparedLayout lp fp op raw t ordW) (m : Memory w) :
    ((rawOperands lp fp raw m) 4).val = raw.length ⌈/⌉ w := by
  change (prefixRows fp _).val = _
  rw [prefixRows_val fp _ (by rw [L.frameWidth]; have := L.width; omega),
    prepared_length L m, L.frameWidth]

theorem lengthLayout (L : PreparedLayout lp fp op raw t ordW) : PackLayout lp (lengthBits w raw) := by
  have hw := L.width
  have hsf := L.adviceBeforeFrame
  have hlf := L.frameBeforePrefix
  have hpf := (fp 4).isLt
  have hwfit : w+1 < 2^w := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hw
    have := Nat.lt_two_pow_self (n := n)
    rw [hn, pow_add]; omega
  refine ⟨by omega, L.lengthWidth.le, by rw [L.lengthCount, length_lengthBits], ?_, ?_, ?_, ?_⟩
  · simpa [packCalls, L.lengthWidth, L.lengthRows] using hwfit
  · rw [L.lengthSource, length_lengthBits]; omega
  · rw [L.lengthDest, L.lengthRows]; omega
  · right; rw [L.lengthSource, L.lengthDest, length_lengthBits]; omega

theorem rawLayout (L : PreparedLayout lp fp op raw t ordW) (m : Memory w) :
    PackLayout (rawOperands lp fp raw m) raw := by
  have hdest : rawOperands lp fp raw m 1 = fp 4 := rfl
  have hwidth : (rawOperands lp fp raw m 2).val = w := L.frameWidth
  have h₁ := L.adviceBeforeFrame
  have h₂ := L.frameBeforePrefix
  have h₃ := L.prefixBeforeOrder
  have h₄ := L.rawFits
  have h₅ := (op 1).isLt
  refine ⟨by have := L.width; omega, hwidth.le, prepared_length L m, ?_, ?_, ?_, ?_⟩
  · rw [packCalls, rawOperands_rows L m, hwidth]; exact L.prefixCursorFit
  · rw [rawSourceAddress L m]; omega
  · rw [hdest, rawOperands_rows L m]; omega
  · right; rw [rawSourceAddress L m, hdest]; omega

theorem orderLayout (L : PreparedLayout lp fp op raw t ordW) (values : Fin t → Word ordW) :
    PackLayout op (ordinalBits values) := by
  have h₁ := L.adviceBeforeFrame
  have h₂ := L.frameBeforePrefix
  have h₃ := L.prefixBeforeOrder
  have h₄ := (op 1).isLt
  refine ⟨by have := L.width; omega, L.ordinalWidth.trans_le L.ordinalFits,
    by rw [L.ordinalCount, length_ordinalBits], ?_, ?_, ?_, ?_⟩
  · rw [packCalls, L.ordinalRows, L.ordinalWidth]; exact L.orderCursorFit
  · rw [L.ordinalSource, length_ordinalBits]; omega
  · rw [L.ordinalRows]; exact L.orderFit
  · right; rw [L.ordinalSource, length_ordinalBits]; omega

private theorem before_frames (L : PreparedLayout lp fp op raw t ordW) (m : Memory w)
    (k : ℕ) (hk : k < (fp 3).val) :
    published fp (lengthMemory lp raw m) k = m k := by
  rw [published_outside fp _ (by have := L.width; omega) (frameFit L).le k (.inl hk)]
  apply packMemory_outside
  left; rw [L.lengthDest]; omega

private theorem final_before_prefix (L : PreparedLayout lp fp op raw t ordW)
    (values : Fin t → Word ordW) (m : Memory w) (k : ℕ) (hk : k < (fp 4).val) :
    preparedAdviceMemory lp fp op raw values m k = published fp (lengthMemory lp raw m) k := by
  rw [preparedAdviceMemory, packMemory_outside op _ _ _ _ (.inl (by have := L.prefixBeforeOrder; omega))]
  exact packMemory_outside _ _ _ _ _ (.inl hk)

/-- Final readback of the four operand frames and the three packed banks.
Outside the frame interval, packed prefix and ordinal table, memory agrees
pointwise with its value before the length stage. -/
structure PreparedImage (lp : Fin 5 → Word w) (fp : FramePub w) (op : Fin 5 → Word w)
    (raw : List Bool) (values : Fin t → Word ordW) (m out : Memory w) : Prop where
  frames : PublishedAt fp (lengthMemory lp raw m) out
  lengthWord : (out ((fp 3).val+22)).val = raw.length
  rawWord (j : ℕ) (hj : j < raw.length ⌈/⌉ w) :
    out ((fp 4).val+j) = LiveEvaluatorInitialize.inputWord w raw j
  ordinalWord (j : Fin t) : (out ((op 1).val+j.val)).val = (values j).val
  outside (k : ℕ) (hf : k < (fp 3).val ∨ (fp 3).val+23 ≤ k)
      (hr : k < (fp 4).val ∨ (fp 4).val+(raw.length ⌈/⌉ w) ≤ k)
      (ho : k < (op 1).val ∨ (op 1).val+t ≤ k) : out k = m k

theorem prepared_image (L : PreparedLayout lp fp op raw t ordW) (values : Fin t → Word ordW) (m : Memory w) :
    PreparedImage lp fp op raw values m (preparedAdviceMemory lp fp op raw values m) := by
  have hw : 0 < w := by have := L.width; omega
  have hF := L.frameBeforePrefix
  have hO := L.prefixBeforeOrder
  have ht := published_at fp (lengthMemory lp raw m) hw (frameFit L).le
  constructor
  · constructor <;> intro j
    · exact (final_before_prefix L _ m _ (by have := j.isLt; omega)).trans (ht.prefixWord j)
    · exact (final_before_prefix L _ m _ (by have := j.isLt; omega)).trans (ht.copyWord j)
    · exact (final_before_prefix L _ m _ (by have := j.isLt; omega)).trans (ht.skeletonWord j)
    · exact (final_before_prefix L _ m _ (by have := j.isLt; omega)).trans (ht.scatterWord j)
  · rw [final_before_prefix L _ m _ (by omega), published_outside _ _ hw (frameFit L).le _ (.inr le_rfl)]
    simpa only [actualLength_at fp _ (frameFit L)] using prepared_length L m
  · intro j hj
    rw [preparedAdviceMemory, packMemory_outside op _ _ _ _ (.inl (by omega))]
    exact packMemory_raw (rawOperands lp fp raw m) raw _ L.frameWidth j ((rawOperands_rows L m).symm ▸ hj)
  · intro j
    have ho := packMemory_ordinal op values (rawMemory lp fp raw m) L.ordinalWidth L.ordinalFits
      L.ordinalRows.symm.le j
    exact congrArg Fin.val ho
  · intro k hf hr ho
    have hro : (rawOperands lp fp raw m 1).val = (fp 4).val := rfl
    rw [preparedAdviceMemory, packMemory_outside _ _ _ _ _ (L.ordinalRows ▸ ho), rawMemory,
      packMemory_outside _ _ _ _ _ (by rw [hro, rawOperands_rows L m]; exact hr),
      published_outside _ _ hw (frameFit L).le _ (by omega), lengthMemory, packMemory_outside]
    rw [L.lengthDest, L.lengthRows]; omega

/-- Exact deterministic call sequence, costs and post-memory of one native
packing bank. -/
structure PackHistory (pub : Fin 5 → Word w) (bits : List Bool) (m : Memory w)
    (fuel : ℕ) (reports : List (Report w)) : Prop where
  memory : after m (eventLog reports) = packMemory pub bits m (packCalls pub)
  calls : reports.length = stageCalls pub
  cost : RAMBuckets.cost Report.probes reports ≤ 4*stageCalls pub
  caps : ∀ r ∈ reports, r.probes ≤ 3 ∧ r.events.length < fuel
  path (bs : List (List Bool)) (rs : List (Report w)) :
    (runSegment (stageTable.instantiate w pub).program fuel (some 0) m bs = some rs ∧
      endState (some 0) rs = none) ↔ bs = List.replicate (stageCalls pub) [] ∧ rs = reports

private theorem pack_history {pub : Fin 5 → Word w} {bits : List Bool} {fuel : ℕ}
    (L : PackLayout pub bits) (m : Memory w) (hs : PackSource pub bits m) (hf : stageFuel ≤ fuel) :
    ∃ rs, PackHistory pub bits m fuel rs := by
  obtain ⟨rs, hm, hlen, hc, hr, hp⟩ := packStageSweep L m hs hf
  exact ⟨rs, hm, hlen, hc, hr, hp⟩

/-- Source readback in the successive input memories of the three native
packing stages, using only the copied header bits. -/
theorem preparedSources {advice : Bits a} {m : Memory w} {values : Fin t → Word ordW} {padding : ℕ}
    (L : PreparedLayout lp fp op raw t ordW)
    (copied : ∀ i : Fin a, m ((fp 0).val+i.val) = PrimedInputRAM.encodeBit w (advice i))
    (htape : List.ofFn advice = distribution w (fp 1).val raw values padding) :
    PackSource lp (lengthBits w raw) m ∧
    PackSource (rawOperands lp fp raw m) raw (published fp (lengthMemory lp raw m)) ∧
    PackSource op (ordinalBits values) (rawMemory lp fp raw m) := by
  let rp := rawOperands lp fp raw m
  let m₂ := published fp (lengthMemory lp raw m)
  let m₃ := rawMemory lp fp raw m
  have hbefore := L.adviceBeforeFrame
  have hfp := L.frameBeforePrefix
  have hraw := L.rawFits
  obtain ⟨hs₁, hs₂, hs₃⟩ := distribution_sources_of_copied copied lp rp op htape L.rawFits L.lengthSource
    (rawSourceAddress L m) L.ordinalSource
  have hsrc₂ : PackSource rp raw m₂ := by
    intro j hj
    rw [show m₂ _ = _ from before_frames L m ((rp 0).val+j) (by rw [rawSourceAddress L m]; omega), hs₂ j hj]
  have hsrc₃ : PackSource op (ordinalBits values) m₂ := by
    intro j hj
    rw [length_ordinalBits] at hj
    rw [show m₂ _ = _ from before_frames L m ((op 0).val+j) (by rw [L.ordinalSource]; omega),
      hs₃ j (by rwa [length_ordinalBits])]
  have hsrc₄ : PackSource op (ordinalBits values) m₃ := hsrc₃.after_other_bank rp raw (packCalls rp)
    (.inl (by rw [L.ordinalSource, length_ordinalBits]; change _ ≤ (fp 4).val; omega))
  exact ⟨hs₁, hsrc₂, hsrc₄⟩

/-- Source images, native reports and final data for the consecutive length,
frame, prefix and ordinal stages. The prefix machine sees its public words
through the just-published operand loader. -/
theorem prepareAdvice {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ} {g : Fin (2^(h+1))}
    {original m : Memory w} {values : Fin t → Word ordW} {padding fuel : ℕ}
    (L : PreparedLayout lp fp op raw t ordW)
    (image : LiveHeader.AdviceImage (d := d) hw advice cuts g (fp 0).val original m)
    (htape : List.ofFn advice = distribution w (fp 1).val raw values padding) (hf : 83 ≤ fuel) :
    let m₁ := lengthMemory lp raw m
    let m₂ := published fp m₁
    let rp := rawOperands lp fp raw m
    let m₃ := rawMemory lp fp raw m
    ∃ lrs rrs ors, PackHistory lp (lengthBits w raw) m fuel lrs ∧
      (∀ bs rep, execute (LiveEvaluatorAdviceFrames.template.instantiate w fp).program fuel
        ((LiveEvaluatorAdviceFrames.template.instantiate w fp).program.start 0) m₁ bs = some rep ↔
        bs = [] ∧ rep = ⟨events fp m₁, none⟩) ∧ after m₁ (events fp m₁) = m₂ ∧
      CompressorRecords.Frame.data (fp 3) m₂ = rp ∧ PackHistory rp raw m₂ fuel rrs ∧
      PackHistory op (ordinalBits values) m₃ fuel ors ∧
      PreparedImage lp fp op raw values m (preparedAdviceMemory lp fp op raw values m) := by
  intro m₁ m₂ rp m₃
  have hw' : 0 < w := by omega
  have hcap : actualLength fp m₁ ≤ fp 1 := (prepared_length L m).le.trans L.rawFits
  have hwidth : 0 < fp 2 := (L.frameWidth.symm ▸ hw' : 0 < (fp 2).val)
  have hclock : stageFuel ≤ fuel := by unfold stageFuel; omega
  obtain ⟨hs₁, hs₂, hs₃⟩ := preparedSources L image.copied htape
  obtain ⟨lrs, hlen⟩ := pack_history (lengthLayout L) m hs₁ hclock
  obtain ⟨rrs, hprefix⟩ := pack_history (rawLayout L m) m₂ hs₂ hclock
  obtain ⟨ors, horder⟩ := pack_history (orderLayout L values) m₃ hs₃ hclock
  refine ⟨lrs, rrs, ors, hlen, ?_, (execute_frames fp 0 m₁ hcap hwidth).2,
    (frameData fp m₁ hw' (frameFit L).le).1, hprefix, horder, prepared_image L values m⟩
  intro bs rep
  simpa only [hcap, hwidth, true_and] using execute_frames_iff fp 0 m₁ bs fuel hf rep

/-- All four dynamic operand loaders still read their complete frames after
both data banks have been packed. -/
theorem PreparedImage.frameData {values : Fin t → Word ordW} {m out : Memory w}
    (image : PreparedImage lp fp op raw values m out) (hf : (fp 3).val + 22 ≤ 2^w) :
    CompressorRecords.Frame.data (fp 3) out = prefixFrame fp (lengthMemory lp raw m) ∧
    CompressorRecords.Frame.data (fp 3+8) out = copyFrame fp (lengthMemory lp raw m) ∧
    CompressorRecords.Frame.data (fp 3+13) out = skeletonFrame fp (lengthMemory lp raw m) ∧
    CompressorRecords.Frame.data (fp 3+17) out = scatterFrame fp (lengthMemory lp raw m) := by
  have data {n : ℕ} (offset : ℕ) (h : offset + n ≤ 22) (j : Fin n) :
      CompressorRecords.Frame.data (fp 3 + (offset : Word w)) out j = out ((fp 3).val + offset + j.val) := by
    have hv : (fp 3 + (offset : Word w)).val = (fp 3).val+offset := by
      rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    rw [CompressorRecords.Frame.data_at _ _ (by rw [hv]; omega), hv]
  obtain ⟨hp, hc, hs, ho⟩ := image.frames
  refine ⟨funext (fun j => ?_), funext (fun j => ?_), funext (fun j => ?_), funext (fun j => ?_)⟩
  · exact (CompressorRecords.Frame.data_at _ _ (by omega) j).trans (hp j)
  · exact (data 8 (by decide) j).trans (hc j)
  · exact (data 13 (by decide) j).trans (hs j)
  · exact (data 17 (by decide) j).trans (ho j)

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI
