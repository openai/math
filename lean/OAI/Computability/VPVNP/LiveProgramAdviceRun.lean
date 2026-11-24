import OAI.Computability.VPVNP.LiveProgramAdviceSplice
import OAI.Computability.VPVNP.LiveProgramAdvicePackRun
import OAI.Computability.VPVNP.LiveDeterministicPaths
import OAI.Computability.VPVNP.LiveEvaluatorAdviceResources

/-!
# The four linked advice stages of the live program

Starting at the length-field stage, the linked machine packs the length,
publishes and validates the four operand frames, packs the evaluator's
actual prefix through its dynamic frame, and packs the ordinal table.
Each transfer writes only the reserved stage tag. The last report returns
cursor zero to the prefix-copy stage with the full prepared memory image.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open BurstRAM (Word Memory writeMemory)
open LiveStageLink (tagWord)
open LiveEvaluatorAdviceBanks
open LiveEvaluatorAdviceFrames (actualLength published frameData)
open scoped Fin.CommRing

/-- The evaluated public operand bank for packing the advised prefix length. -/
abbrev lp (c : Constants) (g : Geometry) := bank g (StageOperands.lengthPack c)
/-- The evaluated public operand bank for publishing the four midpoint input frames. -/
abbrev fp (c : Constants) (g : Geometry) := bank g (StageOperands.adviceFrames c)
/-- The evaluated public operand bank for packing the advised label order. -/
abbrev op (c : Constants) (g : Geometry) := bank g (StageOperands.orderPack c)

/-- Number of burst calls across length packing, the single frame publication, active-prefix
packing and order packing. -/
def calls (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) :=
  stageCalls (lp c g) + 1 + stageCalls (rawOperands (lp c g) (fp c g) raw m) + stageCalls (op c g)

/-- The prepared advice memory with the outer tag set to enter prefix copying. -/
def finalMemory (c : Constants) (g : Geometry) (lit : LiteralPrefix) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g))) (m : Memory g.w) :=
  writeMemory (preparedAdviceMemory (lp c g) (fp c g) (op c g) raw values m) (tagAddr g lit)
    (tagWord g.w Stage.prefixCopy)

/-- Upper bound on calls plus external probes for the four advice preparation stages, including
the fixed frame-publication charge. -/
def work (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) :=
  6*stageCalls (lp c g) + 23 + 11*stageCalls (rawOperands (lp c g) (fp c g) raw m) +
    6*stageCalls (op c g)

/-- Every successful execution of the given number of choice-free calls from cursor zero has
total calls-plus-probes cost at most the supplied limit. -/
def CostLimit {w : ℕ} {C : Type*} (P : BurstRAM.Program w C) (fuel calls : ℕ)
    (m : Memory w) (cost : ℕ) : Prop :=
  ∀ logs, BurstRAM.runSegment P fuel (some 0) m (List.replicate calls []) = some logs →
    RAMBuckets.cost BurstRAM.Report.probes logs ≤ cost

private theorem reportCost {w q : ℕ} (logs : List (BurstRAM.Report w))
    (hp : ∀ r ∈ logs, r.probes ≤ q) : RAMBuckets.cost BurstRAM.Report.probes logs ≤ (q+1)*logs.length := by
  induction logs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    have h := hp r (by simp)
    have t := ih (fun r hr => hp r (List.mem_cons_of_mem _ hr))
    simp only [RAMBuckets.cost, List.length_cons, Nat.mul_succ]; omega

theorem returning_cost {w : ℕ} {C : Type*} {P : BurstRAM.Program w C} {f n q} {m u : Memory w}
    (h : Returning P f n q m u) : CostLimit P f n m ((q+1)*n) := by
  obtain ⟨logs,hr,-,-,hl,hb⟩ := h
  intro rs hrun
  obtain rfl := Option.some.inj (hr.symm.trans hrun)
  rw [← hl]
  exact reportCost _ (fun r h => (hb r h).1)

theorem costLimit_append {w : ℕ} {C : Type*} {P : BurstRAM.Program w C} {f a b qa qb x y}
    {m u v : Memory w} (ha : Returning P f a qa m u) (hb : Returning P f b qb u v)
    (cx : CostLimit P f a m x) (cy : CostLimit P f b u y) :
    CostLimit P f (a+b) m (x+y) := by
  obtain ⟨xs,hx,hxe,hxm,-,-⟩ := ha
  obtain ⟨ys,hy,-,-,-,-⟩ := hb
  intro logs hr
  rw [List.replicate_add, PrimedSchedule.runSegment_append, hx] at hr
  have he : xs++ys = logs := by simpa only [Option.bind_some,hxe,hxm,hy,Option.map_some,Option.some.injEq] using hr
  rw [← he, RAMBuckets.cost_append]
  exact Nat.add_le_add (cx _ hx) (cy _ hy)

/-- Execute the complete native advice prefix in the shared machine with its
real tag writes and repeated fetches of the dynamic prefix-packer frame. -/
theorem fourStages_budget (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (m : Memory g.w) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g)))
    {a padding : ℕ} (advice : Fin a → Bool)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (copied : ∀ i : Fin a, m (((fp c g) 0).val+i.val) = PrimedInputRAM.encodeBit g.w (advice i))
    (htape : List.ofFn advice = distribution g.w ((fp c g) 1).val raw values padding)
    (hlimit : (Layout.shadow c).eval g < 2^g.w) {cap : ℕ} (hf : 130 ≤ cap)
    (htag : m (tagAddr g lit).val = tagWord g.w Stage.prefixLength) :
    Returning (machine c p O g lit).program cap (calls c g raw m) 22 m (finalMemory c g lit raw values m) ∧
      CostLimit (machine c p O g lit).program cap (calls c g raw m) m (work c g raw m) := by
  let lenPub := lp c g
  let framePub := fp c g
  let ordPub := op c g
  let rawPub := rawOperands lenPub framePub raw m
  let P := (machine c p O g lit).program
  let tag := tagAddr g lit
  let tagged (mem : Memory g.w) (s : Stage) := writeMemory mem tag (tagWord g.w s)
  let m₁ := lengthMemory lenPub raw m
  let m₂ := published framePub m₁
  let m₃ := rawMemory lenPub framePub raw m
  let m₄ := preparedAdviceMemory lenPub framePub ordPub raw values m
  have htag' (mem : Memory g.w) (s : Stage) : tagged mem s tag.val = tagWord g.w s := by
    simp [tagged,writeMemory]
  have hsrc : tag.val < (framePub 0).val := tag_before_advice c g lit hlimit
  have hframe : tag.val < (framePub 3).val := by
    have h := L.adviceBeforeFrame
    change (framePub 0).val + g.w + (framePub 1).val + _ ≤ (framePub 3).val at h
    omega
  have hbefore : (framePub 3).val + 23 ≤ (framePub 4).val := L.frameBeforePrefix
  have hroom : (framePub 3).val+22 < 2^g.w := by have := (framePub 4).isLt; omega
  have hw : 0 < g.w := by have := L.width; omega
  have hfit : 21 ≤ 2^g.w := by omega
  obtain ⟨hlength,hraw,hord⟩ := preparedSources L copied htape
  have r1 : Returning P cap (stageCalls lenPub) 5 m (tagged m₁ Stage.adviceFrames) :=
    AdvicePackRun.linkedPack_direct (c := c) (p := p) (O := O) (s := Stage.prefixLength)
      (dest := Stage.adviceFrames) (g := g) (lit := lit) (lengthLayout L) m hlength rfl hfit
      (by omega) htag (.inl (show tag.val < (lenPub 1).val by have h : (lenPub 1).val = (framePub 3).val+22 := L.lengthDest; omega))
      (fun _ _ _ => rfl)
  have hcap : actualLength framePub (tagged m₁ Stage.adviceFrames) ≤ framePub 1 := by
    rw [actualLength_write_tag framePub m₁ tag _ hframe hroom]
    exact (prepared_length L m).le.trans L.rawFits
  have hpub : published framePub (tagged m₁ Stage.adviceFrames) = tagged m₂ Stage.adviceFrames :=
    published_write_tag framePub m₁ tag _ hframe hw hroom
  have r2 : Returning P cap 1 22 (tagged m₁ Stage.adviceFrames) (tagged m₂ Stage.prefixPack) := by
    have hr := returning_frames c p O g lit (tagged m₁ Stage.adviceFrames) cap hfit hf
      (htag' ..) hcap (show 0 < (framePub 2).val by rw [L.frameWidth]; exact hw)
    change Returning P cap 1 22 _ (tagged (published framePub _) Stage.prefixPack) at hr
    simpa only [hpub,tagged,write_tag_twice] using hr
  have hbase : (rawPub 0).val = (framePub 0).val+g.w := by
    change (framePub 0 + framePub 2).val = _
    rw [Fin.val_add,L.frameWidth,Nat.mod_eq_of_lt (by
      have h : (framePub 0).val+g.w+(framePub 1).val+_ ≤ (framePub 3).val := L.adviceBeforeFrame
      have := (framePub 3).isLt; omega)]
  have hrSrc : PackSource rawPub raw (tagged m₂ Stage.prefixPack) :=
    (packSource_write_tag rawPub raw m₂ tag _ (by omega)).mpr hraw
  have hrawDest : rawPub 1 = framePub 4 := rfl
  have outside (j : Fin 5) : (framePub 3 + Fin.ofNat (2^g.w) j.val).val < (rawPub 1).val := by
    rw [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by have := j.isLt; omega),hrawDest]
    have := j.isLt; omega
  have hdata : CompressorRecords.Frame.data (framePub 3) (tagged m₂ Stage.prefixPack) = rawPub := by
    change CompressorRecords.Frame.data (framePub 3) (tagged m₂ Stage.prefixPack) =
      LiveEvaluatorAdviceFrames.prefixFrame framePub m₁
    rw [← (frameData framePub m₁ hw hroom.le).1]
    funext j
    have hsum : (framePub 3 + (j.val : Word g.w)).val = (framePub 3).val+j.val := by
      rw [Fin.val_add,Fin.val_natCast,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    simp [CompressorRecords.Frame.data,tagged,writeMemory,hsum,show (framePub 3).val+j.val ≠ tag.val by omega,m₂]
  have r3 : Returning P cap (stageCalls rawPub) 10 (tagged m₂ Stage.prefixPack) (tagged m₃ Stage.orderPack) := by
    have hr := AdvicePackRun.linkedPack_framed (c := c) (p := p) (O := O) (s := Stage.prefixPack)
      (dest := Stage.orderPack) (g := g) (lit := lit) (rawLayout L m) (tagged m₂ Stage.prefixPack) hrSrc rfl hfit
      (show 100 ≤ cap by omega) (htag' ..) (.inl (show tag.val < (rawPub 1).val by rw [hrawDest]; omega)) (framePub 3) hdata
      (fun j => Or.inl (outside j)) (fun _ _ _ => rfl)
    change Returning P cap (stageCalls rawPub) 10 _ (tagged (packMemory rawPub raw _ _) Stage.orderPack) at hr
    change Returning P cap _ 10 _ (tagged (packMemory rawPub raw m₂ (packCalls rawPub)) Stage.orderPack)
    simpa only [tagged,packMemory_write_tag _ _ _ _ _ _ (show tag.val < (rawPub 1).val by rw [hrawDest]; omega),
      write_tag_twice] using hr
  have hOrderSrc : tag.val < (ordPub 0).val := by
    have h : (ordPub 0).val = (framePub 0).val+g.w+(framePub 1).val := L.ordinalSource
    omega
  have hOrderDst : tag.val < (ordPub 1).val := by
    have h : (framePub 4).val + (raw.length ⌈/⌉ g.w) ≤ (ordPub 1).val := L.prefixBeforeOrder
    omega
  have r4 : Returning P cap (stageCalls ordPub) 5 (tagged m₃ Stage.orderPack) (tagged m₄ Stage.prefixCopy) := by
    have hs := (packSource_write_tag ordPub (ordinalBits values) m₃ tag (tagWord g.w Stage.orderPack) hOrderSrc).mpr hord
    have hr := AdvicePackRun.linkedPack_direct (c := c) (p := p) (O := O) (s := Stage.orderPack)
      (dest := Stage.prefixCopy) (g := g) (lit := lit) (orderLayout L values) (tagged m₃ Stage.orderPack) hs
      rfl hfit (show 80 ≤ cap by omega) (htag' ..) (.inl hOrderDst) (fun _ _ _ => rfl)
    change Returning P cap (stageCalls ordPub) 5 _ (tagged (packMemory ordPub (ordinalBits values) _ _) _) at hr
    change Returning P cap _ 5 _ (tagged (packMemory ordPub (ordinalBits values) m₃ (packCalls ordPub)) Stage.prefixCopy)
    simpa only [tagged,packMemory_write_tag _ _ _ _ _ _ hOrderDst,write_tag_twice] using hr
  have r12 := returning_append r1 r2
  have r123 := returning_append r12 r3
  have c12 := costLimit_append r1 r2 (returning_cost r1) (returning_cost r2)
  have c123 := costLimit_append r12 r3 c12 (returning_cost r3)
  exact ⟨returning_append r123 r4,costLimit_append r123 r4 c123 (returning_cost r4)⟩

/-- Returning execution and final image of the four stages. -/
theorem fourStages (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (m : Memory g.w) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g)))
    {a padding : ℕ} (advice : Fin a → Bool)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (copied : ∀ i : Fin a, m (((fp c g) 0).val+i.val) = PrimedInputRAM.encodeBit g.w (advice i))
    (htape : List.ofFn advice = distribution g.w ((fp c g) 1).val raw values padding)
    (hlimit : (Layout.shadow c).eval g < 2^g.w) {cap : ℕ} (hf : 130 ≤ cap)
    (htag : m (tagAddr g lit).val = tagWord g.w Stage.prefixLength) :
    Returning (machine c p O g lit).program cap (calls c g raw m) 22 m (finalMemory c g lit raw values m) :=
  (fourStages_budget c p O g lit m raw values advice L copied htape hlimit hf htag).1


/-- The end of the four-stage run retains all prepared banks. Its only extra
write is the prefix-copy tag, so the frame statement compares with the
initial memory carrying that same tag. -/
theorem finalImage (c : Constants) (g : Geometry) (lit : LiteralPrefix) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g))) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w) :
    PreparedImage (lp c g) (fp c g) (op c g) raw values
      (writeMemory m (tagAddr g lit) (tagWord g.w Stage.prefixCopy)) (finalMemory c g lit raw values m) := by
  let tag := tagAddr g lit
  let v := tagWord g.w Stage.prefixCopy
  let lenPub := lp c g
  let framePub := fp c g
  let ordPub := op c g
  let rp := rawOperands lenPub framePub raw m
  have ht : tag.val < (framePub 0).val := tag_before_advice c g lit hlimit
  have hsrc : (framePub 0).val+g.w+(framePub 1).val+_ ≤ (framePub 3).val := L.adviceBeforeFrame
  have hf : (framePub 3).val+23 ≤ (framePub 4).val := L.frameBeforePrefix
  have hfit : (framePub 3).val+22 < 2^g.w := by have := (framePub 4).isLt; omega
  have htFrame : tag.val < (framePub 3).val := by omega
  have hw : 0 < g.w := by have := L.width; omega
  have htLen : tag.val < (lenPub 1).val := by have h : (lenPub 1).val = (framePub 3).val+22 := L.lengthDest; omega
  have htOrd : tag.val < (ordPub 1).val := by
    have h : (framePub 4).val + (raw.length ⌈/⌉ g.w) ≤ (ordPub 1).val := L.prefixBeforeOrder
    omega
  have hm₁ : lengthMemory lenPub raw (writeMemory m tag v) = writeMemory (lengthMemory lenPub raw m) tag v :=
    packMemory_write_tag lenPub _ m tag v _ htLen
  have hrp : rawOperands lenPub framePub raw (writeMemory m tag v) = rp := by
    rw [rawOperands,hm₁,prefixFrame_write_tag framePub _ tag v htFrame hfit]
    rfl
  have hm₃ : rawMemory lenPub framePub raw (writeMemory m tag v) =
      writeMemory (rawMemory lenPub framePub raw m) tag v := by
    simp only [rawMemory,hrp,hm₁,published_write_tag framePub _ tag v htFrame hw hfit]
    exact packMemory_write_tag rp raw _ tag v _ (show tag.val < (framePub 4).val by omega)
  have hm₄ : preparedAdviceMemory lenPub framePub ordPub raw values (writeMemory m tag v) =
      finalMemory c g lit raw values m := by
    rw [preparedAdviceMemory,hm₃,packMemory_write_tag ordPub _ _ tag v _ htOrd]
    rfl
  exact hm₄ ▸ prepared_image L values (writeMemory m tag v)

/-- These four stages give an equivalence on all accepting choice tapes for any
report cap on the continuation, including caps on the concatenated group. -/
theorem fourStages_paths {c p O g lit m raw values cap}
    (h : Returning (machine c p O g lit).program cap (calls c g raw m) 22 m
      (finalMemory c g lit raw values m)) (within : List (BurstRAM.Report g.w) → Prop) :
    ∃ logs, Nonempty (PathsFrom (machine c p O g lit).program cap (some 0)
      (finalMemory c g lit raw values m) (fun rs => within (logs++rs)) ≃
      PathsFrom (machine c p O g lit).program cap (some 0) m within) ∧
      logs.length = calls c g raw m ∧ ∀ r ∈ logs, r.probes ≤ 22 ∧ r.events.length < cap := by
  obtain ⟨logs,hx,he,hm,hl,hb⟩ := h
  have hpath := emptySegmentEquiv hx within
  rw [he,hm] at hpath
  exact ⟨logs,⟨hpath⟩,hl,hb⟩

/-- The canonical call counts use the actual raw prefix length and the table's
encoded ordinal width, including the empty-bank return when there are no rows. -/
theorem callCounts (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g))) :
    stageCalls (lp c g) = g.w+1 ∧
    stageCalls (rawOperands (lp c g) (fp c g) raw m) = LiveEvaluatorAdviceResources.prefixCalls raw.length g.w ∧
    stageCalls (op c g) = LiveEvaluatorAdviceResources.orderCalls (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)) := by
  have hwidth : (rawOperands (lp c g) (fp c g) raw m 2).val = g.w := L.frameWidth
  simp only [stageCalls,packCalls,LiveEvaluatorAdviceResources.prefixCalls,LiveEvaluatorAdviceResources.orderCalls,
    L.lengthWidth,L.lengthRows,rawOperands_rows L m,hwidth,L.ordinalRows,L.ordinalWidth,Nat.one_mul]
  simp

theorem work_eq_setupCost (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g))) :
    work c g raw m = LiveEvaluatorAdviceResources.setupCost g.w raw.length
      (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)) := by
  obtain ⟨hl,hr,ho⟩ := callCounts c g raw m L
  rw [work,hl,hr,ho,LiveEvaluatorAdviceResources.setupCost]
  omega

end LiveProgram.Advice

end VPVNP
end Computability
end OAI
