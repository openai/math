import OAI.Computability.VPVNP.LiveHeaderProgramRun
import OAI.Computability.VPVNP.LiveGroupModeInput
import OAI.Computability.VPVNP.PrimedCounterCallPaths

/-!
# Executions of the scalar stages of the live header program

These stages run once and end with an accepting exit to the next stage. They
read the summary words produced by the index scan and write only their own
specified outputs. Every local operand is the one wired in the complete table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderWidths
open LiveHeaderDescriptors PrimedInputRAM

variable {w : ℕ}

/-- A single accepted call to the relocated stage, with its real memory effect. -/
def SingleRun (s : Sizes) (base : ℕ) (st : Stage) (before final : Memory w) : Prop :=
  let P := ((stageTemplate st).2.instantiate w (rowData w s base st)).program
  ∃ es, execute P 40 (P.start 0) before [] = some ⟨es,none⟩ ∧ after before es = final ∧
    es.length < 40 ∧ countProbes es ≤ probes st ∧ choiceBits es = []

/-- The first sixteen words of the selected header stage's public row, used by its scalar
worker. -/
def scalarPub (w : ℕ) (s : Sizes) (base : ℕ) (st : Stage) : Fin 16 → Word w :=
  rowData w s base st ∘ includeFin (by decide)

theorem single_of_flow (s : Sizes) (base : ℕ) (st : Stage) (a : Flow 48 16)
    (hc : stageTemplate st = entry (a.template none)) (m : Memory w) {es out final}
    (hr : Flow.Exec (scalarPub w s base st) 0 a (fun _ => 0) m es out final)
    (hf : es.length < 40) (hp : countProbes es ≤ probes st) (hb : choiceBits es = []) :
    SingleRun s base st m final := by
  unfold SingleRun
  rw [hc]
  refine ⟨es, ?_, PrimedCounter.Call.exec_memory hr, hf, hp, hb⟩
  rw [entry_start]
  exact (Flow.template_execute_iff a none (scalarPub w s base st) 0 (fun _ => 0) (fun _ => 0) m 40 [] _).mpr
    ⟨out,final,hr,rfl,hf,hb⟩

/-- The four scratch words consumed after index scanning. -/
structure Summary (s : Sizes) (base i : ℕ) (m : Memory w) : Prop where
  high : (m (highAddr s base)).val = Nat.log 2 i
  count : (m (populationAddr s base)).val = (LiveHeader.prefixOnes i (s.h+2)).card
  singleton : (LiveHeader.prefixOnes i (s.h+2)).card = 1 ↔ i = 2 ^ Nat.log 2 i
  low : m (indexBase base) = encodeBit w (i.testBit 0)

/-- The public and scratch words used by the width and phase stages. -/
structure ScalarFit (w : ℕ) (s : Sizes) (base : ℕ) : Prop where
  height : s.h+1 < 2^w
  delta : s.delta < 2^w
  cut : (s.h+1)*s.delta < 2^w
  address : limit s base ≤ 2^w

private theorem highFit {s : Sizes} {base : ℕ} (fit : ScalarFit w s base) : highAddr s base < 2^w := by
  have h := fit.address
  rw [limit_eq] at h
  unfold highAddr indexBase
  omega

private theorem populationFit {s : Sizes} {base : ℕ} (fit : ScalarFit w s base) : populationAddr s base < 2^w := by
  have h := fit.address
  rw [limit_eq] at h
  unfold populationAddr highAddr indexBase
  omega

private theorem indexFit {s : Sizes} {base : ℕ} (fit : ScalarFit w s base) : indexBase base < 2^w := by
  have h := highFit fit
  unfold highAddr at h
  omega

private theorem wordAt (n : ℕ) (hn : n < 2^w) : (Fin.ofNat (2^w) n).val = n := Nat.mod_eq_of_lt hn

/-- Every width stage has a successful source call. All requested widths
have their exact clamped value, including both incident cuts in the tail. -/
theorem width_run (s : Sizes) (base i : ℕ) (slot : Slot) (m : Memory w) (fit : ScalarFit w s base)
    (hi : 0 < i) (hi' : i ≤ 2^(s.h+1)) (summary : Summary s base i m) :
    ∃ v : Word w, SingleRun s base (.width slot) m (writeMemory m (Fin.ofNat _ (widthAddr base slot)) v) ∧
      (Needed s.h i slot → v.val = CutSchedule.width (s.h+1) s.delta (index i slot)) := by
  let pub := scalarPub w s base (.width slot)
  have finish (v : Word w) {out} (hr : Flow.Exec pub 0 (WidthCode.block widthSlots slot) (fun _ => 0) m
      (WidthCode.events pub widthSlots m slot v) out (writeMemory m (pub widthSlots.outputAddress) v)) :
      SingleRun s base (.width slot) m (writeMemory m (Fin.ofNat _ (widthAddr base slot)) v) := by
    obtain ⟨hp,hb,hl⟩ := WidthCode.event_cost pub widthSlots m slot v
    exact single_of_flow s base (.width slot) _ rfl _ hr (by omega) hp.le hb
  by_cases need : Needed s.h i slot
  · have hh : (pub widthSlots.height).val = s.h+1 := wordAt _ fit.height
    have hd : (pub widthSlots.delta).val = s.delta := wordAt _ fit.delta
    have hk : (pub widthSlots.highestAddress).val = highAddr s base := wordAt _ (highFit fit)
    have hc : (pub widthSlots.populationAddress).val = populationAddr s base := wordAt _ (populationFit fit)
    obtain ⟨out,hr,hv⟩ := WidthCode.needed_exec pub widthSlots 0 m (fun _ => 0) slot s.h s.delta i
      _ hi hi' need summary.singleton hh hd (hk ▸ summary.high) (hc ▸ summary.count) fit.cut
    exact ⟨_, finish _ hr, fun _ => hv⟩
  · obtain ⟨v,out,hr⟩ := WidthCode.unconditional_exec pub widthSlots 0 m (fun _ => 0) slot
    exact ⟨v,finish _ hr,fun h => (need h).elim⟩

theorem flag_run (s : Sizes) (base i : ℕ) (flag : Flag) (m : Memory w) (fit : ScalarFit w s base)
    (hi : 0 < i) (hi' : i ≤ 2^(s.h+1)) (summary : Summary s base i m) :
    SingleRun s base (.flag flag) m (writeMemory m (Fin.ofNat _ (flagAddr base flag))
      (encodeBit w (decide (flag.holds s.h i)))) := by
  let pub := scalarPub w s base (.flag flag)
  have hh : (pub widthSlots.height).val = s.h+1 := wordAt _ fit.height
  have hk : (pub widthSlots.highestAddress).val = highAddr s base := wordAt _ (highFit fit)
  have hc : (pub widthSlots.populationAddress).val = populationAddr s base := wordAt _ (populationFit fit)
  obtain ⟨es,out,hr,hp,hb,hl⟩ := PhaseCode.block_exec pub widthSlots 0 m (fun _ => 0) s.h i _
    flag hi hi' summary.singleton hh (hk ▸ summary.high) (hc ▸ summary.count)
  exact single_of_flow s base (.flag flag) _ rfl _ hr (by omega) hp.le hb

theorem firstTail_run (hw : 2 ≤ w) (s : Sizes) (base i : ℕ) (m : Memory w) (fit : ScalarFit w s base)
    (hi : 0 < i) (hi' : i ≤ 2^(s.h+1)) (summary : Summary s base i m) :
    SingleRun s base .firstTail m (writeMemory m (Fin.ofNat _ (firstTailAddr base))
      (encodeBit w (decide (i = 2^s.h+1)))) := by
  let pub := scalarPub w s base .firstTail
  have hh : (pub widthSlots.height).val = s.h+1 := wordAt _ fit.height
  have hk : (pub widthSlots.highestAddress).val = highAddr s base := wordAt _ (highFit fit)
  have hc : (pub widthSlots.populationAddress).val = populationAddr s base := wordAt _ (populationFit fit)
  have hlow : (pub 5).val = indexBase base := wordAt _ (indexFit fit)
  obtain ⟨es,out,hr,hp,hb,hl⟩ := PhaseCode.firstTail_exec hw pub widthSlots 5 0 m (fun _ => 0)
    s.h i hi hi' hh (hk ▸ summary.high) (hc ▸ summary.count) (hlow ▸ summary.low)
  exact single_of_flow s base .firstTail _ rfl _ hr (by omega) hp.le hb

private theorem scalarAddrFit {s : Sizes} {base addr : ℕ} (fit : ScalarFit w s base)
    (ha : addr < indexBase base) : addr < 2^w := ha.trans (indexFit fit)

theorem mode_run (s : Sizes) (base d : ℕ) {hw : 4 ≤ w} (advice : CutSchedule.Bits s.advice)
    (cuts : ChainAssignments.AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (m : Memory w)
    (fit : ScalarFit w s base) (headers : LiveHeader.SiteHeaders d hw advice cuts g m)
    (left : (m (widthAddr base .liveLeft)).val = LiveHeader.incidentWidth (Δ := s.delta) .left g)
    (right : (m (widthAddr base .liveRight)).val = LiveHeader.incidentWidth (Δ := s.delta) .right g)
    (flag : m (flagAddr base .firstHalf) = encodeBit w (LiveHeader.firstHalfFlag g))
    (tag : LiveHeader.Mode.Tag) (hsel : LiveHeader.physicalTag cuts g = some tag) :
    SingleRun s base .mode m (writeMemory m (Fin.ofNat _ (tagAddr base)) (Fin.ofNat _ tag.code.val)) := by
  let pub := scalarPub w s base .mode
  let zero : Fin (2^d) := ⟨0, Nat.two_pow_pos _⟩
  have hl : (pub 0).val = widthAddr base .liveLeft := wordAt (widthAddr base .liveLeft) (scalarAddrFit fit (by dsimp [widthAddr,indexBase]; omega))
  have hr : (pub 1).val = widthAddr base .liveRight := wordAt (widthAddr base .liveRight) (scalarAddrFit fit (by dsimp [widthAddr,indexBase]; omega))
  have hf : (pub 2).val = flagAddr base .firstHalf := wordAt (flagAddr base .firstHalf) (scalarAddrFit fit (by dsimp [flagAddr,indexBase]; omega))
  obtain ⟨es,out,he,_,ht,hp,hb,_⟩ := LiveHeader.Mode.exec_selected pub 0 (fun _ => 0) m hw
    (ChainAssignments.physicalHeader advice cuts g zero) (LiveHeader.firstHalfFlag g) tag (headers zero)
    (hf ▸ flag) (by rw [hl,hr,left,right]; exact hsel)
  exact single_of_flow s base .mode _ rfl _ he (by omega) hp.le hb

/-- Each descriptor stage publishes the exact interval to its immediately
following scan. The scratch words are reused between successive fields. -/
theorem descriptor_run (s : Sizes) (base : ℕ) (side : Side) (f : Field) (m : Memory w)
    (hw : 0 < w) (fit : ScalarFit w s base) (W tag : ℕ) (half firstTail : Bool)
    (hW : (m (widthAddr base (if side = .left then .liveLeft else .liveRight))).val = W)
    (ht : (m (tagAddr base)).val = tag)
    (hh : m (flagAddr base .firstHalf) = encodeBit w half)
    (hft : m (firstTailAddr base) = encodeBit w firstTail)
    (hefit : 1+s.e ≤ s.delta) (hcfit : 1+s.config ≤ s.delta) (hblock : W = 0 ∨ s.delta ≤ W) :
    let iv := span (shape side W tag half firstTail) W s.delta s.e s.config f
    ∃ o l : Word w, o.val = iv.1 ∧ l.val = iv.2 ∧
      SingleRun s base (.descriptor side f) m (writeMemory (writeMemory m (Fin.ofNat _ (offsetAddr base)) o)
        (Fin.ofNat _ (countAddr base)) l) := by
  let pub := scalarPub w s base (.descriptor side f)
  have hwaddr : (pub descriptorSlots.widthAddress).val = widthAddr base
      (if side = .left then .liveLeft else .liveRight) := wordAt (widthAddr base (if side = .left then .liveLeft else .liveRight)) (scalarAddrFit fit (by
        cases side <;> simp [widthAddr,indexBase]))
  have htaddr : (pub descriptorSlots.tagAddress).val = tagAddr base :=
    wordAt (tagAddr base) (scalarAddrFit fit (by dsimp [tagAddr,indexBase]; omega))
  have hhaddr : (pub descriptorSlots.firstHalfAddress).val = flagAddr base .firstHalf :=
    wordAt (flagAddr base .firstHalf) (scalarAddrFit fit (by dsimp [flagAddr,indexBase]; omega))
  have hfaddr : (pub descriptorSlots.firstTailAddress).val = firstTailAddr base :=
    wordAt (firstTailAddr base) (scalarAddrFit fit (by dsimp [firstTailAddr,indexBase]; omega))
  obtain ⟨out,o,l,hr,ho,hl⟩ := Native.block_exec hw pub descriptorSlots 0 m (fun _ => 0) side f W tag
    s.delta s.e s.config half firstTail (hwaddr ▸ hW) (htaddr ▸ ht) (hhaddr ▸ hh) (hfaddr ▸ hft)
    (wordAt s.delta fit.delta) (wordAt s.e (by have := fit.delta; omega)) (wordAt s.config (by have := fit.delta; omega))
    hefit hcfit hblock
  obtain ⟨hp,hb,hLen⟩ := Native.event_cost pub descriptorSlots m o l
  exact ⟨o,l,ho,hl,single_of_flow s base (.descriptor side f) _ rfl _ hr (by omega) hp.le hb⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
