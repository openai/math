import OAI.Computability.VPVNP.LiveHeaderBootstrap
import OAI.Computability.VPVNP.LiveHeaderMetadata
import OAI.Computability.VPVNP.LiveHeaderPrimedStages

/-!
# The native header prefix before incident-field extraction

Index and advice scans, all scalar dispatches, and both primed-index stages
run on a single physical memory. The prefix leaves the field buffers zero
and the processor headers intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderWidths LiveHeaderDescriptors
open LiveHeader PrimedInputRAM ChainAssignments

variable {w d : ℕ}

/-- The scalar field's position in the eleven-stage metadata sequence. -/
def Metadata.ordinal : Metadata.Field → Fin 11
  | .width .liveLeft => 0 | .width .liveRight => 1 | .width .primedLeft => 2
  | .width .primedMiddle => 3 | .width .primedRight => 4
  | .flag .first => 5 | .flag .middle => 6 | .flag .firstHalf => 7 | .flag .last => 8
  | .firstTail => 9 | .mode => 10

private theorem metadata_read {s : Sizes} {base i : ℕ} {tag : Mode.Tag} {m out : Memory w}
    (img : Metadata.Image s base i tag m out 11) (f : Metadata.Field) :
    Metadata.Correct s i tag f (out (f.address base)) := by
  have h := img.readback (Metadata.ordinal f) (Metadata.ordinal f).isLt
  cases f with
  | width slot => cases slot <;> exact h
  | flag flag => cases flag <;> exact h
  | firstTail | mode => exact h

/-- Values at the interface from the primed-index phase to the field scans. -/
structure Prepared (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (out : Memory w) : Prop where
  headers : SiteHeaders d hw advice cuts g out
  scalars : ∀ f : Metadata.Field, Metadata.Correct s (g.val+1) tag f (out (f.address base))
  adviceWords : ∀ j : Fin s.advice, out (adviceBase s base+j.val) = encodeBit w (advice j)
  primedLeft : ∀ j < s.h+2, out (leftIndexBase s base+j) = encodeBit w ((2*(g.val+1)-1).testBit j)
  primedRight : ∀ j < s.h+2, out (rightIndexBase s base+j) = encodeBit w ((2*(g.val+1)).testBit j)
  zero : ∀ a, exteriorBase s base .left ≤ a → out a = 0

private theorem scalar_range (base : ℕ) (f : Metadata.Field) :
    base < f.address base ∧ f.address base < borrowAddr base := by
  cases f with
  | width slot => cases slot <;> dsimp [Metadata.Field.address,widthAddr,borrowAddr] <;> omega
  | flag flag => cases flag <;> dsimp [Metadata.Field.address,flagAddr,borrowAddr] <;> omega
  | firstTail | mode => dsimp [Metadata.Field.address,tagAddr,firstTailAddr,borrowAddr]; omega

/-- The first fifteen actual stages, with the exact state seen by the
incoming and outgoing field descriptor scans. -/
theorem prepared_prefix (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag)
    (hsel : physicalTag cuts g = some tag) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (scratch : 2^d ≤ base) (fit : limit s base ≤ 2^w) :
    ∃ xs out, StagePrefix s base (some (⟨0,by decide⟩ : StageId)) (physicalMemory (d := d) hw advice cuts g)
      xs (some (⟨15,by decide⟩ : StageId)) out ∧ (∀ x ∈ xs, x.Good s) ∧
      Prepared (d := d) s base hw advice cuts g tag out := by
  obtain ⟨a,ma,ha,ga,ready⟩ := index_advice_prefix s base hw advice cuts g indices adv scratch fit
  obtain ⟨b,mb,hb,gb,im⟩ := Metadata.run_prefix s base d advice cuts g tag (scalarFit_of_limit fit) scratch
    ma ready.headers ready.summary 11 le_rfl (fun _ => hsel)
  have indexInput (j : ℕ) (hj : j < s.h+1) : mb (indexBase base+j) = encodeBit w ((g.val+1).testBit j) :=
    (im.frame _ (Or.inr (by dsimp [indexBase]; omega))).trans (ready.index j (by omega))
  obtain ⟨c,out,hc,gc,primed⟩ := PrimedStages.primed_prefix s base fit g mb indexInput
  have hbase : (Fin.ofNat (2^w) base).val = base := by
    apply Nat.mod_eq_of_lt
    rw [limit_eq] at fit
    omega
  have keep (a : ℕ) (ht : a ≠ base) (hr : a ≠ borrowAddr base)
      (hl : a < leftIndexBase s base ∨ leftIndexBase s base+(s.h+2) ≤ a)
      (hr' : a < rightIndexBase s base ∨ rightIndexBase s base+(s.h+2) ≤ a) : out a = mb a := by
    rw [primed.frame a hr hl hr']
    simp only [LiveStageLink.transferMemory,writeMemory,hbase,ht,↓reduceIte]
  refine ⟨(a++b)++c,out,(ha.append hb).append hc,?_,?_,?_,?_,primed.left,primed.right,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact ga x hx
      · exact gb x hx
    · exact gc x hx
  · intro v
    have hv := v.isLt.trans_le scratch
    rw [keep _ hv.ne (by dsimp [borrowAddr]; omega) (Or.inl (by
      dsimp [leftIndexBase,populationAddr,highAddr,indexBase]; omega)) (Or.inl (by
      dsimp [rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega))]
    exact (im.frame _ (Or.inl hv)).trans (ready.headers v)
  · intro f
    have ⟨hl,hr⟩ := scalar_range base f
    have hL : f.address base < leftIndexBase s base := by
      dsimp [borrowAddr] at hr
      dsimp [leftIndexBase,populationAddr,highAddr,indexBase]
      omega
    have hR : f.address base < rightIndexBase s base := by dsimp [rightIndexBase]; omega
    rw [keep _ hl.ne' hr.ne (Or.inl hL) (Or.inl hR)]
    exact metadata_read im f
  · intro j
    let atAdvice := adviceBase s base+j.val
    have hright : rightIndexBase s base+(s.h+2) ≤ atAdvice := by dsimp [atAdvice,adviceBase]; omega
    have hleft : leftIndexBase s base+(s.h+2) ≤ atAdvice := by dsimp [rightIndexBase] at hright; omega
    have hhi : base+14 < atAdvice := by dsimp [leftIndexBase,populationAddr,highAddr,indexBase] at hleft; omega
    change out atAdvice = _
    rw [keep _ (by omega) (by dsimp [borrowAddr]; omega) (Or.inr hleft) (Or.inr hright)]
    exact (im.frame _ (Or.inr (by omega))).trans (ready.adviceWords j)
  · intro a ha
    have hright : rightIndexBase s base+(s.h+2) ≤ a := by dsimp [exteriorBase,adviceBase] at ha; omega
    have hleft : leftIndexBase s base+(s.h+2) ≤ a := by dsimp [rightIndexBase] at hright; omega
    have hpop : populationAddr s base < a := by dsimp [leftIndexBase] at hleft; omega
    have hhi : base+14 < a := by dsimp [populationAddr,highAddr,indexBase] at hpop; omega
    rw [keep _ (by omega) (by dsimp [borrowAddr]; omega) (Or.inr hleft) (Or.inr hright),
      im.frame _ (Or.inr (by omega)),ready.frame _ (by omega) (Or.inr hpop) (Or.inr ha)]
    simp [physicalMemory,RAMMemory.initialMemory,show ¬a < 2^d by omega]

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
