import OAI.Computability.VPVNP.LiveHeaderSingleRun
import OAI.Computability.VPVNP.LiveHeaderProgramFit

/-!
# Running all width, phase, and mode stages consecutively

The eleven scalar stages fill consecutive scratch words. A frame outside the
written prefix transports the scan summary, advice and original packed sites
across the real linker handoffs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Metadata

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderWidths LiveHeaderDescriptors
open PrimedInputRAM

variable {w : ℕ}

/-- A scalar metadata item produced by the live header, covering five cut widths, four phase
flags, the first-tail flag, and mode. -/
inductive Field where
  | width (s : Slot) | flag (f : Flag) | firstTail | mode

/-- The header stage that computes the selected scalar metadata item. -/
def Field.stage : Field → Stage
  | .width s => .width s | .flag f => .flag f | .firstTail => .firstTail | .mode => .mode

/-- The physical scratch address at which the selected scalar metadata item is stored. -/
def Field.address (base : ℕ) : Field → ℕ
  | .width s => widthAddr base s | .flag f => flagAddr base f
  | .firstTail => firstTailAddr base | .mode => tagAddr base

/-- The order of the eleven scalar metadata calls, beginning with cut widths and ending with
the mode. -/
def order : Fin 11 → Field :=
  ![.width .liveLeft,.width .liveRight,.width .primedLeft,.width .primedMiddle,.width .primedRight,
    .flag .first,.flag .middle,.flag .firstHalf,.flag .last,.firstTail,.mode]

/-- Convert a metadata position to its header stage number, with position eleven denoting the
following stage. -/
def stageId (j : ℕ) (hj : j ≤ 11) : StageId := ⟨j+2,by rw [stage_count]; omega⟩

theorem stage_at (j : Fin 11) : stage (stageId j.val j.isLt.le) = (order j).stage := by
  fin_cases j <;> rfl

theorem next_at (j : Fin 11) : next (stageId j.val j.isLt.le) = some (stageId (j.val+1) j.isLt) := by
  unfold next
  split
  · rfl
  · rename_i hh
    change ¬ j.val+2+1 < stages.length at hh
    rw [stage_count] at hh
    have := j.isLt
    omega

private theorem address_at (base : ℕ) (j : Fin 11) : (order j).address base = base+1+j.val := by
  fin_cases j <;> rfl

/-- The stored word has the scheduled width when needed, the encoded truth value for a flag, or
the selected mode code. -/
def Correct (s : Sizes) (i : ℕ) (tag : LiveHeader.Mode.Tag) : Field → Word w → Prop
  | .width slot,v => Needed s.h i slot → v.val = CutSchedule.width (s.h+1) s.delta (index i slot)
  | .flag f,v => v = encodeBit w (decide (f.holds s.h i))
  | .firstTail,v => v = encodeBit w (decide (i=2^s.h+1))
  | .mode,v => v = Fin.ofNat _ tag.code.val

/-- Completed fields have their mathematical values. Later cells and packed
processor sites still have their values at entry to the width stage. -/
structure Image (s : Sizes) (base i : ℕ) (tag : LiveHeader.Mode.Tag) (original m : Memory w) (done : ℕ) : Prop where
  readback : ∀ j : Fin 11, j.val < done → Correct s i tag (order j) (m (base+1+j.val))
  frame : ∀ a, a < base ∨ base+done < a → m a = original a

theorem Image.summary {s : Sizes} {base i : ℕ} {tag : LiveHeader.Mode.Tag} {original m : Memory w}
    {done : ℕ} (img : Image s base i tag original m done) (hdone : done ≤ 11)
    (h : Summary s base i original) : Summary s base i m := by
  have hhigh := img.frame (highAddr s base) (Or.inr (by dsimp [highAddr,indexBase]; omega))
  have hpop := img.frame (populationAddr s base) (Or.inr (by dsimp [populationAddr,highAddr,indexBase]; omega))
  have hlow := img.frame (indexBase base) (Or.inr (by dsimp [indexBase]; omega))
  exact ⟨hhigh ▸ h.high,hpop ▸ h.count,h.singleton,hlow ▸ h.low⟩

private theorem mode_last (j : Fin 11) (h : order j = .mode) : j = 10 := by
  fin_cases j <;> first | exact rfl | contradiction

private theorem step (s : Sizes) (base d : ℕ) {hw : 4 ≤ w} (advice : CutSchedule.Bits s.advice)
    (cuts : ChainAssignments.AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : LiveHeader.Mode.Tag)
    (fit : ScalarFit w s base) (hsites : 2^d ≤ base) (original m : Memory w)
    (headers : LiveHeader.SiteHeaders d hw advice cuts g original) (sum : Summary s base (g.val+1) original)
    (j : Fin 11) (img : Image s base (g.val+1) tag original m j.val)
    (selected : order j = .mode → LiveHeader.physicalTag cuts g = some tag) :
    ∃ v : Word w, SingleRun s base (order j).stage m (writeMemory m (Fin.ofNat _ ((order j).address base)) v) ∧
      Correct s (g.val+1) tag (order j) v := by
  have summary := img.summary j.isLt.le sum
  have hg : g.val+1 ≤ 2^(s.h+1) := g.isLt
  cases he : order j with
  | width slot => exact width_run s base (g.val+1) slot m fit (by omega) hg summary
  | flag f => exact ⟨_,flag_run s base (g.val+1) f m fit (by omega) hg summary,rfl⟩
  | firstTail => exact ⟨_,firstTail_run (by omega) s base (g.val+1) m fit (by omega) hg summary,rfl⟩
  | mode =>
    have hj := mode_last j he
    have hv : j.val = 10 := by rw [hj]; rfl
    have left := img.readback 0 (by rw [hv]; decide)
    have right := img.readback 1 (by rw [hv]; decide)
    have firstHalf := img.readback 7 (by rw [hv]; decide)
    have hl := left (Or.inr (Or.inl rfl))
    have hr := right (Or.inr (Or.inr rfl))
    have cur : LiveHeader.SiteHeaders d hw advice cuts g m :=
      fun v => (img.frame v.val (Or.inl (v.isLt.trans_le hsites))).trans (headers v)
    refine ⟨_,mode_run s base d advice cuts g m fit cur ?_ ?_ firstHalf tag (selected he),rfl⟩
    · change (m (base+1)).val = CutSchedule.width (s.h+1) s.delta g.val
      change (m (base+1)).val = CutSchedule.width (s.h+1) s.delta (g.val+1-1) at hl
      simpa using hl
    · exact hr

private theorem extend (s : Sizes) (base i : ℕ) (tag : LiveHeader.Mode.Tag)
    (fit : ScalarFit w s base) {original m : Memory w} {j : Fin 11} (img : Image s base i tag original m j.val)
    {v : Word w} (hc : Correct s i tag (order j) v) :
    Image s base i tag original
      (LiveStageLink.transferMemory (Fin.ofNat _ base) (next (stageId j.val j.isLt.le))
        (writeMemory m (Fin.ofNat _ ((order j).address base)) v)) (j.val+1) := by
  have h := fit.address
  rw [limit_eq] at h
  have hj := j.isLt
  have hb : (Fin.ofNat (2^w) base).val = base := Nat.mod_eq_of_lt (by omega)
  have ha : (Fin.ofNat (2^w) ((order j).address base)).val = base+1+j.val := by
    rw [address_at,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [next_at]
  constructor
  · intro k hk
    simp only [LiveStageLink.transferMemory,writeMemory,hb,ha,show base+1+k.val ≠ base by omega,↓reduceIte]
    by_cases he : k = j
    · subst k; simpa using hc
    · have hv : k.val ≠ j.val := fun e => he (Fin.ext e)
      simpa [hv] using img.readback k (by omega)
  · intro a ha'
    have hn : a ≠ base := by omega
    have hn' : a ≠ base+1+j.val := by omega
    simpa only [LiveStageLink.transferMemory,writeMemory,hb,ha,hn,hn',↓reduceIte] using img.frame a (by omega)

/-- Execute any prefix of the eleven scalar stages. The first ten can run
before the two mode bits are known to be compatible. -/
theorem run_prefix (s : Sizes) (base d : ℕ) {hw : 4 ≤ w} (advice : CutSchedule.Bits s.advice)
    (cuts : ChainAssignments.AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : LiveHeader.Mode.Tag)
    (fit : ScalarFit w s base) (hsites : 2^d ≤ base) (m : Memory w)
    (headers : LiveHeader.SiteHeaders d hw advice cuts g m) (sum : Summary s base (g.val+1) m)
    (done : ℕ) (hdone : done ≤ 11) (modeOK : done = 11 → LiveHeader.physicalTag cuts g = some tag) :
    ∃ xs out, StagePrefix s base (some (stageId 0 (by decide))) m xs (some (stageId done hdone)) out ∧
      (∀ x ∈ xs, x.Good s) ∧ Image s base (g.val+1) tag m out done := by
  induction done with
  | zero => exact ⟨[],m,.nil ..,by simp,⟨by simp, fun _ _ => rfl⟩⟩
  | succ n ih =>
    have hn : n < 11 := by omega
    let j : Fin 11 := ⟨n,hn⟩
    obtain ⟨xs,cur,old,good,img⟩ := ih hn.le (by omega)
    have sel : order j = .mode → LiveHeader.physicalTag cuts g = some tag := by
      intro h
      have hj := congrArg Fin.val (mode_last j h)
      change n = 10 at hj
      apply modeOK (by omega)
    obtain ⟨v,run,hv⟩ := step s base d advice cuts g tag fit hsites m cur headers sum j img sel
    have one : calls s (order j).stage = 1 := by cases order j <;> rfl
    obtain ⟨x,_,hgood,seg⟩ := run.prefix (stageId n hn.le) (stage_at j) one
    have image := extend s base (g.val+1) tag fit img hv
    rw [next_at j] at seg image
    refine ⟨xs++[x],_,old.append seg,?_,image⟩
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact good y h
    · exact (List.mem_singleton.mp h) ▸ hgood

end LiveHeaderProgram.Metadata

end VPVNP
end Computability
end OAI
