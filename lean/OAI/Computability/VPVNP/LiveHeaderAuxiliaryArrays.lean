import OAI.Computability.VPVNP.LiveHeaderPairReadback
import OAI.Computability.VPVNP.LiveAuxiliaryHeaderInputs
import OAI.Computability.VPVNP.LiveAuxiliaryStages

/-!
# The seven source arrays for the native auxiliary pair

The live header supplies three computed widths, both primed group numbers,
the advice and the two decoded exterior fields. Nomination supplies the
seventh array while preserving the occupied header addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM LiveHeaderSchedule LiveHeaderWidths PrimedInputRAM ChainAssignments CutSchedule LiveHeader
open scoped Fin.CommRing

variable {s : Sizes} {base d w t Z : ℕ} {hw : 4 ≤ w} {advice : Bits s.advice}
variable {cuts : AllCuts s.h s.delta} {tag : Mode.Tag} {m : Memory w}

private def lengthSlot : Fin 3 → Slot := ![.primedLeft, .primedMiddle, .primedRight]

private theorem length_address (base : ℕ) (j : Fin 3) :
    widthAddr base .primedLeft+j.val = widthAddr base (lengthSlot j) := by
  fin_cases j <;> rfl

private theorem pair_length (s : Sizes) (i : Fin (2^s.h)) (j : Fin 3) :
    width (s.h+1) s.delta (index (i.val+1) (lengthSlot j)) =
      cutLength (PairedChain.lengths s.h s.delta s.advice i) j := by
  fin_cases j <;> change width _ _ _ = width _ _ _
  all_goals congr 1

/-- The post-nomination memory meets every input-array premise of the sparse
auxiliary initializer at its real public source addresses. -/
theorem Output.auxiliaryInputArrays (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta) (room : limit s base ≤ 2^w)
    (muBase : Word w) (hist : List (Word w)) (afterNom : Memory w)
    (stable : ∀ a, base < a → a < limit s base → afterNom a = m a)
    (nominations : ∀ j : Fin hist.length, afterNom (muBase+(j.val : Word w)).val = hist[j]) :
    let L := PairedChain.lengths s.h s.delta s.advice i
    let ξ := exteriorOf fit (liveCutEquiv s.h s.delta cuts).1
    LiveAuxiliaryHeaders.InputArrays L (PairedChain.headers advice ξ i) hist
      (LiveAuxiliaryStages.headerSources s base muBase) afterNom := by
  dsimp only
  let L := PairedChain.lengths s.h s.delta s.advice i
  let ξ := exteriorOf fit (liveCutEquiv s.h s.delta cuts).1
  have read (b j : ℕ) (lo : base < b+j) (hi : b+j < limit s base) :
      afterNom ((b : Word w)+(j : Word w)).val = m (b+j) := by
    rw [← Nat.cast_add,Fin.val_cast_of_lt (hi.trans_le room),stable _ lo hi]
  have read_exterior (side : LiveHeaderDescriptors.Side) (j : ℕ) (hj : j < s.capacity .exterior) :
      afterNom ((exteriorBase s base side : Word w)+(j : Word w)).val = m (exteriorBase s base side+j) := by
    have upper := (dest_bounds s base side .exterior (by decide)).2
    change exteriorBase s base side+s.capacity .exterior ≤ limit s base at upper
    apply read
    · cases side <;> dsimp [exteriorBase,adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase] <;> omega
    · omega
  obtain ⟨leftCut,rightCut⟩ := out.pairExteriorWords i ev he fit
  constructor
  · intro j
    change afterNom ((widthAddr base .primedLeft : Word w)+(j.val : Word w)).val = Fin.ofNat _ (cutLength L j)
    have hbound := j.isLt
    rw [read _ _ (by dsimp [widthAddr]; omega) (by rw [limit_eq]; dsimp [widthAddr]; omega), length_address]
    have h := out.scalars (.width (lengthSlot j)) (Or.inl i.isLt)
    change (m (widthAddr base (lengthSlot j))).val = width (s.h+1) s.delta (index (i.val+1) (lengthSlot j)) at h
    rw [pair_length] at h
    apply Fin.ext
    change (m (widthAddr base (lengthSlot j))).val = cutLength L j % 2^w
    rw [← h, Nat.mod_eq_of_lt (m _).isLt]
  · intro j
    change afterNom ((leftIndexBase s base : Word w)+(j.val : Word w)).val =
      encodeBit w (RAMSerialization.wordBits _ (PairedChain.groupIndex i 0) j)
    have hj : j.val < s.h+2 := j.isLt
    rw [read, out.primedLeft _ hj, ← testBit_wordBits (PairedChain.groupIndex i 0) j]
    · change encodeBit w ((2*(i.val+1)-1).testBit j.val) = encodeBit w ((2*i.val+0+1).testBit j.val)
      rw [show 2*(i.val+1)-1 = 2*i.val+0+1 by omega]
    · dsimp [leftIndexBase,populationAddr,highAddr,indexBase]; omega
    · rw [limit_eq]; dsimp [leftIndexBase,populationAddr,highAddr,indexBase]; omega
  · intro j
    change afterNom ((rightIndexBase s base : Word w)+(j.val : Word w)).val =
      encodeBit w (RAMSerialization.wordBits _ (PairedChain.groupIndex i 1) j)
    have hj : j.val < s.h+2 := j.isLt
    rw [read, out.primedRight _ hj, ← testBit_wordBits (PairedChain.groupIndex i 1) j]
    · change encodeBit w ((2*(i.val+1)).testBit j.val) = encodeBit w ((2*i.val+1+1).testBit j.val)
      rw [show 2*(i.val+1) = 2*i.val+1+1 by omega]
    · dsimp [rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega
    · rw [limit_eq]; dsimp [rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega
  · intro j
    change afterNom ((adviceBase s base : Word w)+(j.val : Word w)).val = encodeBit w (advice j)
    have hj : j.val < s.advice := j.isLt
    rw [read, out.adviceWords j]
    · dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega
    · rw [limit_eq]; dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega
  · intro j
    change afterNom ((exteriorBase s base .left : Word w)+(j.val : Word w)).val = encodeBit w (ξ i.castSucc j)
    rw [read_exterior .left j.val (j.isLt.trans_le L.leftFit)]
    exact leftCut j
  · intro j
    change afterNom ((exteriorBase s base .right : Word w)+(j.val : Word w)).val = encodeBit w (ξ i.succ j)
    rw [read_exterior .right j.val (j.isLt.trans_le L.rightFit)]
    exact rightCut j
  · exact nominations

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
