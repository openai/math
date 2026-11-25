import OAI.Hierarchy.GridPassageRAMMaskDecode
import OAI.Hierarchy.GridPassageMaskHistory
import OAI.Hierarchy.GridPassageMaskSelection

namespace OAI
/-! # Execution of the native variable-width mark correction -/

namespace Hierarchy.GridPassageRAMMask
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open GridLens GridPassageRAMPadIndex
open GridPassageRAMRow (AddressMap DecodeReads rankIn cursor)
open scoped Classical Fin.CommRing

variable {w k n E B : ℕ}

def parameters (a : AddressMap) (w compact k n B : ℕ) : Parameters w :=
  values w ((n+1)^k*k*B) B k (n+1) a.out.counter a.out.chosen compact a.powers a.out.mark

variable (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1))) (width : Fin k → ℕ)

def target (mark B : ℕ) (i : ℕ) : Option ℕ :=
  if h : i < (n+1)^k*k*B then
    let u := (indexEquiv k (n+1) B).symm ⟨i,h⟩
    removeAt direction row touch width mark u.1.1 u.1.2 u.2
  else none

@[simp] theorem target_slot (mark : ℕ) (x : Fin k → Fin (n+1)) (j : Fin k) (r : Fin B) :
    target direction row touch width mark B (ordinal x j r) = removeAt direction row touch width mark x j r := by
  let e := indexEquiv k (n+1) B
  let z := e ((x,j),r)
  have index : ordinal x j r = z.val := (indexEquiv_val x j r).symm
  rw [index]
  unfold target
  rw [dite_eq_left z.isLt]
  change removeAt direction row touch width mark (e.symm z).1.1 (e.symm z).1.2
    (e.symm z).2 = _
  rw [show e.symm z = ((x,j),r) from e.symm_apply_apply _]

theorem target_range (mark B i u : ℕ) (hit : target direction row touch width mark B i = some u) :
    mark ≤ u ∧ u < mark+E*(n+1) := by
  unfold target at hit
  split at hit
  · rename_i hi
    let p := (indexEquiv k (n+1) B).symm ⟨i,hi⟩
    let s := untouchedRails direction row touch p.1.1 p.1.2
    change (if h : width p.1.2 ≤ p.2.val ∧ p.2.val < s.card then some
      (mark+cursor (s.orderEmbOfFin rfl ⟨p.2.val,h.2⟩).val (p.1.1 p.1.2)) else none) = some u at hit
    split at hit
    · rename_i take
      let e := s.orderEmbOfFin rfl ⟨p.2.val,take.2⟩
      let t := p.1.1 p.1.2
      have et : cursor e.val t < E*(n+1) := calc
        _ < e.val*(n+1)+(n+1) := Nat.add_lt_add_left t.isLt _
        _ = (e.val+1)*(n+1) := (Nat.succ_mul ..).symm
        _ ≤ E*(n+1) := Nat.mul_le_mul_right _ e.isLt
      have put : mark+cursor e.val t = u := Option.some.inj hit
      omega
    · cases hit
  · cases hit

theorem target_mark_iff (mark : ℕ) (e : Fin E) (t : Fin (n+1)) :
    (∃ i<(n+1)^k*k*B, target direction row touch width mark B i = some (mark+cursor e.val t)) ↔
    let x := cellOnRail (direction e) (row e) t
    touch e ≠ some t ∧ width (direction e) ≤ rankIn direction row touch x (direction e) e ∧
      rankIn direction row touch x (direction e) e < B := by
  rw [← exists_remove_iff direction row touch width mark e t]
  constructor
  · rintro ⟨i,hi,hit⟩
    obtain ⟨⟨⟨x,j⟩,r⟩,eq,_⟩ := decode i hi
    exact ⟨x,j,r,by simpa only [←eq,target_slot] using hit⟩
  · rintro ⟨x,j,r,hit⟩
    exact ⟨ordinal x j r,ordinal_lt x j r,by simpa only [target_slot] using hit⟩

def finalMemory (a : AddressMap) (B : ℕ) (input : Memory w) : Memory w :=
  erased (target direction row touch width a.out.mark B) (a.finalMemory k n E B input) ((n+1)^k*k*B)

theorem final_frame (a : AddressMap) (B : ℕ) (input : Memory w) (addr : ℕ)
    (outside : addr<a.out.mark ∨ a.out.mark+E*(n+1)≤addr) :
    finalMemory direction row touch width a B input addr = a.finalMemory k n E B input addr := by
  rw [finalMemory,erased_reads,ite_eq_right]
  rintro ⟨s,_,hit⟩
  have span := target_range direction row touch width _ _ _ _ hit
  omega

/-- The whole selector preserves both the immutable input pages and every higher external bank. -/
theorem external_frame (a : AddressMap) (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (addr : ℕ) (outside : addr<a.out.counter ∨ a.out.mark+E*(n+1)≤addr) :
    finalMemory direction row touch width a B input addr = input addr := by
  have state := a.final_correct direction row touch B fits input loaded
  rcases outside with lo|hi
  · have counts := fits.separated.counts
    have choices := fits.separated.choices
    exact (final_frame direction row touch width a B input addr (.inl (by omega))).trans (state.input _ lo)
  · exact (final_frame direction row touch width a B input addr (.inr hi)).trans (state.above _ hi)

theorem final_mark (a : AddressMap) (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (pad : ∀ j, width j ≤ B) (e : Fin E) (t : Fin (n+1)) :
    finalMemory direction row touch width a B input (a.out.mark+cursor e.val t) = if
      touch e ≠ some t ∧ rankIn direction row touch (cellOnRail (direction e) (row e) t) (direction e) e < width (direction e)
      then 1 else 0 := by
  rw [finalMemory,erased_reads,a.final_mark direction row touch B fits input loaded]
  let rank := rankIn direction row touch (cellOnRail (direction e) (row e) t) (direction e) e
  let gone := ∃ i < (n+1)^k*k*B,
    target direction row touch width a.out.mark B i = some (a.out.mark+cursor e.val t)
  have erased_iff : gone ↔ touch e ≠ some t ∧ width (direction e) ≤ rank ∧ rank < B :=
    target_mark_iff direction row touch width _ e t
  split
  · rename_i deleted
    have surplus := (erased_iff.mp deleted).2.1
    symm
    apply ite_eq_right
    rintro ⟨_,low⟩
    exact (Nat.not_le_of_lt low) surplus
  · rename_i remaining
    split
    · rename_i old
      symm
      apply ite_eq_left
      refine ⟨old.1,?_⟩
      by_contra high
      exact remaining (erased_iff.mpr ⟨old.1,Nat.le_of_not_gt high,old.2⟩)
    · rename_i old
      symm
      apply ite_eq_right
      intro keep
      exact old ⟨keep.1,keep.2.trans_le (pad _)⟩

theorem final_chosen (a : AddressMap) (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (pad : ∀ j, width j ≤ B) (cap : ∀ x j, width j ≤ (untouchedRails direction row touch x j).card)
    (x : Fin k → Fin (n+1)) (j : Fin k) (r : Fin (width j)) :
    finalMemory direction row touch width a B input (a.out.chosen+((finFunctionFinEquiv x).val*k+j.val)*B+r.val) =
      ((firstPassage direction row touch width cap x ⟨j,r⟩).val : Word w) := by
  have bound := ordinal_lt x j (r.castLE (pad j))
  change ((finFunctionFinEquiv x).val*k+j.val)*B+r.val < _ at bound
  have room := fits.separated.choices
  rw [final_frame direction row touch width a B input _ (.inl (by omega))]
  exact a.final_chosen direction row touch B fits input loaded width pad cap x j r

end Hierarchy.GridPassageRAMMask

end OAI
