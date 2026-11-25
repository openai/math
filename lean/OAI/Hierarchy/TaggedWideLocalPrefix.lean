import OAI.Hierarchy.TaggedShorterCommonScan
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Replaying an original ordinal prefix using only one site's bounded role directory -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open scoped Classical BigOperators

variable {n g D W : ℕ} (key : Fin n → Fin g) (width : Fin n→ℕ)

theorem original_prefix (head : Fin n) (ch : Fin g) :
    TaggedShorterCommonScan.earlier key width head.val ch=
      ∑i : Fin n,if i.val<head.val ∧ key i=ch then width i else 0 := by
  rw [TaggedShorterCommonScan.earlier]
  calc
    _ = ∑ j : Fin head.val,if key (j.castLE head.isLt.le)=ch then width (j.castLE head.isLt.le) else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj,(Finset.mem_range.mp hj).trans head.isLt]
    _ = _ := by
      apply Finset.sum_bij_ne_zero (fun i _ _=>i.castLE head.isLt.le)
      · simp
      · intro a _ _ b _ _ eqn
        exact Fin.ext (congrArg (fun j : Fin n=>j.val) eqn)
      · intro a _ ne
        have lt : a.val<head.val := by by_contra h;simp [h] at ne
        exact ⟨⟨a.val,lt⟩,Finset.mem_univ _,by simpa [lt] using ne,rfl⟩
      · intro a _ _
        simp [a.isLt]

/-- For a fixed half-chord, every positive contributing original ordinal
occurs at a unique bounded local role. Dormant and unrelated words can be
arbitrary. The native gate compares global ordinal and the other endpoint,
then adds the read width. -/
theorem local_prefix (head : Fin n) (ch : Fin g) (ord other value : Fin D→ℕ) (target : ℕ)
    (place : {i : Fin n // 0<width i ∧ key i=ch} ↪ Fin D)
    (observed : ∀i,ord (place i)=i.val.val ∧ other (place i)=target ∧ value (place i)=width i.val)
    (empty : ∀q,q∉Set.range place → other q≠target ∨ value q=0) :
    (∑q : Fin D,if ord q<head.val ∧ other q=target then value q else 0)=
      TaggedShorterCommonScan.earlier key width head.val ch := by
  rw [original_prefix]
  let used := fun i : Fin n=>0<width i ∧ key i=ch
  let load := fun q : Fin D=>if ord q<head.val ∧ other q=target then value q else 0
  calc
    _ = ∑q∈Finset.univ.map place,load q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ outside
      have miss : q∉Set.range place := by
        simpa only [Finset.mem_map,Finset.mem_univ,true_and,Set.mem_range] using outside
      rcases empty q miss with h|h <;> simp [load,h]
    _ = ∑i : {i : Fin n // used i},if i.val.val<head.val then width i.val else 0 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp only [load,(observed i).1,(observed i).2.1,(observed i).2.2,and_true]
    _ = _ := by
      apply Finset.sum_bij_ne_zero (fun i _ _=>i.val)
      · simp
      · intro a _ _ b _ _ h
        exact Subtype.ext h
      · intro i _ nonzero
        split_ifs at nonzero with test
        · have pos := Nat.pos_of_ne_zero nonzero
          exact ⟨⟨i,pos,test.2⟩,Finset.mem_univ _,by simpa [test.1] using nonzero,rfl⟩
        · contradiction
      · intro i _ _
        simp only [i.property.2,and_true]

end Hierarchy.Tagged.PassiveWindow

end
end OAI
