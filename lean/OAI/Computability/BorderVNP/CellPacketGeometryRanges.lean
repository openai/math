import OAI.Computability.BorderVNP.CellPacketGeometrySort

/-! # Compact intervals of the public cell directory

Two rows at a cell key bracket its original word ordinals. Sorting all words globally
returns one contiguous interval between the two markers, in precisely the original
order within the cell. Zero-length sections have adjacent markers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort

/-- Words between two source ordinals in their common cell. Other cells and padding
can appear anywhere in the raw rectangle. -/
def inside {n : ℕ} (key : Fin n → ℕ) (lo hi : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (key i = key lo ∧ lo < i ∧ i < hi)

/-- Natural address of the indicated word after the left marker in the sorted table. -/
def innerIndex {n : ℕ} (lo hi : Fin n) (i : Fin (hi.val-lo.val-1)) : Fin n :=
  ⟨lo.val+1+i.val,by have := hi.isLt; have := i.isLt; omega⟩

private theorem key_mono {b : ℕ} (key : Fin (2^b) → ℕ) (π : Equiv.Perm (Fin (2^b)))
    (hrank : Monotone fun i => 2*key (π i)*2^b+(π i).val) : Monotone (key ∘ π) := by
  intro i j hij
  have h := hrank hij
  change 2*key (π i)*2^b+(π i).val ≤ 2*key (π j)*2^b+(π j).val at h
  change key (π i) ≤ key (π j)
  by_contra! hbad
  have hh := Nat.mul_le_mul_right (2^b) (show 2*key (π j)+1 ≤ 2*key (π i) by omega)
  rw [Nat.succ_mul] at hh
  have := (π j).isLt
  omega

private theorem key_stable {b : ℕ} (key : Fin (2^b) → ℕ) (π : Equiv.Perm (Fin (2^b)))
    (hrank : Monotone fun i => 2*key (π i)*2^b+(π i).val) {i j : Fin (2^b)}
    (eqn : key (π i) = key (π j)) : i < j ↔ π i < π j := by
  have weak (l r : Fin (2^b)) (hl : l ≤ r) (eq : key (π l) = key (π r)) : π l ≤ π r := by
    have h := hrank hl
    change 2*key (π l)*2^b+(π l).val ≤ 2*key (π r)*2^b+(π r).val at h
    rw [eq,Nat.add_le_add_iff_left] at h
    exact h
  exact ⟨fun h => lt_of_le_of_ne (weak i j h.le eqn) (π.injective.ne h.ne),
    fun h => lt_of_not_ge (fun hn => h.not_ge (weak j i hn eqn.symm))⟩

/-- In the actual sorted table, the rows between the returned marker positions are
exactly the cell's indicated raw words, with no holes and no change of order. -/
theorem inside_sorted {b : ℕ} (key : Fin (2^b) → ℕ) (π : Equiv.Perm (Fin (2^b)))
    (hrank : Monotone fun i => 2*key (π i)*2^b+(π i).val) (lo hi : Fin (2^b))
    (same : key lo = key hi) :
    List.ofFn (fun j => π (innerIndex (π.symm lo) (π.symm hi) j)) = inside key lo hi := by
  let l := π.symm lo
  let r := π.symm hi
  let pos := innerIndex l r
  let pick := π ∘ pos
  have left : π l = lo := π.apply_symm_apply lo
  have right : π r = hi := π.apply_symm_apply hi
  have eqKey (u : Fin (2^b)) (hu : l < u) (hv : u < r) : key (π u) = key lo := by
    have h₁ := key_mono key π hrank hu.le
    have h₂ := key_mono key π hrank hv.le
    change key (π l) ≤ key (π u) at h₁
    change key (π u) ≤ key (π r) at h₂
    rw [left] at h₁
    rw [right,← same] at h₂
    exact h₂.antisymm h₁
  have bounds (j : Fin (r.val-l.val-1)) : l < pos j ∧ pos j < r := by
    change l.val < l.val+1+j.val ∧ l.val+1+j.val < r.val
    have := j.isLt
    omega
  have strict : StrictMono pick := by
    intro i j h
    apply (key_stable key π hrank ((eqKey _ (bounds i).1 (bounds i).2).trans
      (eqKey _ (bounds j).1 (bounds j).2).symm)).mp
    change l.val+1+i.val < l.val+1+j.val
    omega
  have sameMem (u : Fin (2^b)) : u ∈ List.ofFn pick ↔ u ∈ inside key lo hi := by
    simp only [inside,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,List.mem_ofFn]
    constructor
    · rintro ⟨j,rfl⟩
      have bds := bounds j
      have hk := eqKey _ bds.1 bds.2
      refine ⟨hk,?_,?_⟩
      · rw [← left]
        exact (key_stable key π hrank (left ▸ hk.symm)).mp bds.1
      · rw [← right]
        exact (key_stable key π hrank (hk.trans (right ▸ same))).mp bds.2
    · rintro ⟨hk,hl,hr⟩
      let i := π.symm u
      have eqn : π i = u := π.apply_symm_apply _
      have a : l < i := (key_stable key π hrank (by rw [left,eqn,hk])).mpr (by rwa [left,eqn])
      have z : i < r := (key_stable key π hrank (by rw [eqn,right,hk,same])).mpr (by rwa [eqn,right])
      let j : Fin (r.val-l.val-1) := ⟨i.val-(l.val+1),by change l.val < i.val at a; change i.val < r.val at z; omega⟩
      have hp : pos j = i := Fin.ext (by change l.val+1+(i.val-(l.val+1)) = i.val; change l.val < i.val at a; omega)
      exact ⟨j,by simp [pick,hp,eqn]⟩
  have hp := (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective strict.injective)
    ((List.nodup_finRange _).filter _)).mpr sameMem
  have mono : Monotone (id : Fin (2^b) → Fin (2^b)) := monotone_id
  exact hp.eq_of_pairwise' strict.monotone.sortedLE_ofFn.pairwise
    (List.Pairwise.filter _ (List.ofFn_id _ ▸ mono.sortedLE_ofFn.pairwise))

/-- Width read by subtracting the two sorted marker addresses and skipping the
left marker. -/
theorem interval_count {b : ℕ} (key : Fin (2^b) → ℕ) (π : Equiv.Perm (Fin (2^b)))
    (hrank : Monotone fun i => 2*key (π i)*2^b+(π i).val) (lo hi : Fin (2^b))
    (same : key lo = key hi) :
    (π.symm hi).val-(π.symm lo).val-1 = (inside key lo hi).length := by
  simpa only [List.length_ofFn] using congrArg List.length (inside_sorted key π hrank lo hi same)

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
