import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI
/-! # Contiguous ranks of a prefix of variable-width rows -/

namespace Hierarchy.ProtocolRAM.PaidPrefixRank

open scoped BigOperators
variable {T : ℕ}

/-- The prefix of a flattened dependent array ends after all cells of rows below `j`. -/
def prefixCount (width : Fin T → ℕ) (j : Fin (T+1)) : ℕ :=
  ∑ i : Fin j.val, width (i.castLE (by omega))

private def widthAt (width : Fin T → ℕ) (i : ℕ) := if h : i<T then width ⟨i,h⟩ else 0

theorem prefixCount_eq (width : Fin T → ℕ) (j : Fin (T+1)) :
    prefixCount width j=∑ i : Fin j.val,width (i.castLE (by omega)) := rfl

private theorem asRange (width : Fin T→ℕ) (j : Fin (T+1)) :
    prefixCount width j=∑ i ∈ Finset.range j.val,widthAt width i := by
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [widthAt,dite_eq_left (show i.val<T by have:=i.isLt;omega)]; rfl

theorem mono (width : Fin T→ℕ) {i j : Fin (T+1)} (bound : i.val≤j.val) :
    prefixCount width i≤prefixCount width j := by
  rw [asRange,asRange]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono bound)

theorem le (width : Fin T→ℕ) (j : Fin (T+1)) : prefixCount width j≤∑ i,width i :=
  mono width (i:=j) (j:=Fin.last T) (by change j.val≤T; exact Nat.le_of_lt_succ j.isLt)

theorem succ (width : Fin T→ℕ) (i : Fin T) :
    prefixCount width i.succ=prefixCount width i.castSucc+width i := by
  rw [asRange,asRange]
  change (∑ x ∈ Finset.range (i.val+1),widthAt width x)=_
  rw [Finset.sum_range_succ]
  simp [widthAt,i.isLt]

theorem lt_iff (width : Fin T→ℕ) (j : Fin (T+1)) (r : Fin (∑ i,width i)) :
    r.val<prefixCount width j ↔ ((finSigmaFinEquiv (n:=width)).symm r).1.val<j.val := by
  obtain ⟨⟨i,k⟩,rfl⟩ := (finSigmaFinEquiv (n:=width)).surjective r
  rw [Equiv.symm_apply_apply]
  have rank : (finSigmaFinEquiv (n:=width) ⟨i,k⟩).val=prefixCount width i.castSucc+k.val :=
    finSigmaFinEquiv_apply _
  rw [rank]
  change prefixCount width i.castSucc+k.val<prefixCount width j ↔ i.val<j.val
  constructor
  · intro less
    by_cases past : j.val≤i.val
    · have := mono width (i:=j) (j:=i.castSucc) past
      omega
    · omega
  · intro inside
    have bound := mono width (i:=i.succ) (j:=j) (by change i.val+1≤j.val;omega)
    rw [succ] at bound
    have:=k.isLt
    omega

/-- Embed the shorter initial array into the full array and sum with zero
weight on the complement. -/
theorem sum_initial {A : Type*} [AddCommMonoid A] {n N : ℕ} (bound : n≤N) (f : Fin N→A) :
    (∑ i : Fin n,f (i.castLE bound))=∑ r : Fin N,if r.val<n then f r else 0 := by
  obtain ⟨tail,rfl⟩:=Nat.exists_eq_add_of_le bound
  rw [Fin.sum_univ_add (fun r : Fin (n+tail)=>if r.val<n then f r else 0)]
  have early (i : Fin n) : (i.castAdd tail).val<n := i.isLt
  have late (i : Fin tail) : ¬(Fin.natAdd n i).val<n := by change ¬n+i.val<n; omega
  simp only [early,late,ite_true,ite_false,Finset.sum_const_zero,add_zero]; rfl

/-- Restrict a sum over the flat array to a row prefix and recover the
ordinary sum of all constituent cells in those rows. -/
theorem restricted_sum {A : Type*} [AddCommMonoid A] (width : Fin T→ℕ) (j : Fin (T+1))
    (f : Fin (∑ i,width i)→A) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin (∑ i,width i)=>r.val<prefixCount width j),f r)=
      ∑ i ∈ Finset.univ.filter (fun i : Fin T=>i.val<j.val),∑ k : Fin (width i),f (finSigmaFinEquiv ⟨i,k⟩) := by
  classical
  rw [Finset.sum_filter,Finset.sum_filter]
  let e:=finSigmaFinEquiv (n:=width)
  calc
    _=∑ b : Σ i,Fin (width i),if b.1.val<j.val then f (e b) else 0 := by
      rw [←e.sum_comp (fun r => if r.val<prefixCount width j then f r else 0)]
      apply Finset.sum_congr rfl
      intro b _
      have equals:=lt_iff width j (e b)
      change (e b).val<prefixCount width j ↔ (e.symm (e b)).1.val<j.val at equals
      rw [e.symm_apply_apply] at equals
      simp only [equals]
    _=_ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i.val<j.val <;> simp [h,e]

end Hierarchy.ProtocolRAM.PaidPrefixRank

end OAI
