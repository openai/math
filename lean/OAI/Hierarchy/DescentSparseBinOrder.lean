import OAI.Hierarchy.DescentSparseBinLookup
import OAI.Hierarchy.DescentSparseBinMatch
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Recovering the full physical ordering from the installed local keys -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {n w : ℕ}

def code (c : C) := (Fintype.equivFin C c).val

omit [DecidableEq C] in
theorem code_lt (c : C) : code c<Fintype.card C := (Fintype.equivFin C c).isLt

omit [DecidableEq C] in
theorem code_injective : Function.Injective (code (C:=C)) :=
  Fin.val_injective.comp (Fintype.equivFin C).injective

theorem roster_strict (neighbors : Finset C) :
    StrictMono (fun a : Fin (roster neighbors).length=>code ((roster neighbors).get a)) := by
  have prev : (binOrder C).Pairwise (fun x y=>code x<code y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    simpa [binOrder,code] using ij
  have subseq := prev.filter (fun c=>decide (c∈keep neighbors))
  intro i j ij
  exact List.pairwise_iff_getElem.mp subseq i.val j.val i.isLt j.isLt ij

/-- The actual unsorted header words contain each reachable occupied colony
once, with all empty geometric cells using the out-of-range tag. -/
structure Aperture (neighbors : Finset C) (n : ℕ) where
  target : Fin n→Option C
  unique : ∀i j v,target i=some v→target j=some v→i=j
  covers : ∀v,(∃i,target i=some v)↔v∈keep neighbors

namespace Aperture
variable {neighbors : Finset C}

def key (A : Aperture neighbors n) (i : Fin n) := ((A.target i).map code).getD (Fintype.card C)

private theorem exists_row (A : Aperture neighbors n) (j : Fin (roster neighbors).length) :
    ∃i,A.target i=some ((roster neighbors).get j) := by
  apply (A.covers _).2
  exact of_decide_eq_true (List.mem_filter.mp (List.get_mem (roster neighbors) j)).2

def entry (A : Aperture neighbors n) : Fin (roster neighbors).length ↪ Fin n where
  toFun j := (A.exists_row j).choose
  inj' := by
    intro i j eqn
    have hi := (A.exists_row i).choose_spec
    have hj := (A.exists_row j).choose_spec
    have same := hi.symm.trans ((congrArg A.target eqn).trans hj)
    exact (roster_nodup neighbors).injective_get (Option.some.inj same)

theorem covered (A : Aperture neighbors n) (j : Fin (roster neighbors).length) :
    A.target (A.entry j)=some ((roster neighbors).get j) := (A.exists_row j).choose_spec

theorem entry_key (A : Aperture neighbors n) (j : Fin (roster neighbors).length) :
    A.key (A.entry j)=code ((roster neighbors).get j) := by simp [key,A.covered]

theorem nonentry (A : Aperture neighbors n) (i : Fin n) (h : ∀j,A.entry j≠i) :
    A.target i=none := by
  cases row : A.target i with
  | none => rfl
  | some c =>
    have good : c∈roster neighbors := by
      simp only [roster,List.mem_filter,mem_binOrder,true_and,decide_eq_true_eq]
      exact (A.covers c).mp ⟨i,row⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp good
    exact False.elim (h j (A.unique _ _ c ((A.covered j).trans (congrArg some hj)) row))

/-- The machine's stable rank of a genuinely occupied slot is exactly its
index in the global list filtered by reachable destinations. -/
theorem entry_rank (A : Aperture neighbors n) (j : Fin (roster neighbors).length) :
    (order A.key (A.entry j)).val=j.val := by
  rw [order_val]
  have eqn : Finset.univ.filter (fun i=>before A.key i (A.entry j))=(Finset.Iio j).map A.entry := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,Finset.mem_Iio]
    by_cases occupied : ∃t,A.entry t=i
    · obtain ⟨t,rfl⟩ := occupied
      have both : before A.key (A.entry t) (A.entry j) ↔ t<j := by
        unfold before
        rw [A.entry_key,A.entry_key]
        constructor
        · rintro (sm|⟨same,lt⟩)
          · exact (roster_strict neighbors).lt_iff_lt.mp sm
          · have sameRow := (roster_strict neighbors).injective same
            subst t
            exact False.elim (lt_irrefl _ lt)
        · exact fun lt=>Or.inl (roster_strict neighbors lt)
      simp [both]
    · have vacant := A.nonentry i (fun t eqn=>occupied ⟨t,eqn⟩)
      have full : A.key i=Fintype.card C := by simp [key,vacant]
      have lo := code_lt ((roster neighbors).get j)
      simp only [before,full,A.entry_key,not_lt_of_ge lo.le,lo.ne',false_and,or_false]
      exact iff_of_false id (fun ⟨t,_,eqn⟩=>occupied ⟨t,eqn⟩)
  rw [eqn,Finset.card_map,Fin.card_Iio]

theorem padding_key (A : Aperture neighbors n) (r : Fin n) (pad : (roster neighbors).length≤r.val) :
    A.key ((order A.key).symm r)=Fintype.card C := by
  have no (j : Fin (roster neighbors).length) : A.entry j≠(order A.key).symm r := by
    intro eqn
    have same := A.entry_rank j
    rw [eqn,Equiv.apply_symm_apply] at same
    have := j.isLt
    omega
  simp [key,A.nonentry _ no]

theorem capacity (A : Aperture neighbors n) : (roster neighbors).length≤n := by
  simpa using Fintype.card_le_of_injective A.entry A.entry.injective

/-- Authentic gathered tag at its normalized local physical index. -/
theorem tag_read (A : Aperture neighbors n) (m : Memory w) (tags : Bank) (scratch dest : ℕ)
    (read : ∀ i : Fin n,tags.read m (i.val:Word w)=(A.key i:Word w)) (j : Fin (roster neighbors).length) :
    after scratch dest tags (.lookup tags .row) A.key m (dest+j.val)=
      (code ((roster neighbors).get j):Word w) := by
  have hit := publish scratch dest tags (.lookup tags .row) A.key m (A.entry j)
  rw [A.entry_rank] at hit
  exact hit.trans ((read _).trans (congrArg (fun z : ℕ=>(z:Word w)) (A.entry_key j)))


end Aperture
end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
