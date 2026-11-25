import OAI.Hierarchy.DescentResetShelfRuns
import OAI.Hierarchy.DescentRootPageCode
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # One fixed family of private root windows per reset

The catalog is independent of the observed bases, fallback labels, and number of
stacked copies. Empty root tickets still issue the same loops. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentResetHostSize Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
noncomputable section

/-- The two Boolean sheets hold a good root’s actual packet matrix and physical
header. Each good tap has its own selected-control sheet. Each exceptional ticket
has a header and an observed leaf census. -/
abbrev RootPage (r Y : ℕ) := Bool×((Code r×(Bool ⊕ Fin Y)) ⊕ (Code r×Option (Fin Y)))

def rootIndex (r Y : ℕ) : RootPage r Y≃Fin (Fintype.card (RootPage r Y)):=Fintype.equivFin _

namespace Shelf
variable {w N : ℕ}
def catalog (jobs : Fin N→Shelf w) := (List.ofFn jobs).reverse

theorem catalog_order (jobs : Fin N→Shelf w) (base stride : ℕ)
    (shelf : ∀i,base+stride*i.val≤(jobs i).first ∧ (jobs i).limit≤base+stride*(i.val+1)) :
    (catalog jobs).Pairwise (fun early later=>later.limit≤early.first) := by
  rw [catalog,List.pairwise_reverse,List.pairwise_iff_getElem]
  intro i j hi hj ij
  let a : Fin N:=⟨i,by simpa using hi⟩
  let b : Fin N:=⟨j,by simpa using hj⟩
  have bound:=(shelf a).2.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left stride ij) base).trans (shelf b).1)
  simpa [a,b] using bound

theorem issued_catalog (jobs : Fin N→Shelf w) (base stride : ℕ)
    (layout : ∀i,base+stride*i.val≤(jobs i).first ∧ (jobs i).limit≤base+stride*(i.val+1))
    (m : Memory w) :
    let all:=series (catalog jobs)
    all.Runs m ∧ all.ticks=(∑i,(jobs i).ticks)+4 ∧
      (∀i a,(jobs i).first≤a→a<(jobs i).limit→all.image m a=(jobs i).image m a) ∧
      (∀a,a<base ∨ base+stride*N≤a→all.image m a=m a) := by
  refine ⟨runs_series _ m,?_,?_,?_⟩
  · rw [series_ticks,catalog,List.map_reverse,List.sum_reverse,List.map_ofFn]
    simp [List.sum_ofFn]
  · intro i a lo hi
    apply read_series _ (catalog_order jobs base stride layout) m _ lo hi
    exact List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨_,rfl⟩)
  · intro a away
    apply frame_series
    intro page h
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_reverse.mp h)
    rcases away with lo|hi
    · exact .inl (lo.trans_le ((Nat.le_add_right base _).trans (layout i).1))
    · exact .inr ((layout i).2.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left stride i.isLt) base).trans hi))

theorem all_root_pages {r Y : ℕ} (pages : RootPage r Y→Shelf w) (base stride : ℕ)
    (layout : ∀p,base+stride*(rootIndex r Y p).val≤(pages p).first ∧
      (pages p).limit≤base+stride*((rootIndex r Y p).val+1)) (m : Memory w) :
    let jobs:=pages ∘ (rootIndex r Y).symm
    let all:=series (catalog jobs)
    all.Runs m ∧ (∀p a,(pages p).first≤a→a<(pages p).limit→all.image m a=(pages p).image m a) ∧
      (∀a,a<base ∨ base+stride*Fintype.card (RootPage r Y)≤a→all.image m a=m a) := by
  let jobs:=pages ∘ (rootIndex r Y).symm
  obtain ⟨run,_,fields,kept⟩:=issued_catalog jobs base stride
    (fun i=>by simpa [jobs] using layout ((rootIndex r Y).symm i)) m
  refine ⟨run,?_,kept⟩
  intro p a lo hi
  simpa [jobs] using fields (rootIndex r Y p) a (by simpa [jobs] using lo) (by simpa [jobs] using hi)

end Shelf
end
end Hierarchy.DescentSixParty.Chronology

end OAI
