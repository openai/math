import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Packed bit ordinals from sparse physical item identities -/

namespace Hierarchy.DescentOrderedWords
open scoped BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] {N : ℕ} (key : I ↪ Fin N) (width : I→ℕ)
def before (i : I) := Finset.univ.filter (fun j=>key j<key i)
def offset (i : I) : ℕ := ∑j∈before key i,width j

theorem earlier (i j : I) (lt : key i<key j) : offset key width i+width i≤offset key width j := by
  have absent : i∉before key i := by simp [before]
  calc offset key width i+width i=∑v∈insert i (before key i),width v := by rw [offset,Finset.sum_insert absent,add_comm]
       _≤_ := by
         apply Finset.sum_le_sum_of_subset
         intro v mem
         rcases Finset.mem_insert.mp mem with rfl|old
         · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩
         · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp old).2 lt⟩

theorem end_le (i : I) : offset key width i+width i≤∑v,width v := by
  have absent : i∉before key i := by simp [before]
  calc offset key width i+width i=∑v∈insert i (before key i),width v := by rw [offset,Finset.sum_insert absent,add_comm]
       _≤_ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def bitIndex (z : Σi,Fin (width i)) : Fin (∑i,width i) :=
  ⟨offset key width z.1+z.2.val,(Nat.add_lt_add_left z.2.isLt _).trans_le (end_le key width _)⟩

theorem bitIndex_injective : Function.Injective (bitIndex key width) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  have val := congrArg Fin.val eq
  change offset key width i+a.val=offset key width j+b.val at val
  rcases lt_trichotomy (key i) (key j) with less|same|more
  · have sep := earlier key width i j less
    have := a.isLt
    omega
  · obtain rfl := key.injective same
    exact congrArg (Sigma.mk i) (Fin.ext (by omega))
  · have sep := earlier key width j i more
    have := b.isLt
    omega

/-- This is a packed word in increasing external item ID and, within the
item, increasing bit order. Zero-width old items occupy no bits. -/
def address : (Σi,Fin (width i)) ≃ Fin (∑i,width i) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨bitIndex_injective key width,by simp⟩)

@[simp] theorem address_val (i : I) (j : Fin (width i)) :
    (address key width ⟨i,j⟩).val=offset key width i+j.val := rfl

/-- Each live directory row is read once, even when the enclosing ID space
has a large empty suffix or has holes between populated rows. -/
def scan {A : Type*} (tag size : A→ℕ) (limit : ℕ) : List A→ℕ×ℕ
  | [] => (0,0)
  | a::as => let rest := scan tag size limit as
             ((if tag a<limit then size a else 0)+rest.1,1+rest.2)

theorem scan_spec {A : Type*} (tag size : A→ℕ) (limit : ℕ) (directory : List A) :
    scan tag size limit directory=((directory.map (fun i=>if tag i<limit then size i else 0)).sum,directory.length) := by
  induction directory with
  | nil => rfl
  | cons a as ih => simp [scan,ih,Nat.add_comm]

theorem scan_offset (directory : List I) (ids : directory.Nodup) (all : ∀i,i∈directory) (i : I) :
    scan (fun z=>(key z).val) width (key i).val directory=(offset key width i,directory.length) := by
  have total : directory.toFinset=Finset.univ := by ext x;simp [all]
  rw [scan_spec]
  rw [←List.sum_toFinset _ ids,total,offset,before,Finset.sum_filter]; rfl

end
end Hierarchy.DescentOrderedWords

end OAI
