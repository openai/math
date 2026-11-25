import OAI.Hierarchy.TaggedSortLiftStage
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Sorting the ordered fibers of a public block partition -/

noncomputable section
namespace Hierarchy.Tagged.SortLift
open scoped Classical

variable {n m : ℕ} {α κ : Type*} [LinearOrder κ]

abbrev Fiber (g : Fin n → Fin m) (b : Fin m) := {i : Fin n // g i=b}

def fiberOrder (g : Fin n → Fin m) (b : Fin m) :=
  Fintype.orderIsoFinOfCardEq (Fiber g b) rfl

def blockEquiv (g : Fin n → Fin m) : (Σ b, Fin (Fintype.card (Fiber g b))) ≃ Fin n :=
  (Equiv.sigmaCongrRight (fun b=>(fiberOrder g b).toEquiv)).trans (Equiv.sigmaFiberEquiv g)

def blockPass (g : Fin n → Fin m) : Stage n :=
  ⟨m,fun b=>Fintype.card (Fiber g b),blockEquiv g,blockEquiv g⟩

def atBlock (g : Fin n → Fin m) (b : Fin m) (j : Fin (Fintype.card (Fiber g b))) :=
  (fiberOrder g b j).val

theorem atBlock_label (g : Fin n → Fin m) (b : Fin m) (j : Fin (Fintype.card (Fiber g b))) :
    g (atBlock g b j)=b := (fiberOrder g b j).property

theorem atBlock_order (g : Fin n → Fin m) {b : Fin m} {i j : Fin (Fintype.card (Fiber g b))} :
    atBlock g b i≤atBlock g b j ↔ i≤j := (fiberOrder g b).le_iff_le

private theorem cut_at (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ) (b : Fin m)
    (j : Fin (Fintype.card (Fiber g b))) :
    key ((blockPass g).eval key x (atBlock g b j))<t ↔
      j.val<cutCount (fun v=>key (x (atBlock g b v))<t) :=
  (blockPass g).lt_cut_iff key x b j t

def CutPrefix (x : Fin n → α) (key : α → κ) (t : κ) : Prop :=
  ∀ i j : Fin n, i≤j → key (x j)<t → key (x i)<t

theorem before_pass (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ) {lo : ℕ}
    (before : ∀ i : Fin n,i.val<lo → key (x i)<t) :
    ∀ i : Fin n,i.val<lo → key ((blockPass g).eval key x i)<t := by
  intro i hi
  obtain ⟨⟨b,j⟩,rfl⟩ := (blockEquiv g).surjective i
  change (atBlock g b j).val<lo at hi
  apply (cut_at g key x t b j).2
  have count : (Finset.Iic j).card ≤ cutCount (fun v=>key (x (atBlock g b v))<t) := by
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact before _ (lt_of_le_of_lt ((atBlock_order g).mpr (Finset.mem_Iic.mp hv)) hi)
  rw [Fin.card_Iic] at count
  omega

theorem after_pass (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ) {hi : ℕ}
    (after : ∀ i : Fin n,hi ≤ i.val → ¬key (x i)<t) :
    ∀ i : Fin n,hi ≤ i.val → ¬key ((blockPass g).eval key x i)<t := by
  intro i hi' good
  obtain ⟨⟨b,j⟩,rfl⟩ := (blockEquiv g).surjective i
  change hi≤(atBlock g b j).val at hi'
  have count : cutCount (fun v=>key (x (atBlock g b v))<t)≤(Finset.Iio j).card := by
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
    apply Finset.mem_Iio.mpr
    by_contra! rev
    exact after _ (hi'.trans ((atBlock_order g).mpr rev)) hv
  rw [Fin.card_Iio] at count
  exact (not_lt_of_ge count) ((cut_at g key x t b j).mp good)

theorem inside_pass (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ)
    {i j : Fin n} (same : g i=g j) (ord : i≤j) :
    key ((blockPass g).eval key x j)<t → key ((blockPass g).eval key x i)<t := by
  obtain ⟨⟨b,v⟩,rfl⟩ := (blockEquiv g).surjective i
  obtain ⟨⟨c,w⟩,rfl⟩ := (blockEquiv g).surjective j
  change g (atBlock g b v)=g (atBlock g c w) at same
  simp only [atBlock_label] at same
  subst c
  intro good
  have order : v.val≤w.val := (atBlock_order g).mp ord
  exact (cut_at g key x t b v).2 (lt_of_le_of_lt order ((cut_at g key x t b w).mp good))

theorem keep_cut (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ)
    (initial : CutPrefix x key t) : CutPrefix ((blockPass g).eval key x) key t := by
  intro i j ij good
  by_cases yes : key (x i)<t
  · exact before_pass g key x t (lo:=i.val+1)
      (fun u hu=>initial u i (show u.val ≤ i.val by omega) yes) i (Nat.lt_succ_self _)
  · exact (after_pass g key x t (hi:=i.val)
      (fun u hu gt=>yes (initial i u hu gt)) j ij good).elim

theorem resolve_cut (g : Fin n → Fin m) (key : α → κ) (x : Fin n → α) (t : κ) {lo hi : ℕ}
    (before : ∀ i : Fin n,i.val<lo → key (x i)<t)
    (after : ∀ i : Fin n,hi ≤ i.val → ¬key (x i)<t)
    (one : ∀ i j : Fin n,lo ≤ i.val → i.val<hi → lo≤j.val → j.val<hi → g i=g j) :
    CutPrefix ((blockPass g).eval key x) key t := by
  intro i j ij good
  by_cases left : i.val<lo
  · exact before_pass g key x t before i left
  by_cases right : hi≤j.val
  · exact (after_pass g key x t after j right good).elim
  exact inside_pass g key x t (one i j (le_of_not_gt left)
    (lt_of_le_of_lt ij (lt_of_not_ge right)) ((le_of_not_gt left).trans ij) (lt_of_not_ge right)) ij good

end Hierarchy.Tagged.SortLift

end
end OAI
