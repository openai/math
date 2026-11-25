import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Finset

/-- Explicit enumeration for a tape layout. -/
structure Series (A : Type) where
  explore : List A
  nodup : explore.Nodup
  complete (a:A) : a ∈ explore

namespace Series
variable {A B C : Type}
def count (s : Series A) := s.explore.length
def tab (s : Series A) (f : A→B) : List B := s.explore.map f
@[simp] theorem elements (s : Series A) (f : A→B) (b : B) :
    b∈s.tab f ↔ ∃ a, f a=b := by simp [tab, s.complete]
@[simp] theorem card (s : Series A) (f : A→B) : (s.tab f).length=s.count := by simp [tab,count]
@[simp] theorem tab_id (s : Series A) : s.tab id=s.explore := by simp [tab]

theorem faithful (s : Series A) : Function.Injective (s.tab (B:=B)) := by
  intro f g e
  funext a
  exact List.map_inj_left.mp e _ (s.complete a)

theorem map_tab (s : Series A) (f : A→B) (g : B→C) :
    List.map g (s.tab f) = s.tab (g ∘ f) := by simp [tab]

/-- view lists of the same length as functions. -/
def follow (s : Series A) (i : Fin s.count) := s.explore[i.val]'i.isLt
theorem unique (s : Series A) : Function.Bijective s.follow := by
  constructor
  · intro ⟨i,hi⟩ ⟨j,hj⟩ h
    apply Fin.ext
    exact (s.nodup.getElem_inj_iff).mp h
  intro y
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp (s.complete y)
  exact ⟨⟨i,hi⟩,e⟩

noncomputable def index (s : Series A) : A ≃ Fin s.count :=
  (Equiv.ofBijective _ s.unique).symm
@[simp] theorem index_symm (s : Series A) (i : Fin s.count) :
    s.index.symm i = s.follow i := rfl
@[simp] theorem index_follow (s : Series A) (i) :
    s.index (s.follow i)=i := Equiv.apply_symm_apply s.index i
@[simp] theorem follow_index (s : Series A) (a) :
    s.follow (s.index a)=a := Equiv.symm_apply_apply s.index a

theorem get (s : Series A) (f : A→B) (i : Fin s.count) (h : i.val<(s.tab f).length) :
    (s.tab f)[i.val]'h = f (s.index.symm i) := by
  simp only [tab, index_symm, follow, List.getElem_map]
  rfl

noncomputable def untab (s : Series A) (l : List B) (h : l.length=s.count) :=
  fun a : A => l[(s.index a).val]'(by have z := (s.index a).isLt; omega)

theorem recover (s : Series A) (l : List B) (h : l.length=s.count) :
    s.tab (s.untab l h) = l := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  let j : Fin s.count := ⟨i,h ▸ hi'⟩
  rw [s.get (s.untab l h) j]
  simp only [untab, Equiv.apply_symm_apply]
  rfl

@[simp] theorem total (s : Series A) [Fintype A] : s.count=Fintype.card A := by
  simpa using (Fintype.card_congr s.index).symm

def fixed (l : List A) (h : l.Nodup) (hf : ∀ a, a ∈ l) : Series A := ⟨l,h,hf⟩
noncomputable def arbitrary (A : Type) [Fintype A] : Series A :=
  fixed Finset.univ.toList (Finset.nodup_toList _) (by simp)

def via (s : Series A) (e : A ≃ B) : Series B :=
  fixed (s.explore.map e) (s.nodup.map e.injective) (by
    intro b
    exact List.mem_map.mpr ⟨e.symm b,s.complete _,by simp⟩)

@[simp] theorem tab_via (s : Series A) (e : A≃B) (f : B→C) :
    (s.via e).tab f = s.tab (f ∘ e) := by simp [via,fixed,tab]
@[simp] theorem count_via (s : Series A) (e : A≃B) : (s.via e).count=s.count := by
  simp [count,via,fixed]

def cart (s : Series A) (t : Series B) : Series (A × B) :=
  fixed (s.explore.product t.explore) (s.nodup.product t.nodup) (by rintro ⟨a,b⟩; exact List.mem_product.mpr ⟨s.complete _, t.complete _⟩)

@[simp] theorem count_cart (s : Series A) (t : Series B) :
    (s.cart t).count=s.count*t.count := List.length_product _ _

theorem grouped (s : Series A) (t : Series B) (w : A×B→C) :
    (s.cart t).tab w = (s.tab (fun a => t.tab (fun b => w (a,b)))).flatten := by
  simp only [tab, cart, fixed]
  induction s.explore with
  | nil => rfl
  | cons x l ih =>
    change ((t.explore.map _ ++ (l.product _)).map w) = _
    simp only [List.map_append, List.map_cons,List.flatten_cons,ih,List.map_map]
    rfl

def natural (n : ℕ) : Series (Fin n) := fixed (List.finRange n)
  (List.nodup_finRange n) (by simp)

@[simp] theorem count_natural (n : ℕ) : (natural n).count=n := by simp

@[simp] theorem get_natural (n : ℕ) (i : Fin n) (h) :
    (natural n).follow ⟨i.val,h⟩=i := by
  simp [natural, follow, fixed]

def one : Series Unit := fixed [()] (by simp) (by simp)
end Series
end Strip

end IntegerMultiplication
end Computability
end OAI
