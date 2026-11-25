import OAI.Hierarchy.TaggedShorterPacking

namespace OAI
/-! # Immutable slot reservations in the next-fit supergroups -/

namespace Hierarchy.TaggedShorterSupergroups
open TaggedShorterPacking

private inductive Located {G : Type*} (size : G → ℕ) : List G → G → ℕ → Prop
  | head (g : G) (xs : List G) : Located size (g::xs) g 0
  | tail (h : G) {xs : List G} {g : G} {b : ℕ} (rest : Located size xs g b) :
    Located size (h::xs) g (size h+b)

private theorem findGroup {G : Type*} (size : G → ℕ) {xs : List G} {g : G} (mem : g ∈ xs) :
    ∃ b,Located size xs g b := by
  induction xs with
  | nil => simp at mem
  | cons h xs ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · exact ⟨0,.head _ _⟩
    · obtain ⟨b,hb⟩ := ih tail
      exact ⟨_,.tail h hb⟩

private theorem fitsAt {G : Type*} {size : G → ℕ} {xs : List G} {g : G} {b : ℕ}
    (atPos : Located size xs g b) : b+size g≤load size xs := by
  induction atPos with
  | head => simp [load]
  | tail _ _ ih =>
    simp only [load,List.map_cons,List.sum_cons] at *
    omega

private theorem separateAt {G : Type*} {size : G → ℕ} {xs : List G} {g g' : G} {b b' i j : ℕ}
    (lhs : Located size xs g b) (rhs : Located size xs g' b')
    (hi : i<size g) (hj : j<size g') (same : b+i=b'+j) : g=g' ∧ i=j := by
  induction xs generalizing g g' b b' with
  | nil => cases lhs
  | cons a xs ih =>
    cases lhs with
    | head =>
      cases rhs with
      | head => exact ⟨rfl,by omega⟩
      | tail => omega
    | tail _ prev =>
      cases rhs with
      | head => omega
      | tail _ other => exact ih prev other hi hj (by omega)

/-- Each old group needs two advice words, its containing bin and its
first socket in that bin. The same directory serves both endpoint roles. -/
structure Directory {G : Type*} (size : G → ℕ) (H : ℕ) where
  groups : ℕ
  group : G → Fin groups
  base : G → ℕ
  fits : ∀g,base g+size g≤H
  separate : ∀g g' i j, group g=group g' → i<size g → j<size g' →
    base g+i=base g'+j → g=g' ∧ i=j

namespace Directory
variable {G : Type*} {size : G → ℕ} {H lanes : ℕ} (d : Directory size H)

def slot (g : G) (i : Fin (size g)) : Fin H :=
  ⟨d.base g+i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (d.fits g)⟩

def place : (Σ g,Fin (size g)) ↪ Fin d.groups × Fin H where
  toFun z := (d.group z.1,d.slot z.1 z.2)
  inj' := by
    rintro ⟨g,i⟩ ⟨g',j⟩ e
    have h := d.separate g g' i.val j.val (congrArg Prod.fst e) i.isLt j.isLt
      (congrArg (fun z : Fin d.groups × Fin H => z.2.val) e)
    obtain ⟨rfl,eq⟩ := h
    exact congrArg (Sigma.mk g) (Fin.ext eq)

/-- One native addition to the pre-scaled immutable group base places
the source or destination port and its padded transport subslot. -/
theorem piece_val (g : G) (i : Fin (size g)) (z : Fin lanes) :
    (d.slot g i).val*lanes+z.val = d.base g*lanes+(i.val*lanes+z.val) := by
  simp [slot,Nat.add_mul,Nat.add_assoc]

end Directory

/-- Construct the two-word directory from the actual next-fit partition. Its
word addresses coincide with disjoint intervals in the fixed supergroup. -/
theorem purchase {G : Type*} (size : G → ℕ) (H : ℕ) (xs : List G)
    (all : ∀g,g∈xs) (room : ∀g,2*size g≤H) :
    ∃ d : Directory size H, d.groups=(pack size H xs).length ∧
      d.groups*H≤2*load size xs+H := by
  classical
  let bins := pack size H xs
  obtain ⟨flat,upper,_⟩ := pack_spec size H xs (fun g _=>room g)
  have locate (g : G) : ∃ t : Fin bins.length,∃ b,Located size (bins.get t) g b := by
    have member : g∈bins.flatten := by rw [show bins.flatten=xs from flat]; exact all g
    obtain ⟨l,hl,mem⟩ := List.mem_flatten.mp member
    obtain ⟨t,ht⟩ := List.mem_iff_get.mp hl
    obtain ⟨b,atPos⟩ := findGroup size mem
    exact ⟨t,b,ht.symm ▸ atPos⟩
  choose grp base here using locate
  refine ⟨⟨bins.length,grp,base,?_,?_⟩,rfl,pack_count size H xs (fun g _=>room g)⟩
  · intro g
    exact (fitsAt (here g)).trans (upper _ (List.get_mem ..))
  · intro g g' i j eq hi hj same
    have other := here g'
    rw [←eq] at other
    exact separateAt (here g) other hi hj same

end Hierarchy.TaggedShorterSupergroups

end OAI
