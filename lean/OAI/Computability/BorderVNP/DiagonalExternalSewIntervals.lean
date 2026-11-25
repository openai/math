import OAI.Computability.BorderVNP.PackedDeliveries
import Mathlib.Data.Finset.Sort

/-! # Ordered intervals shared by a pair of exterior fields

At offset `j`, the two ends may fall in different blocks of their respective
teams. A public cable is one nonempty intersection with a block at each end.
Its bits retain their original order in the field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Finset
open scoped Classical

variable {F : Type} {link : ℕ} (start : F → Bool → ℕ) (g : ℕ)

/-- The two site blocks containing offset `j` of a paired field. -/
def blockPair (f : F) (j : Fin link) : ℕ × ℕ :=
  ((start f false + j.val) / g, (start f true + j.val) / g)

/-- Only occupied pairs of site blocks receive a cable. -/
def Pieces (link : ℕ) := Σ f : F, ↥(Finset.univ.image (blockPair (link := link) start g f))

instance [Fintype F] : Fintype (Pieces start g link) :=
  inferInstanceAs (Fintype (Σ f : F, ↥(Finset.univ.image (blockPair (link := link) start g f))))

/-- Offsets in one cable, measured in the original ordered link field. -/
def pieceOffsets (c : Pieces start g link) : Finset (Fin link) :=
  univ.filter fun j => blockPair start g c.1 j = c.2.val

/-- Number of actual bit wires represented by one public cable. -/
def pieceWidth (c : Pieces start g link) : ℕ := (pieceOffsets start g c).card

/-- Every public cable contains at least one bit. -/
theorem pieceWidth_pos (c : Pieces start g link) : 0 < pieceWidth start g c := by
  obtain ⟨j, _, hj⟩ := mem_image.mp c.2.property
  exact card_pos.mpr ⟨j, by simp [pieceOffsets,hj]⟩

/-- Original ordered offset of a particular cable bit. -/
def pieceOffset (c : Pieces start g link) (j : Fin (pieceWidth start g c)) : Fin link :=
  ((pieceOffsets start g c).orderIsoOfFin rfl j).val

/-- Both ends agree on the original order of the bits in a cable. -/
theorem pieceOffset_strictMono (c : Pieces start g link) : StrictMono (pieceOffset start g c) :=
  fun _ _ h => ((pieceOffsets start g c).orderIsoOfFin rfl).strictMono h

/-- Both block addresses are constant throughout an ordered cable. -/
theorem pieceOffset_blocks (c : Pieces start g link) (j : Fin (pieceWidth start g c)) :
    blockPair start g c.1 (pieceOffset start g c j) = c.2.val :=
  (mem_filter.mp (((pieceOffsets start g c).orderIsoOfFin rfl j).property)).2

/-- Grouping by both endpoint blocks preserves every bit of every field exactly once. -/
noncomputable def pieceBits : (Σ c : Pieces start g link, Fin (pieceWidth start g c)) ≃ F × Fin link where
  toFun x := (x.1.1, pieceOffset start g x.1 x.2)
  invFun x :=
    let c : Pieces start g link := ⟨x.1, ⟨blockPair start g x.1 x.2, mem_image_of_mem _ (mem_univ _)⟩⟩
    ⟨c, ((pieceOffsets start g c).orderIsoOfFin rfl).symm ⟨x.2, by simp [pieceOffsets,c]⟩⟩
  left_inv := by
    rintro ⟨⟨f,⟨p,hp⟩⟩,j⟩
    have he := pieceOffset_blocks start g (⟨f,⟨p,hp⟩⟩ : Pieces start g link) j
    dsimp only at he ⊢
    generalize hz : pieceOffset start g (⟨f,⟨p,hp⟩⟩ : Pieces start g link) j = z at he ⊢
    subst p
    congr 1
    apply ((pieceOffsets start g _).orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    exact Subtype.ext hz.symm
  right_inv := by
    rintro ⟨f,j⟩
    simp [pieceOffset]

/-- The cable contains all offsets between any two of its offsets. -/
theorem pieceOffsets_between (c : Pieces start g link) {i j k : Fin link}
    (hi : i ∈ pieceOffsets start g c) (hk : k ∈ pieceOffsets start g c) (hij : i ≤ j) (hjk : j ≤ k) :
    j ∈ pieceOffsets start g c := by
  have h₁ := (mem_filter.mp hi).2
  have h₂ := (mem_filter.mp hk).2
  have ht (s : Bool) : (start c.1 s + i.val)/g = (start c.1 s + j.val)/g := by
    apply Nat.le_antisymm (Nat.div_le_div_right (Nat.add_le_add_left hij _))
    apply (Nat.div_le_div_right (Nat.add_le_add_left hjk _)).trans_eq
    cases s
    · exact congrArg Prod.fst (h₂.trans h₁.symm)
    · exact congrArg Prod.snd (h₂.trans h₁.symm)
  exact mem_filter.mpr ⟨mem_univ _, (Prod.ext (ht false).symm (ht true).symm).trans h₁⟩

/-- All wires meeting one source block fit in its `g` bit slots. -/
theorem pieceWidth_le (hg : 0 < g) (c : Pieces start g link) : pieceWidth start g c ≤ g := by
  let off (j : Fin (pieceWidth start g c)) : Fin g :=
    ⟨(start c.1 false + (pieceOffset start g c j).val) % g, Nat.mod_lt _ hg⟩
  have hinj : Function.Injective off := by
    intro i j h
    have hi := congrArg Prod.fst (pieceOffset_blocks start g c i)
    have hj := congrArg Prod.fst (pieceOffset_blocks start g c j)
    have hdiv := hi.trans hj.symm
    change (start c.1 false + (pieceOffset start g c i).val)/g =
      (start c.1 false + (pieceOffset start g c j).val)/g at hdiv
    have hmod := congrArg Fin.val h
    dsimp [off] at hmod
    have h₁ := Nat.div_add_mod' (start c.1 false + (pieceOffset start g c i).val) g
    have h₂ := Nat.div_add_mod' (start c.1 false + (pieceOffset start g c j).val) g
    rw [hdiv,hmod] at h₁
    exact (pieceOffset_strictMono start g c).injective (Fin.ext (by omega))
  simpa using Fintype.card_le_of_injective off hinj

/-- Clipped field-relative start and exclusive end for a pair of block records. -/
def pieceBounds (c : Pieces start g link) : ℕ × ℕ :=
  let a := c.2.val.1 * g
  let b := c.2.val.2 * g
  (max (a - start c.1 false) (b - start c.1 true),
    min link (min (a + g - start c.1 false) (b + g - start c.1 true)))

/-- The two endpoint block numbers determine the interval by elementary address
arithmetic, including partial blocks at both ends. -/
theorem mem_pieceBounds (hg : 0 < g) (c : Pieces start g link) (j : Fin link) :
    j ∈ pieceOffsets start g c ↔ (pieceBounds start g c).1 ≤ j.val ∧ j.val < (pieceBounds start g c).2 := by
  simp only [pieceOffsets,mem_filter,mem_univ,true_and,blockPair,Prod.ext_iff,
    Nat.div_eq_iff hg,pieceBounds, max_le_iff,lt_min_iff]
  have := j.isLt
  omega

private def intervalBit (c : Pieces start g link) (j : Fin ((pieceBounds start g c).2 - (pieceBounds start g c).1)) :
    Fin link :=
  ⟨(pieceBounds start g c).1+j.val, by
    have hj := j.isLt
    have h : (pieceBounds start g c).2 ≤ link := Nat.min_le_left _ _
    omega⟩

/-- The public interval width is the difference of its two clipped endpoints. -/
theorem pieceWidth_eq_bounds (hg : 0 < g) (c : Pieces start g link) :
    pieceWidth start g c = (pieceBounds start g c).2 - (pieceBounds start g c).1 := by
  let lo := (pieceBounds start g c).1
  let hi := (pieceBounds start g c).2
  let E : Fin (hi-lo) ≃ ↥(pieceOffsets start g c) := {
    toFun j := ⟨intervalBit start g c j,(mem_pieceBounds _ _ hg _ _).mpr (by
      change lo ≤ lo+j.val ∧ lo+j.val < hi
      have := j.isLt
      omega)⟩
    invFun j := ⟨j.val.val-lo,by
      have h := (mem_pieceBounds _ _ hg _ _).mp j.property
      change lo ≤ j.val.val ∧ j.val.val < hi at h
      omega⟩
    left_inv j := Fin.ext (by change lo+j.val-lo = j.val; omega)
    right_inv j := Subtype.ext (Fin.ext (by
      have h := (mem_pieceBounds _ _ hg _ _).mp j.property
      change lo ≤ j.val.val ∧ _ at h
      change lo + (j.val.val-lo) = j.val.val
      omega)) }
  simpa only [pieceWidth,Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr E).symm

/-- The `j`th shared bit is located by a single addition to the clipped start. -/
theorem pieceOffset_eq_start_add (hg : 0 < g) (c : Pieces start g link) (j : Fin (pieceWidth start g c)) :
    (pieceOffset start g c j).val = (pieceBounds start g c).1 + j.val := by
  let next (i : Fin (pieceWidth start g c)) := intervalBit start g c (Fin.cast (pieceWidth_eq_bounds _ _ hg c) i)
  have belongs (i : Fin (pieceWidth start g c)) : next i ∈ pieceOffsets start g c := by
    apply (mem_pieceBounds _ _ hg _ _).mpr
    change (pieceBounds start g c).1 ≤ (pieceBounds start g c).1+i.val ∧
      (pieceBounds start g c).1+i.val < (pieceBounds start g c).2
    have hi := i.isLt
    have he := pieceWidth_eq_bounds start g hg c
    omega
  have mono : StrictMono next := fun _ _ h => Nat.add_lt_add_left h _
  have he := Finset.orderEmbOfFin_unique (s := pieceOffsets start g c) rfl belongs mono
  exact congrArg Fin.val (congrFun he j).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
