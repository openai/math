import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.DiagonalExternalSewPhysical
import OAI.Computability.BorderVNP.DiagonalExternalSewPhysicalVolume

/-! # Original fine input lane of a terminal team tile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.TileRuns

open scoped Classical

variable {R r w link g : ℕ}

/-- Fine inputs after sewing, with both ends of a cable distinguished. -/
abbrev Slot (R r w link g : ℕ) :=
  FreePort R r w ⊕ (Bool × Σ c : Cables R r w link g, Fin (cableWidth c))

/-- Decode the public port of a free bit or a physical cable bit. -/
noncomputable def port (R r w link g : ℕ) : Slot R r w link g ≃ PublicPort R r w link :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.refl Bool).prodCongr (cableBits R r w link g))).trans
    (publicPortEquiv R r w link)

/-- The slot at a lane of a tile, including the unoccupied suffix of the final tile. -/
noncomputable def lookup (u : Fin (R+1)) (tile : ℕ) (j : Fin g) : Option (Slot R r w link g) :=
  if h : tile*g+j.val < r*(2*w+R*link) then
    some ((port R r w link g).symm (u,finProdFinEquiv.symm ⟨tile*g+j.val,h⟩)) else none

/-- An occupied lane is identified uniquely by its original team and ordinal. -/
theorem lookup_some (u : Fin (R+1)) (tile : ℕ) (j : Fin g) (a : Slot R r w link g) :
    lookup u tile j = some a ↔ (port R r w link g a).1 = u ∧
      (teamOrdinal (port R r w link g a)).val = tile*g+j.val := by
  unfold lookup
  split
  next h =>
    rw [Option.some.injEq,Equiv.symm_apply_eq]
    constructor
    · intro H
      rw [← H]
      exact ⟨rfl,congrArg Fin.val (finProdFinEquiv.apply_symm_apply _)⟩
    · rintro ⟨hu,hj⟩
      exact Prod.ext hu.symm (finProdFinEquiv.symm_apply_eq.mpr (Fin.ext hj.symm))
  next h =>
    constructor
    · intro H; cases H
    · rintro ⟨_,hj⟩
      exact (h (hj ▸ (teamOrdinal (port R r w link g a)).isLt)).elim

/-- Unoccupied lanes are exactly those after the processor array. -/
theorem lookup_none (u : Fin (R+1)) (tile : ℕ) (j : Fin g) :
    lookup (r := r) (w := w) (link := link) u tile j = none ↔ r*(2*w+R*link) ≤ tile*g+j.val := by
  unfold lookup
  split <;> simp_all

/-- A retained free lane has the same physical tile and within-tile offset. -/
theorem lookup_free_lane {V : ℕ} (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (u : Fin (R+1)) (tile : Fin V) (j : Fin g) (f : FreePort R r w)
    (h : lookup (link := link) u tile.val j = some (.inl f)) :
    freeLane hg room f = ⟨(u,tile),j⟩ := by
  obtain ⟨hu,hj⟩ := (lookup_some ..).mp h
  change (publicPortEquiv R r w link (.inl f)).1 = u at hu
  change (teamOrdinal (publicPortEquiv R r w link (.inl f))).val = tile.val*g+j.val at hj
  let p := publicPortEquiv R r w link (.inl f)
  have div : (teamOrdinal p).val/g = tile.val := (Nat.div_eq_iff hg).mpr (by dsimp [p]; rw [hj]; have := j.isLt; omega)
  have rem : (teamOrdinal p).val%g = j.val := by
    have H := Nat.div_add_mod' (teamOrdinal p).val g
    rw [div] at H
    dsimp only [p] at H ⊢
    omega
  exact Sigma.ext (Prod.ext hu (Fin.ext div)) (heq_of_eq (Fin.ext rem))

/-- Absolute processor-array position of the first lane of this directed cable end. -/
def cableStart (s : Bool) (c : Cables R r w link g) :=
  c.1.2.val*(2*w+R*link)+w+(fieldRank c.1.1 s).val*link + (pieceBounds (fieldStart w (2*w+R*link) link) g c).1

/-- Cable bit ordinals form an affine interval in the original physical input. -/
theorem cable_ordinal (hg : 0 < g) (s : Bool) (c : Cables R r w link g) (j : Fin (cableWidth c)) :
    (teamOrdinal (port R r w link g (.inr (s,⟨c,j⟩)))).val = cableStart s c+j.val := by
  change (teamOrdinal (publicPortEquiv R r w link (.inr (s,c.1.1,c.1.2,pieceOffset _ _ c j)))).val = _
  rw [publicPortEquiv_exterior,teamOrdinal_val]
  dsimp only
  rw [pieceOffset_eq_start_add _ _ hg c j]
  change c.1.2.val*(2*w+R*link)+(w+((fieldRank c.1.1 s).val*link+_)) =
    c.1.2.val*(2*w+R*link)+w+(fieldRank c.1.1 s).val*link+_+j.val
  omega

/-- The team at a sewn cable end is the same original team at each lane. -/
theorem cable_team (s : Bool) (c : Cables R r w link g) (j : Fin (cableWidth c)) :
    (port R r w link g (.inr (s,⟨c,j⟩))).1 = fieldTeam c.1.1 s := by
  change (publicPortEquiv R r w link (.inr (s,c.1.1,c.1.2,pieceOffset _ _ c j))).1 = _
  rw [publicPortEquiv_exterior]

/-- A positive lookup belongs to the physical endpoint's tile. -/
theorem lookup_fieldBlock (u : Fin (R+1)) (tile : ℕ) (k : Fin g) (s : Bool) (c : Cables R r w link g)
    (j : Fin (cableWidth c)) (h : lookup u tile k = some (.inr (s,⟨c,j⟩))) :
    fieldBlock w (2*w+R*link) link g c s = (u,tile) := by
  have hg : 0 < g := Nat.zero_lt_of_lt k.isLt
  obtain ⟨hu,hj⟩ := (lookup_some ..).mp h
  rw [cable_team] at hu
  change (teamOrdinal (publicPortEquiv R r w link (.inr (s,c.1.1,c.1.2,pieceOffset _ _ c j)))).val = _ at hj
  rw [publicPortEquiv_exterior,teamOrdinal_val] at hj
  rw [fieldBlock_bit w (2*w+R*link) link g c s j]
  apply Prod.ext hu
  apply (Nat.div_eq_iff hg).mpr
  dsimp only at hj ⊢
  have := k.isLt
  omega

end Diagonal.ExternalSew.TileRuns

end BorderVNP
end Computability
end OAI
