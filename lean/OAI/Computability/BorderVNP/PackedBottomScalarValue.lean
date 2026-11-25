import OAI.Computability.BorderVNP.PackedBottomBoxValue
import OAI.Computability.BorderVNP.PackedBottomScalarWiring

/-! # Scalar contraction at a padded grouped bottom site

The two private padding ranges and the public incidence ties give a unique
extension of each tuple of fine wire guesses when the exterior grid padding
passes. The original scalar tables then read precisely their physical
fine-wire lanes in each copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "W" => wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "slab₀" => scalarSlab (src := src) (dst := dst) (H := H) N cell position width owner v

/-- Read one copy's true incidence vector from the cable-major repeated public input. -/
noncomputable def scalarSlice (copies : ℕ) (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool)
    (i : Fin copies) (j : Fin (incoming G v)) : Bool :=
  input (sourceOrder (BottomRepeat.wide G copies) channelID groupID v
    (BottomRepeat.repeatInput G v copies i ((sourceOrder G channelID groupID v).symm j)))

local notation "slice₀" => scalarSlice (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v

/-- Pull back the true grouped input to the compact fine supplied lanes. -/
noncomputable def scalarFine (copies : ℕ) (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool)
    (i : Fin copies) (j : Fin (suppliedSize N cell v)) : Bool := slice₀ copies input i (fineIndex j)

local notation "fine₀" => scalarFine N cell position pack width owner lane aligned edgeID portID channelID groupID v

/-- The unique physical work prefix for a tuple of independent original fine-wire guesses. -/
noncomputable def scalarWork (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool)
    (g : Fin copies → Fin (guessedSize N cell v) → Bool) :
    Fin (copies*(slab₀ capFine fit).stride) → Bool :=
  ((slab₀ capFine fit).checkedGuessEquiv copies (fine₀ copies input) (slice₀ copies input) (fun _ => Fin.elim0) g).val

local notation "work₀" => scalarWork N cell position pack width owner lane aligned edgeID portID channelID groupID v

private theorem pair_value {a b : ℕ} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i,j)).val = i.val*b+j.val := by change j.val+b*i.val = _; ac_rfl

private theorem work_bit {a b d : ℕ} (work : Fin (a*b) → Bool) (input : Fin d → Bool) (i : Fin a) (k : Fin b) :
    bits work input (i.val*b+k.val) = work (finProdFinEquiv (i,k)) := by
  rw [← pair_value i k]
  exact bits_left work input _

private theorem checked_lane (s : Slab) (b : ℕ) (u : Fin b → Fin s.supplied → Bool)
    (x : Fin b → Fin s.incoming → Bool) (use : Fin b → Fin s.used → Bool)
    (g : Fin b → Fin s.guessed → Bool) (i : Fin b) (k : Fin s.stride) :
    ((s.checkedGuessEquiv b u x use g).val) (finProdFinEquiv (i,k)) =
      s.complete (g i) (u i) (x i) (use i) k := by
  change s.complete _ _ _ _ _ = _
  simp only [Equiv.symm_apply_apply]

/-- The actual physical fine-wire read on the canonical extended work bank equals
the one-copy fine assignment used by the source site's own local factors. -/
theorem scalarWork_fine (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool)
    (g : Fin copies → Fin (guessedSize N cell v) → Bool) (i : Fin copies)
    (k : Fin (GridBoxes.stride N cell v)) :
    bits (work₀ copies capFine fit input g) input (i.val*(slab₀ capFine fit).stride+k.val) =
      copyBits N cell v (g i) (fine₀ copies input i) k := by
  let s := slab₀ capFine fit
  have hfit : GridBoxes.stride N cell v ≤ s.stride := by
    change _ ≤ (capFine+incoming G v)+0
    omega
  let j : Fin s.stride := ⟨k.val,k.isLt.trans_le hfit⟩
  rw [work_bit (work₀ copies capFine fit input g) input i j]
  refine (checked_lane s copies (fine₀ copies input) (slice₀ copies input) (fun _ => Fin.elim0) g i j).trans ?_
  obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective k
  rcases z with a | b
  · simp only [copyBits,Equiv.symm_apply_apply,Sum.elim_inl]
    change (s.complete _ _ _ _ ⟨a.val,_⟩) = _
    have ha : a.val < s.guessed := a.isLt
    simp only [Slab.complete,dite_eq_left ha]
    rfl
  · simp only [copyBits,Equiv.symm_apply_apply,Sum.elim_inr]
    change s.complete _ _ _ _ ⟨s.guessed+b.val,_⟩ = _
    have hb : b.val < s.supplied := b.isLt
    simp only [Slab.complete,Nat.not_lt.mpr (Nat.le_add_right s.guessed b.val),dite_false,
      dite_eq_left (Nat.add_lt_add_left hb s.guessed),Nat.add_sub_cancel_left]
    rfl

/-- The physical scalar site, with one immutable fine table list and the real
fine ties, zeroes and public cable padding, computes the product over copies
summed over independent original wire guesses. -/
theorem scalarBox_value {R : Type*} [CommSemiring R] (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine)
    (fs : List Factor) (entry : (Bool × Option ℕ) → R) (neutral : entry (false,none) = 1)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool) :
    let s := slab₀ capFine fit
    (BottomRepeat.bornWith G channelID groupID v copies capFine s.stride (fs ++ W capFine)).value
      (fun os => (os.map entry).prod) input =
      if ∀ i, publicPad N cell position pack width owner channelID groupID v (slice₀ copies input i) then
        ∑ g : Fin copies → Fin (guessedSize N cell v) → Bool,
        ∏ c : Fin copies, BottomRepeat.boxProduct entry fs (bits (work₀ copies capFine fit input g) input) s.stride c.val
      else 0 := by
  intro s
  refine (BottomRepeat.bornWith_value_reindex G channelID groupID v copies s fs (W capFine) input
    (fine₀ copies input) (slice₀ copies input) (fun _ => Fin.elim0)
    (∀ i, publicPad N cell position pack width owner channelID groupID v (slice₀ copies input i))
    entry ?_ ?_).trans ?_
  · intro f hf bank off copy o ho
    rw [wiring_neutral N cell position pack width owner lane aligned edgeID portID channelID groupID v
      capFine f hf bank off copy o ho,neutral]
  · intro work
    have h := nonreport_wiring_iff N cell position pack width owner lane aligned edgeID portID channelID groupID v
      copies capFine fit (bits work input) [fs ++ W capFine]
    have hs : copyInput (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
        copies s.stride (bits work input) = slice₀ copies input := by
      funext i k
      apply bits_right
    dsimp only at h
    rw [hs] at h
    apply h.trans
    apply and_congr_left
    intro _
    apply forall_congr'
    intro c
    let read₁ := fun j => bits work input (c.val*s.stride+j)
    let read₂ := fun j => if hk : j < s.stride then work (finProdFinEquiv (c,⟨j,hk⟩)) else false
    refine (s.checks_iff read₁ (fine₀ copies input c) (slice₀ copies input c) Fin.elim0).trans
      (Iff.trans ?_ (s.checks_iff read₂ (fine₀ copies input c) (slice₀ copies input c) Fin.elim0).symm)
    have he : (fun k : Fin s.stride => bits work input (c.val*s.stride+k.val)) =
        fun k => if hk : k.val < s.stride then work (finProdFinEquiv (c,⟨k.val,hk⟩)) else false := by
      funext k
      simp only [k.isLt,dite_true,Fin.eta]
      exact work_bit work input c k
    exact Iff.of_eq (congrArg (s.Lanes (fine₀ copies input c) (slice₀ copies input c) Fin.elim0) he)
  · split_ifs <;> rfl

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
