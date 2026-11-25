import OAI.Computability.BorderVNP.PackedBottomRetainedReports
import OAI.Computability.BorderVNP.PackedGridOwnerBank

/-! # Fine wire reads in an installed, retained original box

Reading the beginning of a physically completed copy recovers the exact
concatenation of its hidden fine wires and its supplied fine ports. The later
site-prefix installation and the compact report suffix preserve this read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

/-- Each true fine address is below the original copy stride. -/
theorem Slab.fine_room (s : Slab) (k : Fin (s.guessed+s.supplied)) : k.val < s.stride :=
  k.isLt.trans_le (s.fineFits.trans (by simp only [Slab.stride,Slab.orig,bottomStride]; omega))

/-- At an original fine-wire address the full copy completion reads the true
guessed or supplied bit, independent of its other padding and reports. -/
theorem Slab.complete_fine (s : Slab) (guess : Fin s.guessed → Bool) (supplied : Fin s.supplied → Bool)
    (input : Fin s.incoming → Bool) (report : Fin s.used → Bool) (k : Fin (s.guessed+s.supplied)) :
    s.complete guess supplied input report ⟨k.val,s.fine_room k⟩ = (finSumFinEquiv.symm k).elim guess supplied := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective k
  rw [Equiv.symm_apply_apply]
  cases j with
  | inl j =>
    change s.complete guess supplied input report ⟨j.val,_⟩ = guess j
    simp only [Slab.complete,dite_eq_left j.isLt]
  | inr j =>
    change s.complete guess supplied input report ⟨s.guessed+j.val,_⟩ = supplied j
    have h : ¬ s.guessed+j.val < s.guessed := by omega
    simp only [Slab.complete,dite_eq_right h,dite_eq_left (Nat.add_lt_add_left j.isLt s.guessed),
      Nat.add_sub_cancel_left]

end Packing.BottomReports

namespace Packing.Inherited.Placement

open Crossing CellSparse CellAddresses BottomReports GridBoxes CellMacro
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {ext : P → ℕ} (N : Network D P ext)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (state : N.Site → Site) (hs : ∀ v,(state v).incoming = incoming N v)
    (g : Fin (guessedSize N cell c) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (work : Work N cell c state)

local notation "aux₀" => Site.size ∘ state
local notation "installed₀" => install N cell c siteID edgeID portID state hs g x work
local notation "bank₀" => bank N cell c aux₀ g installed₀ x

/-- Reading a fine wire in a real installed cell equals the hidden/supplied
value from the canonical original copy, at the row-major absolute address. -/
theorem installed_fine_at (v : {v : N.Site // cell v = c}) {a : Site} (p : a.Retention (state v.val))
    (s : Slab) (copies : ℕ) (size : a.work = copies*s.stride) (birth : Fin a.work → Bool)
    (termInput : Fin (state v.val).incoming → Bool) (complete : work v = p.complete termInput birth)
    (guess : Fin copies → Fin s.guessed → Bool) (supplied : Fin copies → Fin s.supplied → Bool)
    (inputs : Fin copies → Fin s.incoming → Bool) (reports : Fin copies → Fin s.used → Bool)
    (image : ∀ i k, birth ((finProdFinEquiv (i,k)).cast size.symm) =
      s.complete (guess i) (supplied i) (inputs i) (reports i) k)
    (i : Fin copies) (k : Fin (s.guessed+s.supplied)) (tail : List Bool) :
    lookup (bank₀++tail) (siteBase N cell c siteID aux₀ v+i.val*s.stride+k.val) =
      (finSumFinEquiv.symm k).elim (guess i) (supplied i) := by
  let lane : Fin s.stride := ⟨k.val,s.fine_room k⟩
  let j : Fin a.work := (finProdFinEquiv (i,lane)).cast size.symm
  have hj : j.val = i.val*s.stride+k.val := by change k.val+s.stride*i.val = _; ac_rfl
  rw [Nat.add_assoc,← hj]
  apply (installed_birth_at N cell c siteID edgeID portID state hs g x work v p termInput birth complete j tail).trans
  exact (image i lane).trans (s.complete_fine (guess i) (supplied i) (inputs i) (reports i) k)

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
