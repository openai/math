import OAI.Computability.BorderVNP.DiagonalNativeCorePaths

/-! # Guard evaluation is independent of unused public owner rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing CellSparse BankBoxOrdinal
open scoped Classical

variable {V : Type} {ns : ℕ} (row : V ↪ Fin ns) (owner owner' : Fin ns → ℕ)
    (same : ∀ v, owner (row v) = owner' (row v))

include same in
/-- Reading a physical owner table in row order selects the same site list
whenever its entries at occupied indices agree. -/
theorem sites_congr_occupied (c : ℕ) : sites row owner c = sites row owner' c := by
  unfold sites
  generalize List.finRange ns = indices
  induction indices with
  | nil => rfl
  | cons i is ih =>
    cases hi : Function.partialInv row i with
    | none =>
      by_cases h : owner i = c <;> by_cases h' : owner' i = c <;> simp [h,h',hi,ih]
    | some v =>
      have live : row v = i := (row.injective.isPartialInv v i).mp hi
      have eqn : owner i = owner' i := live ▸ same v
      by_cases h : owner' i = c <;> simp [eqn,h,hi,ih]

include same in
/-- The stable prefix of boxes counts only occupied slots preceding the
selected site and therefore has the same absolute directory ordinal. -/
theorem firstBox_congr_occupied (state : V → Site) (v : V) :
    firstBox row owner state v = firstBox row owner' state v := by
  unfold firstBox base
  apply Finset.sum_congr rfl
  intro i _
  cases hi : Function.partialInv row i with
  | none => simp [slots,hi]
  | some u =>
    have live : row u = i := (row.injective.isPartialInv u i).mp hi
    rw [←live,same u,same v]

variable {D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : N.Site → Site)

/-- The whole compiled cell directory is unchanged on varying owner bits
outside the physical site's image. All merged box references remain correct. -/
theorem directory_congr_occupied (owner owner' : Fin ns → ℕ) (agree : ∀ v, owner (siteID v) = owner' (siteID v))
    (c : ℕ) (reports : List (List ℕ)) :
    directory owner N cell siteID edgeID portID state c reports =
      directory owner' N cell siteID edgeID portID state c reports := by
  unfold directory
  rw [sites_congr_occupied siteID owner owner' agree,funext (firstBox_congr_occupied siteID owner owner' agree state)]

/-- The private record guard reads the compiled box and record sections;
changing the later subtotal address vectors leaves its observations equal. -/
theorem guardedObservations_congr_occupied (owner owner' : Fin ns → ℕ) (agree : ∀ v, owner (siteID v) = owner' (siteID v))
    (c : ℕ) (reports reports' : List (List ℕ)) (bank : ℕ → Bool) :
    (directory owner N cell siteID edgeID portID state c reports).guardedObservations bank =
      (directory owner' N cell siteID edgeID portID state c reports').guardedObservations bank := by
  rw [directory_congr_occupied N cell siteID edgeID portID state owner owner' agree c reports]
  rfl

end Packing.Inherited.FinalCell

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited Diagonal.CellEntries CellSparse
open scoped Classical

variable {D C ns ne np n d blocks b h K s : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)

/-- The joint raw-bank guard on each real cell can be frozen at the true
owner of each occupied vertex; all unused owner rows and all later tally
address vectors are immaterial to this exact Boolean path predicate. -/
theorem guardedCores_congr_occupied (owner owner' : Fin ns → ℕ) (agree : ∀ v, owner (siteID v) = owner' (siteID v))
    (reports reports' : Fin C → List (List ℕ)) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    GuardedCores N cell siteID edgeID portID state owners slot ports owner reports q raw ↔
      GuardedCores N cell siteID edgeID portID state owners slot ports owner' reports' q raw := by
  unfold GuardedCores
  apply and_congr_right
  intro _
  apply forall_congr'
  intro c
  rw [FinalCell.guardedObservations_congr_occupied N (fun v => (cell v).val) siteID edgeID portID
    (fun v => (state v).program) owner owner' agree c.val (reports c) (reports' c)]

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
