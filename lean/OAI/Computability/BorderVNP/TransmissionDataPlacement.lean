import OAI.Computability.BorderVNP.TransmissionDataAddresses

/-! # Concrete two-word private and live placement tables for cell data slots -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open Function

/-- At a private-site index the table stores its owner and the start of that description's
input word. All out-of-range lookups take the same unused value. -/
def Layout.privatePlacements (d : Layout) (place : d.DestinationKey → ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  if h : i < d.entries then place (.inl ⟨i,h⟩) else (0,0)

/-- At flat team/site index the table stores the owner and the start of the block
receiving this site's genuine live argument fields. -/
def Layout.livePlacements (d : Layout) (place : d.DestinationKey → ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  if h : i < d.teams*d.sites then place (.inr (finProdFinEquiv.symm ⟨i,h⟩)) else (0,0)

/-- The two physical lookup domains partition the typed word keys, even when a team
has zero sites or when there are no private descriptions. -/
theorem Layout.keyPlacement_tabulate (d : Layout) (place : d.DestinationKey → ℕ × ℕ)
    (k : d.DestinationKey) :
    d.keyPlacement (d.privatePlacements place) (d.livePlacements place) k = place k := by
  cases k with
  | inl j => simp [Layout.keyPlacement,Layout.privatePlacements]
  | inr ts =>
    obtain ⟨t,s⟩ := ts
    have index : (finProdFinEquiv (t,s)).val = t.val*d.sites+s.val := by
      simp only [finProdFinEquiv_apply_val, Nat.mul_comm d.sites t.val, Nat.add_comm]
    have fit : t.val*d.sites+s.val < d.teams*d.sites := index ▸ (finProdFinEquiv (t,s)).isLt
    change d.livePlacements place (t.val*d.sites+s.val) = place (.inr (t,s))
    simp only [Layout.livePlacements,dite_eq_left fit]
    rw [show (⟨t.val*d.sites+s.val,fit⟩ : Fin (d.teams*d.sites)) = finProdFinEquiv (t,s) from Fin.ext index.symm,
      Equiv.symm_apply_apply]

/-- Place both kinds of input in one compact bank per cell. The injection into the
full word directory may reserve distinct sections for private metadata and actual
algebraic input ports. There is no requirement that metadata be a tensor argument. -/
noncomputable def BankPlacement.tabulate (d : Layout) {A : Type*} [Fintype A] {cells : ℕ}
    (cell : A → Fin cells) (id : A ↪ ℕ) (width : A → ℕ) (key : d.DestinationKey ↪ A)
    (wordWidths : ∀ k, width (key k) = d.keyWidth k) :
    let place := fun k => ((cell (key k)).val, DataSlabs.base cell id width (key k))
    BankPlacement d (d.privatePlacements place) (d.livePlacements place) A cell id width :=
  ⟨key,wordWidths,fun k => d.keyPlacement_tabulate _ k⟩

end Packing.Directory

end BorderVNP
end Computability
end OAI
