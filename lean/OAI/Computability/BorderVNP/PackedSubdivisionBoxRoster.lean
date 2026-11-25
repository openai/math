import OAI.Computability.BorderVNP.PackedProgramBoxRoster
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Box descriptors at reserved initial subdivision rows

Every original site keeps the same row number and stored box list. The
extra relay rectangle contributes empty box lists at both occupied and
vacant hop slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.BoxRoster

open Crossing Shortening.PublicCapacity CellSparse
open scoped Classical

/-- Extend the static padded site array to the new relay rectangle. -/
def subdivided {s : Shape} {α : Type*} (extra : ℕ) (known : Fin s.sites → List α)
    (i : Fin (s.subdivide extra).sites) :=
  if h : i.val < s.sites then known ⟨i.val,h⟩ else []

variable {D np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {s : Shape} (rows : Rows s N) (route : N.WireRoutes) (extra : ℕ) (fits : ∀ e, route.interior e ≤ extra)
    (ports : P ↪ Fin np) (prior : Site.Programs N) (known : Fin s.sites → List (List Factor))

/-- The genuine initial private program bank realizes the fixed extended roster. -/
theorem subdividePrivatePrograms_roster (old : Realizes rows.site (fun v => (prior v).program.boxes) known) :
    let dir := rows.subdivide route extra fits
    let prog := Subdivision.subdividePrivatePrograms N route rows.edge dir.edge ports prior
    Realizes dir.site (fun v => (prog v).program.boxes) (subdivided extra known) := by
  intro dir prog
  constructor
  · rintro (v|⟨e,j⟩)
    · have id : (dir.site (.inl v)).val = (rows.site v).val := rfl
      rw [subdivided,dite_eq_left (id.trans_lt (rows.site v).isLt)]
      exact old.live v
    · have large : ¬(dir.site (.inr ⟨e,j⟩)).val < s.sites := by
        dsimp only [dir]
        rw [Rows.subdivide_inner]
        omega
      rw [subdivided,dite_eq_right large]
      rfl
  · intro i hi
    unfold subdivided
    split
    · next h =>
      apply old.hole
      rintro ⟨v,hv⟩
      have eqn : (rows.site v).val = i.val := congrArg Fin.val hv
      exact hi ⟨.inl v,Fin.ext eqn⟩
    · rfl

end Packing.Inherited.BoxRoster

end BorderVNP
end Computability
end OAI
