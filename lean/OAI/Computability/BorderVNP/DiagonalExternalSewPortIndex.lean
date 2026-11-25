import OAI.Computability.BorderVNP.TransmissionExteriorSlots

/-! # The two physical ends of each exterior field

At each processor the partner fields skip the local team. Sorting the two team
names gives the unordered cable, and the comparison retains which end was read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

variable {R : ℕ}

/-- The low team occupies the false end and the high team occupies the true end. -/
def fieldTeam (b : Routing.Block (R+1)) : Bool → Fin (R+1)
  | false => b.val.1
  | true => b.val.2

/-- Each end is distinct from its partner. -/
theorem fieldTeam_ne (b : Routing.Block (R+1)) (s : Bool) :
    fieldTeam b s ≠ fieldTeam b (!s) := by
  cases s
  · exact b.property.ne
  · exact b.property.ne.symm

/-- The partner's local field rank, skipping the current team. -/
def fieldRank (b : Routing.Block (R+1)) (s : Bool) : Fin R :=
  Layout.partnerRank (fieldTeam b s) (fieldTeam b (!s)) (fieldTeam_ne b s)

/-- Decoding the rank reads the opposite end of the same physical field. -/
theorem succAbove_fieldRank (b : Routing.Block (R+1)) (s : Bool) :
    (fieldTeam b s).succAbove (fieldRank b s) = fieldTeam b (!s) :=
  Layout.succAbove_partnerRank ..

/-- Sorting the teams named by a field end recovers the original unordered block. -/
theorem blockOf_fieldTeam (b : Routing.Block (R+1)) (s : Bool) :
    Layout.blockOf (fieldTeam b s) (fieldTeam b (!s)) (fieldTeam_ne b s) = b := by
  cases s <;> apply Subtype.ext <;> simp [Layout.blockOf,fieldTeam,b.property,not_lt_of_gt b.property]

/-- Ordered cable ends are exactly the fields in the team-local partner order. -/
def endpointEquiv (R : ℕ) : Bool × Routing.Block (R+1) ≃ Fin (R+1) × Fin R where
  toFun x := (fieldTeam x.2 x.1, fieldRank x.2 x.1)
  invFun x :=
    let u := x.1
    let v := u.succAbove x.2
    (decide (v < u), Layout.blockOf u v (u.ne_succAbove x.2))
  left_inv := by
    rintro ⟨s,b⟩
    dsimp only
    simp only [succAbove_fieldRank]
    apply Prod.ext
    · cases s <;> simp [fieldTeam,b.property,not_lt_of_gt b.property]
    · exact blockOf_fieldTeam b s
  right_inv := by
    rintro ⟨u,k⟩
    let v := u.succAbove k
    have hne : u ≠ v := u.ne_succAbove k
    have hr : Layout.partnerRank u v hne = k := by
      apply Fin.succAbove_right_injective
      exact Layout.succAbove_partnerRank ..
    change (fieldTeam (Layout.blockOf u v hne) (decide (v < u)),
      fieldRank (Layout.blockOf u v hne) (decide (v < u))) = (u,k)
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [Layout.blockOf,h,not_lt_of_gt h,fieldTeam,fieldRank] using hr
    · simpa [Layout.blockOf,h,not_lt_of_gt h,fieldTeam,fieldRank] using hr

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
