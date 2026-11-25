import OAI.Computability.BorderVNP.DiagonalNativeCellRoster
import OAI.Computability.BorderVNP.DiagonalNativeTypedContinuation

/-! # Joining the real owned call rows of every completed positive team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CompactMachine CellDispatch CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {dim box lanes selectors symbols w n teams C : ℕ}
    {id : TableEntry dim box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (S : Fin teams → PositiveTeam id gen n w) (p : ∀ u, (S u).Prefix)

/-- The row owners in global cell order, extended beyond the occupied rows for
the natural-number-indexed native memory. -/
def ownerWord (owner : Fin C → Fin teams) (i : ℕ) :=
  if h : i < C then (owner ⟨i,h⟩).val else 0

/-- The real dispatched cell at its owning team's prefix. In particular, different
teams' bottom report choices are never identified by this construction. -/
noncomputable abbrev cellOfOwner (owner : Fin C → Fin teams) (c : Fin C) :=
  ((S (owner c)).generated (p (owner c))).cell c.val

/-- Recover the true post-serialization roster from the native typed entry that
ends this positive team's actual preparation. -/
theorem ownerTable_at_prefix (u : Fin teams) (f : Frame) (owner : ℕ → ℕ) :
    let T := S u
    let a := p u
    let mac := install gen n T.routines
    let v := (SignedPrep.visitsEquiv id T.pub mac (T.pins a.1).val.2.1 (T.pins a.1).val.2.2).symm a.2
    let cut := SignedPrep.typedParts id T.pub mac v
    ∀ _ : TypedRowsAt gen n T.pub cut.1.val.2.2,
      OwnerTable T.pub cut.1.val.2.2 f owner → OwnerTable T.pub (T.postMemory a) f owner := by
  intro T a mac v cut rows table
  have kept := table.typed rows cut.2
  have state := SignedPrep.typedParts_state id T.pub mac v
  rw [show SignedPrep.visitsEquiv id T.pub mac (T.pins a.1).val.2.1 (T.pins a.1).val.2.2 v = a.2 from
    Equiv.apply_symm_apply _ _] at state
  change OwnerTable T.pub a.2.val.2.2 f owner
  rw [← congrArg Prod.snd state]
  exact kept

/-- A tuple of actual positive preparations enumerates the same finite cells by
physical ordinal. Each cell's logical input is read on its sole owning team.
This applies to every report assignment before the private calls or tally checks. -/
noncomputable def joinOwnedRows (owner : Fin C → Fin teams) (base : Fin teams → ℕ)
    (table : ∀ u, OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,base u,C⟩ (ownerWord owner)) :
    JoinedCells (fun u => (S u).pub) (fun u => (S u).postMemory) (fun u => (S u).generated) p where
  Cell := Fin C
  order u := finCongr (congrArg Frame.count (table u).frame)
  owner := owner
  cells := cellOfOwner S p owner
  teamAt u := congrArg Frame.team (table u).frame
  ownerAt u i := by
    have bound : i.val < C := i.isLt.trans_eq (congrArg Frame.count (table u).frame)
    have word := (table u).atRow i.val bound
    rw [ownerWord,dite_eq_left bound] at word
    change readings _ ((Frame.ofMemory _ _).address i.val) = _
    rw [congrArg (fun f : Frame => f.address i.val) (table u).frame]
    exact word
  cellAt u i own := by
    change ((S u).generated (p u)).cell i.val =
      ((S (owner ((finCongr (congrArg Frame.count (table u).frame)) i))).generated
        (p (owner ((finCongr (congrArg Frame.count (table u).frame)) i)))).cell i.val
    rw [own]

/-- The directory and private/end/report bits on the joined cell are precisely
those of its owning team's native generated row at the original ordinal. -/
theorem joined_owned_input (owner : Fin C → Fin teams) (base : Fin teams → ℕ)
    (table : ∀ u, OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,base u,C⟩ (ownerWord owner))
    (c : Fin C) : (joinOwnedRows S p owner base table).cells c = ((S (owner c)).generated (p (owner c))).cell c.val :=
  rfl

end RoutingISA.Evaluator.PositiveTeam

end BorderVNP
end Computability
end OAI
