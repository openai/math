import OAI.Computability.BorderVNP.RoutingISATypedTaskMemory

/-! # Compact local task ordinals and the full set of owned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open scoped Classical

variable (l : Layout) (mem : ℕ → ℕ)

/-- Global cells owned by the executing team. -/
abbrev Owned := {c : Fin l.cells // l.owner mem c.val=l.team}

/-- Map a global owned cell to its native local task-table position. -/
noncomputable def ownedOrder : Owned l mem ≃ Fin (l.before mem l.cells) :=
  let f (c : Owned l mem) : Fin (l.before mem l.cells) :=
    ⟨l.before mem c.val.val,l.before_strict mem c.val.isLt c.property⟩
  Equiv.ofBijective f ⟨by
    intro a b h
    have he : l.before mem a.val.val = l.before mem b.val.val := congrArg Fin.val h
    apply Subtype.ext; apply Fin.ext
    rcases lt_trichotomy a.val.val b.val.val with h|h|h
    · have := l.before_strict mem h a.property; omega
    · exact h
    · have := l.before_strict mem h b.property; omega,
    by intro j; obtain ⟨c,hc,ho,hj⟩ := l.before_surjective mem j.isLt; exact ⟨⟨⟨c,hc⟩,ho⟩,Fin.ext hj⟩⟩

/-- The global cell referred to by a task of the compact local scan. -/
noncomputable def globalCell (j : ℕ) : ℕ :=
  if h : j < l.before mem l.cells then ((ownedOrder l mem).symm ⟨j,h⟩).val.val else 0

/-- Within the true table each decoded cell is owned and has precisely the requested local ordinal. -/
theorem global_spec {j : ℕ} (hj : j < l.before mem l.cells) :
    globalCell l mem j < l.cells ∧ l.owner mem (globalCell l mem j)=l.team ∧
      l.before mem (globalCell l mem j)=j := by
  rw [globalCell,dite_eq_left hj]
  let u := (ownedOrder l mem).symm ⟨j,hj⟩
  exact ⟨u.val.isLt,u.property,congrArg Fin.val ((ownedOrder l mem).apply_symm_apply ⟨j,hj⟩)⟩

/-- Every owned global cell points back to its unique emitted task row. -/
theorem global_at {c : ℕ} (hc : c < l.cells) (ho : l.owner mem c=l.team) :
    globalCell l mem (l.before mem c)=c := by
  let u : Owned l mem := ⟨⟨c,hc⟩,ho⟩
  rw [globalCell,dite_eq_left (l.before_strict mem hc ho)]
  exact congrArg (fun v : Owned l mem => v.val.val) ((ownedOrder l mem).symm_apply_apply u)

/-- Exact per-team work, data lengths, or other additive charges reindexed by global owner. -/
theorem sum_owned {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ j : Fin (l.before mem l.cells), f (globalCell l mem j.val)) =
      ∑ c : Fin l.cells, if l.owner mem c.val=l.team then f c.val else 0 := by
  rw [← (ownedOrder l mem).sum_comp]
  have he (u : Owned l mem) : globalCell l mem ((ownedOrder l mem) u).val = u.val.val :=
    global_at l mem u.val.isLt u.property
  simp only [he]
  rw [← Finset.sum_filter,Finset.sum_subtype (p := fun c : Fin l.cells => l.owner mem c.val=l.team) _
    (fun _ => by simp) (fun c => f c.val)]

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
