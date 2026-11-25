import OAI.Hierarchy.TaggedWireTurnShelf
import OAI.Hierarchy.TaggedWireRoleProgram

namespace OAI
/-! # Fixed physical role-and-lane placement on the two-word barrel input -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open WireTelescope ThreeFlat Routing Tagged
open scoped Classical
variable {h W k attempts p e : ℕ} (S : PurchaseSampler) (s : Site h (2^W) k)

abbrev Fiber := Incident.Fiber (site S (attempts:=attempts)) s

/-- The last tag bit separates the preceding history from the original
reported data. Both kinds occupy a single common power-of-two aperture. -/
def slabIndex (room : ∀a:Fiber (attempts:=attempts) S s,∀t,labelled S t a.val<2^p) :
    (Bool×Fiber (attempts:=attempts) S s) ↪ Row p where
  toFun q:=⟨labelled S q.1 q.2.val,room q.2 q.1⟩
  inj' := by
    rintro ⟨t,a⟩ ⟨u,b⟩ eq
    obtain ⟨l,r⟩:=(labelled_unique S a b t u).mp (congrArg Fin.val eq)
    cases l;cases r;rfl

/-- Each barrel wire is copied from its one physical role, on this site
only. Unallocated public role identifiers are tied to zero. -/
def slabPins (room : ∀a:Fiber (attempts:=attempts) S s,∀t,labelled S t a.val<2^p) :
    TurnShelf.Aperture p e → ((Bool×Fiber (attempts:=attempts) S s) × Row e) ⊕ Bool :=
  fun q=>Function.extend (slabIndex S s room) (fun a=>Sum.inl (a,q.2)) (fun _=>.inr false) q.1

theorem slabPins_at
    (room : ∀a:Fiber (attempts:=attempts) S s,∀t,labelled S t a.val<2^p)
    (q : TurnShelf.Aperture p e) (a : Fiber (attempts:=attempts) S s) (t : Bool)
    (role : q.1.val=labelled S t a.val) :
    slabPins S s room q=.inl ((t,a),q.2) := by
  have z:q.1=slabIndex S s room (t,a):=Fin.ext role
  unfold slabPins
  rw [z,(slabIndex S s room).injective.extend_apply]

/-- The same immutable index is used for arbitrary admissible selectors,
every signed telescope term, and all payload assignments. -/
theorem slabBits_at
    (room : ∀a:Fiber (attempts:=attempts) S s,∀t,labelled S t a.val<2^p)
    (x : (Bool×Fiber (attempts:=attempts) S s) × Row e→Bool)
    (q : TurnShelf.Aperture p e) (a : Fiber (attempts:=attempts) S s) (t : Bool)
    (role : q.1.val=labelled S t a.val) :
    (Sum.elim x id ∘ slabPins S s room) q=x ((t,a),q.2) := by
  rw [Function.comp_apply,slabPins_at S s room q a t role];rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
