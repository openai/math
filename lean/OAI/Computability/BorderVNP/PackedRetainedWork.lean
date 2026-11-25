import OAI.Computability.BorderVNP.PackedRetainedSewingFiber
import OAI.Computability.BorderVNP.PackedInheritedRowNames

/-! # Private choices through successive retained site programs

Each cut appends the old incidence array to the private work. Along an arbitrary
sequence of cuts the original choices keep their numerical addresses, and every
complete list of observed signs and entries has the same fiber at its birth site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep
open scoped Classical

/-- The successive installed interval programs on the route of an old site. -/
inductive Site.Retention : Site → Site → Type
  | refl (s : Site) : Site.Retention s s
  | layer {a s : Site} (prev : Site.Retention a s) {n : ℕ}
      (cuts : List Slice) (read : Fin s.incoming → Fin n) (cover : Covers s.incoming n cuts read) :
      Site.Retention a (s.retain n cuts)
  | forced {a s : Site} (prev : Site.Retention a s) {n : ℕ} (read : Fin s.incoming → Option (Fin n)) :
      Site.Retention a (SewnField.stage s n (SewnField.intervals read))

namespace Site.Retention

variable {a s t : Site}

/-- Join a history of prior cuts to the cuts of the next epoch. -/
def trans (p : a.Retention s) : {t : Site} → s.Retention t → a.Retention t
  | _, .refl _ => p
  | _, .layer q cuts read cover => .layer (p.trans q) cuts read cover
  | _, .forced q read => .forced (p.trans q) read

/-- Read the original incidence lanes from the actual terminal input. -/
def readInput : {s : Site} → a.Retention s → (Fin s.incoming → Bool) → (Fin a.incoming → Bool)
  | _, .refl _, x => x
  | _, .layer p _ read _, x => p.readInput (x ∘ read)
  | _, .forced p read, x => p.readInput (SewnField.oldInput _ read x)

/-- Write precisely the forced incidence suffix for each successive cut. -/
def complete : {s : Site} → a.Retention s → (Fin s.incoming → Bool) → (Fin a.work → Bool) → (Fin s.work → Bool)
  | _, .refl _, _, g => g
  | _, .layer p _ read _, x, g => Fin.append (p.complete (x ∘ read) g) (x ∘ read)
  | _, .forced p read, x, g =>
    let old := SewnField.oldInput _ read x
    Fin.append (p.complete old g) old

/-- The entire original work area is allocated at every later cut. -/
theorem work_le (p : a.Retention s) : a.work ≤ s.work := by
  induction p with
  | refl => rfl
  | layer p cuts read cover ih => exact ih.trans (Nat.le_add_right ..)
  | forced p read ih => exact ih.trans (Nat.le_add_right ..)

/-- Every original private bit, including each independent bottom wire choice,
is still stored at exactly its birth address. -/
theorem complete_prefix (p : a.Retention s) (x : Fin s.incoming → Bool)
    (g : Fin a.work → Bool) (j : Fin a.work) :
    p.complete x g (j.castLE p.work_le) = g j := by
  induction p with
  | refl => rfl
  | layer q cuts read cover ih =>
    exact (Fin.append_left (q.complete (x ∘ read) g) (x ∘ read) (j.castLE q.work_le)).trans (ih _)
  | forced q read ih =>
    let old := SewnField.oldInput _ read x
    exact (Fin.append_left (q.complete old g) old (j.castLE q.work_le)).trans (ih _)

/-- The inherited program remains local on its whole allocated bank. -/
theorem locality (p : a.Retention s) (loc : a.Local) : s.Local := by
  induction p with
  | refl => exact loc
  | layer p cuts read cover ih => exact Site.local_retain _ ih cuts read cover
  | forced p read ih => exact SewnField.stage_local _ ih _ read (SewnField.intervals_cover read)

/-- Complete observation fibers along a history of genuine physical interval tests. -/
noncomputable def fiberEquiv : {s : Site} → (p : a.Retention s) → (loc : a.Local) → (x : Fin s.incoming → Bool) →
    (obs : List (Bool × Option ℕ)) → a.Fiber (p.readInput x) obs ≃ s.Fiber x obs
  | _, .refl _, _, _, _ => Equiv.refl _
  | _, .layer q cuts read cover, loc, x, obs => (q.fiberEquiv loc (x ∘ read) obs).trans
      (retainFiberEquiv _ (q.locality loc) cuts read cover x obs)
  | _, .forced q read, loc, x, obs => (q.fiberEquiv loc (SewnField.oldInput _ read x) obs).trans
      (SewnField.stageFiberEquiv _ (q.locality loc) read x obs)

/-- The fiber equivalence acts on the actual physical tape by suffix installation. -/
theorem fiberEquiv_val (p : a.Retention s) (loc : a.Local) (x : Fin s.incoming → Bool)
    (obs : List (Bool × Option ℕ)) (g : a.Fiber (p.readInput x) obs) :
    (p.fiberEquiv loc x obs g).val = p.complete x g.val := by
  induction p with
  | refl => rfl
  | layer p cuts read cover ih =>
    exact congrArg (fun f => Fin.append f (x ∘ read)) (ih _ _)
  | forced p read ih =>
    exact congrArg (fun f => Fin.append f (SewnField.oldInput _ read x)) (ih _ _)

/-- An arbitrary accepted terminal tape contains the unique completion of its birth
private work, even when multiple birth assignments give the same observations. -/
theorem observe_iff (p : a.Retention s) (loc : a.Local) (x : Fin s.incoming → Bool)
    (obs : List (Bool × Option ℕ)) (raw : Fin s.work → Bool) :
    s.observe (bits raw x) = some obs ↔
      ∃ g : Fin a.work → Bool, a.observe (bits g (p.readInput x)) = some obs ∧ p.complete x g = raw := by
  constructor
  · intro h
    let u : s.Fiber x obs := ⟨raw,h⟩
    let v := (p.fiberEquiv loc x obs).symm u
    exact ⟨v.val,v.property,(p.fiberEquiv_val loc x obs v).symm.trans
      (congrArg Subtype.val ((p.fiberEquiv loc x obs).apply_symm_apply u))⟩
  · rintro ⟨g,h,rfl⟩
    let v : a.Fiber (p.readInput x) obs := ⟨g,h⟩
    exact (congrArg (fun z => s.observe (bits z x)) (p.fiberEquiv_val loc x obs v).symm).trans
      (p.fiberEquiv loc x obs v).property

end Site.Retention

variable {D m old next np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (binName : A → ℕ)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (v : p.layout.Site) (edgeID : p.layout.Edge ↪ Fin old)
    (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next) (portID : P ↪ Fin np)

local notation3 "cut" => Layer.orderedCuts p edgeID portID v e bin perm binName positive first q nextID

/-- Append the actual stable-order interval program of a selected physical sewing step. -/
noncomputable def orderedRetention {birth s : Site} (past : birth.Retention s)
    (size : s.incoming = incoming p.layout v) :
    birth.Retention (s.retain (incoming (output e p bin perm positive first q).layout (.inl v)) cut) :=
  .layer past cut (layerRead e p bin perm positive first q v edgeID nextID portID ∘ Fin.cast size)
    ((Layer.ordered_covers p edgeID portID v e bin perm binName positive first q nextID).castOld size)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
