import OAI.Hierarchy.GridLensSites
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Source addresses of the labelled data pins in one grid selector -/

namespace Hierarchy.GridThrough
open scoped Classical
noncomputable section

abbrev Cell (k n : ℕ) := Fin k → Fin (n+1)
abbrev Touch {E : Type} {n : ℕ} (touch : E → Option (Fin (n+1))) :=
  {z : E × Fin (n+1) // touch z.1 = some z.2}

/-- Decode the designated pins of a controller. The injective assignment
can include the tick-copy index in the pin using `finProdFinEquiv`.
Every pin outside its image reads the supplied literal. -/
def pinSource {A U : Type} (dest : U ↪ A) (literal : A → Bool) (a : A) : U ⊕ Bool :=
  if h : ∃ u, dest u = a then .inl h.choose else .inr (literal a)

theorem pinSource_inl {A U : Type} (dest : U ↪ A) (literal : A → Bool) (a : A) (u : U) :
    pinSource dest literal a = .inl u ↔ dest u = a := by
  unfold pinSource
  split
  · rename_i h
    simp only [Sum.inl.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · exact fun eq => dest.injective (h.choose_spec.trans eq.symm)
  · rename_i h
    have absent : dest u ≠ a := fun eq => h ⟨u,eq⟩
    simp [absent]

theorem pinSource_unused {A U : Type} (dest : U ↪ A) (literal : A → Bool) (a : A)
    (unused : ∀ u, dest u ≠ a) : pinSource dest literal a = .inr (literal a) := by
  simp [pinSource, not_exists.mpr unused]

theorem pinSource_once {A U : Type} (dest : U ↪ A) (literal : A → Bool) (u : U) :
    ∃! a, pinSource dest literal a = .inl u := by
  exact ⟨dest u, (pinSource_inl ..).2 rfl, fun _ h => ((pinSource_inl ..).1 h).symm⟩

/-- A simulation schedule specifies a tick for each rail. Its two assigned
pins are local to that same tick. The injection records disjointness of all
pins within each receiving tick. -/
structure PinAssignment (E : Type) (k n q d : ℕ) where
  direction : E → Fin k
  tick : E → Cell k n × Fin q
  slot : E × Bool → Fin d
  fresh : Function.Injective (fun u : E × Bool => (tick u.1,slot u))
  literal : Cell k n × Fin (q*d) → Bool

namespace PinAssignment
variable {E : Type} {k n q d : ℕ} (A : PinAssignment E k n q d)

def row (e : E) : Cell k n := (A.tick e).1
def touch (e : E) : Option (Fin (n+1)) := some (A.row e (A.direction e))

/-- The cell ordinal and the replica-local pin are written by the controller;
the two ends of a rail can never land in different replicas. -/
def dest : (Touch A.touch × Bool) ↪ (Cell k n × Fin (q*d)) where
  toFun u := (A.row u.1.val.1,
    finProdFinEquiv ((A.tick u.1.val.1).2,A.slot (u.1.val.1,u.2)))
  inj' := by
    rintro ⟨⟨⟨e,t⟩,ht⟩,s⟩ ⟨⟨⟨e',t'⟩,ht'⟩,s'⟩ eq
    have cells : (A.tick e).1 = (A.tick e').1 := congrArg (fun x : Cell k n × Fin (q*d) => x.1) eq
    have pins : ((A.tick e).2,A.slot (e,s)) = ((A.tick e').2,A.slot (e',s')) :=
      finProdFinEquiv.injective (congrArg Prod.snd eq)
    have es : (e,s) = (e',s') := A.fresh (Prod.ext
      (Prod.ext cells (congrArg (fun x : Fin q × Fin d => x.1) pins))
      (congrArg (fun x : Fin q × Fin d => x.2) pins))
    obtain rfl : e = e' := congrArg Prod.fst es
    obtain rfl : s = s' := congrArg Prod.snd es
    have ts : t = t' := Option.some.inj (ht.symm.trans ht')
    cases ts
    rfl

def data (c : Cell k n) (i : Fin (q*d)) := pinSource A.dest A.literal (c,i)

/-- At a designated replica-local pin the selector supplies the requested
side of exactly the rail assigned to that tick. -/
theorem data_at (e : E) (s : Bool) :
    A.data (A.row e) (finProdFinEquiv ((A.tick e).2,A.slot (e,s))) =
      .inl (⟨(e,A.row e (A.direction e)),rfl⟩,s) := (pinSource_inl ..).2 rfl

theorem data_cell (c : Cell k n) (i : Fin (q*d)) (u : Touch A.touch × Bool)
    (h : A.data c i = .inl u) :
    GridLens.cellOnRail (A.direction u.1.val.1) (A.row u.1.val.1) u.1.val.2 = c := by
  have placed := (pinSource_inl ..).1 h
  have same : A.row u.1.val.1 = c := congrArg Prod.fst placed
  have axis : A.row u.1.val.1 (A.direction u.1.val.1) = u.1.val.2 := Option.some.inj u.1.property
  rw [← axis,GridLens.cellOnRail_self,same]

theorem data_once (u : Touch A.touch × Bool) :
    ∃! ci : Cell k n × Fin (q*d), A.data ci.1 ci.2 = .inl u := pinSource_once A.dest A.literal u

end PinAssignment
end
end Hierarchy.GridThrough

end OAI
