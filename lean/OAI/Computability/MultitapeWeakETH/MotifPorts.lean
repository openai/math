import OAI.Computability.MultitapeWeakETH.MotifTable
import OAI.Computability.NearSquareRoot.CRTControlledWord

/-! # Synchronized selector sequences on the incident supply wires -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP MotifSelector StackInterpreter
open scoped Classical
noncomputable section

private theorem same_masks {A : Type} [DecidableEq A] (xs ys : List A)
    (eqs : ∀ t, xs.map (fun x => decide (x=t)) = ys.map (fun y => decide (y=t))) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => have := eqs y; simp at this
  | cons x xs ih =>
    cases ys with
    | nil => have := eqs x; simp at this
    | cons y ys =>
      have head := (List.cons.inj (eqs x)).1
      have same : y=x := by simpa using head.symm
      exact congrArg₂ List.cons same.symm (ih ys (fun t => (List.cons.inj (eqs t)).2))

/-- Equality of strings over an arbitrary fixed finite alphabet. -/
theorem listEq_poly (A : Type) [Codec A] [FiniteState A] [DecidableEq A] :
    Poly (fun q : List A × List A => decide (q.1=q.2)) := by
  let := Fintype.ofFinite A
  let mask (t : A) (xs : List A) := xs.map fun x => decide (x=t)
  have mp (t : A) : Poly (mask t) := Poly.maps _ (Easy.finite _).poly
  have col (t : A) := ((Easy.fst.poly.compose (mp t)).pair (Easy.snd.poly.compose (mp t))).compose NearSquareRoot.Benes.easyWordEq.poly
  convert all_poly (fun t (p : List A × List A) => decide (mask t p.1 = mask t p.2)) col using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun e t => congrArg (mask t) e,same_masks p.1 p.2⟩

variable {J E : Type} [DecidableEq J] [Fintype E] (G : Supply J E) (j : J)

/-- Local endpoint coordinates keep the two directions of a loop distinct. -/
abbrev Port := {e // j=G.src e} ⊕ {e // j=G.dst e}

def edge : Port G j → E := Sum.elim Subtype.val Subtype.val

def endpoint {I : E → Type} (x : Half G I j) : ∀ p : Port G j, I (edge G j p)
  | .inl e => x.1 e.val e.prop
  | .inr e => x.2 e.val e.prop

def anchorPort : Port G j :=
  if h : j=G.src (G.anchor j) then .inl ⟨_,h⟩ else
    .inr ⟨_,((G.anchor_incident j).resolve_left fun e => h e.symm).symm⟩

omit [Fintype E] in
theorem endpoint_anchor {A : Type} (x : Half G (fun _ => A) j) :
    endpoint G j x (anchorPort G j) = MotifEntry.anchor G j x := by
  unfold MotifEntry.anchor anchorPort
  split <;> rfl

/-- The encoded arrays agree exactly when every incident endpoint agrees with the
specified anchor on every copy, as required by the mathematical entry reader. -/
theorem consistent_iff {u a : ℕ} (t : Half G (fun _ => Fin u → Word a) j) :
    MotifEntry.consistent G j t = true ↔
    ∀ p : Port G j, (List.ofFn fun i => Label.mk (endpoint G j t p i)) =
      (List.ofFn fun i => Label.mk (endpoint G j t (anchorPort G j) i)) := by
  rw [endpoint_anchor]
  simp only [MotifEntry.consistent,decide_eq_true_eq,List.ofFn_inj]
  constructor
  · intro ok p
    apply funext; intro i
    apply Label.ext
    cases p with
    | inl e => exact (dite_eq_left e.prop ▸ (ok e.val).1) i
    | inr e => exact (dite_eq_left e.prop ▸ (ok e.val).2) i
  · intro same e
    constructor
    · split <;> rename_i h
      · exact fun i => congrArg Label.val (congrFun (same (.inl ⟨e,h⟩)) i)
      · trivial
    · split <;> rename_i h
      · exact fun i => congrArg Label.val (congrFun (same (.inr ⟨e,h⟩)) i)
      · trivial

end
end OAI.Computability.MultitapeWeakETH.MotifFields
