import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # The terminal forest in the physical stage coordinates -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
open private forestUncast castAssembly from OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

/-- Execute the chosen contraction's actual tree assembly in the next physical
state's chart. The equality of target shapes changes only its index type. -/
def Move.WordStep.nextForest {R : Move F A D m} {L : A.Words Pins} {i : Fin R.rules.count}
    (x : R.WordStep Pins L i) (N : Forest F L.ports.form) : Forest F x.words.ports.form :=
  forestUncast (R.target_eq i).symm x.words.ports.form (x.stage.assemble N)

/-- Chronologically build the trees of the selected physical terminal cluster. -/
def Run.endForest : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (J : Run.WordSteps Pins r) → (L : A.Words Pins) → Forest F L.ports.form →
    Forest F (r.endWords h J L).ports.form
  | _,_,_,.done _,_,_,_,trees => trees
  | _,_,_,.step R next,h,J,L,trees =>
    let x:=J.1 L h.1
    (next h.1).endForest (Run.tailHistory R next h) (J.2 h.1) x.words (x.nextForest trees)

private theorem forest_assembled_cast {X Y : Shape} (e : X=Y) (P : Plan F X) (V : Form X Pins) (J : P.Assembly V)
    (h : (e ▸ P : Plan F Y).History) (N : Forest F (e ▸ V : Form Y Pins)) :
    HEq ((e ▸ P : Plan F Y).assemble h (castAssembly e P V J) N).2
      (P.assemble (Run.historyOfCast e P h) J (forestUncast e V N)).2 := by
  cases e
  rfl

/-- The physical step traversal returns exactly the trees of recursive Plan assembly. -/
theorem Run.endForest_assemble (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) :
    HEq (r.plan.assemble h (r.wordAssembly J L) N).2 (r.endForest h J L N) := by
  induction r with
  | done => rfl
  | step R next ih =>
    let x:=J.1 L h.1
    exact (forest_assembled_cast (R.target_eq h.1).symm (next h.1).plan x.words.ports.form
      ((next h.1).wordAssembly (J.2 h.1) x.words) h.2 (x.stage.assemble N)).trans
      (ih h.1 (Run.tailHistory R next h) (J.2 h.1) x.words (x.nextForest N))

omit [Field F] in
private theorem forest_at_cast_site {X Y : Shape} (e : X=Y) (V : Form X Pins) (U : Form Y Pins)
    (source : Forest F V) (target : Forest F U) (forms : HEq U V) (forests : HEq target source)
    (z : X.Site) : HEq (target ((congrArg Shape.Site e) ▸ z)) (source z) := by
  cases e
  have form_eq : U=V := eq_of_heq forms
  subst U
  have tree_eq : target=source := eq_of_heq forests
  subst target
  rfl

/-- Read a terminal physical tree by its literal S44 site, transported into the
site type of the resolved history. -/
theorem Run.endForest_site (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (z : (r.terminalLayer h).state.Site) :
    HEq ((r.plan.assemble h (r.wordAssembly J L) N).2 ((congrArg Shape.Site (r.terminalLayer_shape h)) ▸ z))
      (r.endForest h J L N z) :=
  forest_at_cast_site (r.terminalLayer_shape h) _ _ _ _ (r.endWords_form h J L N) (r.endForest_assemble h J L N) z

end ThreeFlat.Diagonal.PhysicalStage
end

end OAI
