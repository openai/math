import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Port counts for a chronological stage with one inherited child -/

namespace ThreeFlat.Diagonal.PhysicalStage.RefreshReadback

open HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F]

theorem transportedHalf {S T : Shape} (eqn : S=T) (W : PortLayout T Pins) (v : S.Site) :
    (eqn.symm ▸ W : PortLayout S Pins).halfBits v = W.halfBits (cast (congrArg Shape.Site eqn) v) := by
  cases eqn
  rfl

private theorem transportedWidth {S T : Shape} (eqn : S=T) (W : Form T Pins) (v : S.Site) :
    (eqn.symm ▸ W : Form S Pins).width v = W.width (cast (congrArg Shape.Site eqn) v) := by
  cases eqn
  rfl

section Measurements
variable {d l D t : ℕ} {A : State d l} (R : Move F A D t) (L : A.Words Pins)
    (b : Fin R.rules.count) (step : R.WordStep Pins L b) (site : (R.rules.target b).Site)

def delivered : PortLayout (R.rules.target b) Pins :=
  (R.target_eq b).symm ▸ step.words.ports

def singleMeasurements (u : A.Site) : Prop :=
  step.stage.count site=1 ∧
    (∀ k,(step.stage.child site k).val=u) ∧
    step.stage.hidden site=L.ports.halfBits u ∧
    step.stage.rootWidth site=L.ports.halfBits u+(delivered R L b step).halfBits site ∧
    (((R.target_eq b).symm ▸ step.words.ports.form : Form (R.rules.target b) Pins).width site) =
      L.ext u+(delivered R L b step).halfBits site

/-- Summing each port of either order counts the same incident bits. -/
theorem wordHalf_order {d l : ℕ} (X : State d l) (K L : X.Words Pins) (v : X.Site) :
    K.ports.halfBits v=L.ports.halfBits v := by
  let width := fun a : X.shape.graph.Port v => X.width a.val.1
  exact ((K.order v).sum_comp width).trans ((L.order v).sum_comp width).symm

theorem single_target (u : A.Site) (count : step.stage.count site=1)
    (child : ∀ k,(step.stage.child site k).val=u) :
    ((R.target_eq b).symm ▸ step.words.ports.form : Form (R.rules.target b) Pins).width site =
      L.ext u+(delivered R L b step).halfBits site := by
  let coord := Equiv.cast (congrArg Shape.Site (R.target_eq b))
  let total (v : (R.rules.target b).Site) := ∑ k : Fin (step.stage.count v),L.ext (step.stage.child v k).val
  have raw : step.words.ext (coord site) = total (coord.symm (coord site)) :=
    (step.originOrder (coord site)).choose
  have sumSite : total site=L.ext u := by
    unfold total
    calc
      (∑ k : Fin (step.stage.count site),L.ext (step.stage.child site k).val) =
          ∑ _ : Fin (step.stage.count site), L.ext u :=
        Finset.sum_congr rfl (fun k _ => congrArg L.ext (child k))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,count,one_nsmul]
  have ex := raw.trans ((congrArg total (coord.symm_apply_apply site)).trans sumSite)
  exact (transportedWidth (R.target_eq b) step.words.ports.form site).trans
    ((congrArg (fun n => n + step.words.ports.halfBits (coord site)) ex).trans
      (congrArg (fun n => L.ext u + n)
        (transportedHalf (R.target_eq b) step.words.ports site).symm))

def rootMeasurements : Prop :=
  step.stage.rootWidth site=(∑ i,L.ports.halfBits (step.stage.child site i).val)+(delivered R L b step).halfBits site

theorem single_root {u : A.Site} (h : singleMeasurements R L b step site u) :
    rootMeasurements R L b step site := by
  rcases h with ⟨count,child,_,root,_⟩
  unfold rootMeasurements
  simpa only [child,Finset.sum_const,Finset.card_univ,Fintype.card_fin,count,one_nsmul] using root

end Measurements
end
end ThreeFlat.Diagonal.PhysicalStage.RefreshReadback

end OAI
