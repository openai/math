import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Terminal pin count of the physical word assembly

Each move carries inherited external pins and introduces the incident half
words of its successor. The local charge floor pays for these half words.
-/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
variable {F Pins : Type} [Field F] {d l : ℕ} {A : State d l}

private theorem Run.width_rootArray (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (C : r.Charges) (floor : r.LocalFloor C) (L : A.Words Pins) (N : Forest F L.ports.form)
    (start : A.Site → ℕ) (initial : ∀ x, L.ports.form.width x ≤ 2*start x)
    (v : r.readTerminal (fun X => X.Site) h) (site : (r.plan.finish h).Site) (agree : HEq v site) :
    (r.plan.assemble h (r.wordAssembly J L) N).1.width site ≤ 2*r.rootArray h C start v := by
  induction r with
  | done A =>
    have same : v = site := eq_of_heq agree
    subst site
    exact initial v
  | step R next ih =>
    let t := h.1
    let rest := tailHistory R next h
    let s := J.1 L t
    let after := R.push t (C.1 t) start
    let target := (next t).finalSite rest v
    have align : HEq v target := (cast_heq _ v).symm
    apply Run.step_tree_price h J L N site target (agree.symm.trans align)
      (fun {p} (_ : Tree F p) => p) (fun ws => ws ≤ 2*(next t).rootArray rest (C.2 t) after v)
    dsimp only
    intro N' _
    exact ih t rest (J.2 t) (C.2 t) (floor t).2 s.words N' after
      (s.width_push start (C.1 t) initial (floor t).1) v target align

/-- The complete terminal port set is paid by the charge of the selected
site, including when no physical moves have been issued. -/
theorem Run.assembled_port_width (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (C : r.Charges) (floor : r.LocalFloor C) (L : A.Words Pins) (N : Forest F L.ports.form)
    (start : A.Site → ℕ) (initial : ∀ x, L.ports.form.width x ≤ 2*start x)
    (v : (r.plan.finish h).Site) :
    (r.plan.assemble h (r.wordAssembly J L) N).1.width v ≤ 2*r.chargeAt h C start v := by
  have align {X Y : Type} (e : X = Y) (y : Y) : HEq ((Equiv.cast e).symm y) y := by cases e; rfl
  exact r.width_rootArray h J C floor L N start initial ((r.finalSite h).symm v) v (align _ v)

/-- A terminal archive bound with a tariff of at least two provides the
pin count needed by the contraction evaluator's word allocation. -/
theorem Run.assembled_pins_fit (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (C : r.Charges) (floor : r.LocalFloor C) (L : A.Words Pins) (N : Forest F L.ports.form)
    (start : A.Site → ℕ) (initial : ∀ x, L.ports.form.width x ≤ 2*start x)
    (v : (r.plan.finish h).Site) {unit W : ℕ}
    (rate : 2 ≤ unit) (room : unit*r.chargeAt h C start v ≤ 2^W) :
    (r.plan.assemble h (r.wordAssembly J L) N).1.width v ≤ 2^W :=
  (r.assembled_port_width h J C floor L N start initial v).trans
    ((Nat.mul_le_mul_right (r.chargeAt h C start v) rate).trans room)


end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
