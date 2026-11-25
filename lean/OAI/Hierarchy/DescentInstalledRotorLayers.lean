import OAI.Hierarchy.DescentInstalledNames

namespace OAI
/-! # Layer count of the configured circuit at an installed good site -/

namespace Hierarchy.DescentChosenRouter
open DescentRotor DescentMixedRouter
open scoped Classical
noncomputable section

open private transportCircuit from OAI.Hierarchy.DescentInstalledNames

/-- Read the field using the finite enumeration carried by the input circuit. -/
private def circuitLayers {E K : Type} [Field K] {n h C₀ bits u : ℕ}
    {G : NonlinearExpanders.Graph n h} {hw : 0<bits} {pay : ℝ}
    {a : Fintype E} {src dst : E → Fin (2^n)}
    (chip : @BaseCircuit E a n h K _ G C₀ bits u hw src dst pay) : ℕ :=
  @BaseCircuit.layers E a n h K _ G C₀ bits u hw src dst pay chip

private theorem transportCircuit_layers {E K : Type} [Field K] {n h C₀ bits u : ℕ}
    {G : NonlinearExpanders.Graph n h} {hw : 0<bits} {pay : ℝ}
    {a b : Fintype E} {src dst : E → Fin (2^n)}
    (chip : @BaseCircuit E a n h K _ G C₀ bits u hw src dst pay) :
    circuitLayers (a:=b) (transportCircuit (a:=a) (b:=b) (G:=G) (hw:=hw) (pay:=pay) chip) =
      circuitLayers (a:=a) chip := by
  cases Subsingleton.elim a b
  rfl

variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)

/-- Number of layers on the actual chip returned by the good branch of `selected`. -/
def selectedRotorLayers (s : Bool) (g : P.Good) : ℕ :=
  match selected P G hw pay hardware s (.inl g) with
  | .good _ _ _ chip => circuitLayers chip
  | .exceptional _ => 0

theorem selectedRotorLayers_eq (s : Bool) (g : P.Good) :
    selectedRotorLayers P G hw pay hardware s g=(hardware s g).layers := by
  unfold selectedRotorLayers selected
  exact transportCircuit_layers (chip:=hardware s g)

end
end Hierarchy.DescentChosenRouter

end OAI
