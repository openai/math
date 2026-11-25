import OAI.Hierarchy.DescentScheduleGrains
import OAI.Hierarchy.DescentEpochHistory

namespace OAI
/-! # One common calendar and one immutable rotor format in the actual epoch -/
namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat Expander NonlinearExpanders
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {H : Histories F d P bits}
variable {G : PoweredGadget F} {u ε : ℝ} {hu : 0≤u} {he : 0≤ε} {t h C Ht n : ℕ}

structure Epoch.Grains (z : ℕ→ℕ) (board : Graph n h) (bitsR : ℕ) (E : Epoch H G hu he t h C Ht) : Prop where
  ordinary : Schedule.Grains z E.subrounds
  grain : E.grain=z t*G.b
  unit : ∀c,(E.reset c).unit=E.grain
  dimension : ∀c,(E.reset c).n=n
  width : ∀c,(E.reset c).width=bitsR
  graph : ∀c,HEq (E.reset c).graph board
  cuts : ∀c,Normalize.CutsEqual (E.reset c).unit (E.reblock c)

theorem Epoch.Grains.menu {z : ℕ→ℕ} {board : Graph n h} {bitsR : ℕ} {E : Epoch H G hu he t h C Ht}
    (g : Epoch.Grains z board bitsR E) (menu : ∀π,Configures F board.arcs C bitsR π) (c) :
    ∀π,Configures F (E.reset c).graph.arcs C (E.reset c).width π := by
  have dim := g.dimension c
  have edge := g.graph c
  subst n
  rw [eq_of_heq edge,g.width c]
  exact menu
/-- One retained clock row for each actual epoch in the chosen dependent run. -/
def Epochs.Grains (board : Graph n h) (bitsR : ℕ) (period : ℕ→ℕ→ℕ) :
    {J : ℕ}→{H : Histories F d P bits}→(j : ℕ)→Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H→Prop
  | 0,_,_,_=>True
  | _+1,_,j,run=>Epoch.Grains (period j) board bitsR run.1 ∧ Grains board bitsR period (j+1) run.2

end Hierarchy.DescentSixParty

end OAI
