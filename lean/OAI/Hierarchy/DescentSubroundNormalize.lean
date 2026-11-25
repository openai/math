import OAI.Hierarchy.DescentNormalize
import OAI.Hierarchy.DescentScannedHost
import OAI.Hierarchy.DescentSelectedHubs

namespace OAI
/-! # The genuine normalization and uniform core unit at a chosen physical subround -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentHostDirectory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F I C V P : Type} [Field F] [Fintype I] [DecidableEq V] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (pick : I×Fin 2 ↪ W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "S" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key V) (hub : V→Bool) (k g q : ℕ)
local notation "C₀" => coalesced (W.selected G pick z hz fit pack p) key hub k g
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (w : ∀i,q∣z i)

def repetitions (e : (C₀).graph.Edge) := (C₀).graph.width e/q

include old picked w in
theorem repetition_width :
    ∀e : (C₀).graph.Edge, e∈(C₀).core → (C₀).graph.width e=repetitions W G pick z hz fit pack p key hub k g q e*q := by
  intro e kept
  apply Eq.symm
  exact Nat.div_mul_cancel (((S).coalesced_dvd key hub k g q
    (W.selected_dvd G pick z hz fit pack q old picked w p)) e kept)

local notation "counts" => repetitions W G pick z hz fit pack p key hub k g q
local notation "cut" => repetition_width W G pick z hz fit pack p key hub k g q old picked w

def subroundNormalize : Normalize S := .merge S V key hub k g (.split C₀ q counts cut (.done _))

theorem normalized_state :
    (subroundNormalize W G pick z hz fit pack p key hub k g q old picked w).result=(C₀).pieces q counts cut :=
  rfl

theorem normalized_unit (e : ((C₀).pieces q counts cut).graph.Edge) (marked : e∈((C₀).pieces q counts cut).core) :
    ((C₀).pieces q counts cut).graph.width e=q :=
  DescentCableUnbundling.uniform (C₀).graph (C₀).core counts q e marked

theorem normalized_adjacent {H : Type} (coords : (C₀).graph.Site→H) (relation : H→H→Prop)
    (actual : ∀e : (C₀).graph.Edge,relation (coords ((C₀).graph.src e)) (coords ((C₀).graph.dst e)))
    (e : ((C₀).pieces q counts cut).graph.Edge) :
    relation (coords (((C₀).pieces q counts cut).graph.src e)) (coords (((C₀).pieces q counts cut).graph.dst e)) :=
  actual (DescentCableUnbundling.original (C₀).graph (C₀).core counts e)

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
