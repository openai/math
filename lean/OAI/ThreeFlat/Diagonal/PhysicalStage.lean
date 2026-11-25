import OAI.ThreeFlat.Diagonal.CompressorShapeCharts
import OAI.ThreeFlat.Diagonal.HistogramRegister

namespace OAI
/-! # Chronological states and composition of regular, binary-lane compression stages -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped BigOperators Classical
noncomputable section

/-- Physical base and lane coordinates, their displayed site chart, and the numbered wire array.
The edge identifiers are always `(base,outgoing port,remaining lane)` at stage boundaries. -/
structure State (degree lanes : ℕ) where
  Base : Type
  [finiteBase : Fintype Base]
  [nonemptyBase : Nonempty Base]
  order : Base ≃ Fin (Fintype.card Base)
  Site : Type
  [finiteSite : Fintype Site]
  chart : Base × BitWord lanes ≃ Site
  graph : LiftedSlots Base degree (BitWord lanes)
  width : (Base × Fin degree) × BitWord lanes → ℕ

attribute [instance] State.finiteBase State.nonemptyBase State.finiteSite

variable {d l D L : ℕ} {F : Type} [Field F]

/-- Order the new base by old base ordinal followed by its consumed tag or port digit. -/
def productOrder {B C : Type} [Fintype B] [Fintype C] {q : ℕ} (x : B ≃ Fin (Fintype.card B))
    (y : C ≃ Fin q) : B×C ≃ Fin (Fintype.card (B×C)) :=
  ((x.prodCongr y).trans finProdFinEquiv).trans (finCongr (by
    rw [Fintype.card_prod, Fintype.card_congr y,Fintype.card_fin]))

abbrev State.shape (A : State d l) := StageAddress.shape A.graph A.chart A.width
abbrev State.positions (A : State d l) := Fintype.card A.Site

def State.energy (A : State d l) : ℝ := ∑ e, (A.width e : ℝ)^2/(1/((A.positions : ℝ)*d))

/-- The field-valued tensor rewrite and its actual successor graph are produced together. -/
structure Move (F : Type) [Field F] (A : State d l) (D L : ℕ) where
  rules : Rewrite A.shape F
  next : Fin rules.count → State D L
  target_eq : ∀ i, rules.target i = (next i).shape

/-- A finite list of deterministic physical passes may depend on all previously chosen terms.
These choices are exactly the choices of the resulting tensor-contraction plan. -/
inductive Run (F : Type) [Field F] : {d l : ℕ} → State d l → Type 1
  | done {d l : ℕ} (A : State d l) : Run F A
  | step {d l D L : ℕ} {A : State d l} (R : Move F A D L) (next : ∀ t, Run F (R.next t)) : Run F A

namespace Run

variable {A : State d l}

def plan : {d l : ℕ} → {A : State d l} → Run F A → Plan F A.shape
  | _, _, _, .done A => .done A.shape
  | _, _, _, .step R next => .step R.rules (fun t => (R.target_eq t).symm ▸ (next t).plan)

def Records : {d l : ℕ} → {A : State d l} → Run F A → Type
  | _, _, _, .done _ => Unit
  | _, _, _, .step R next => Record R.rules.count × (∀ t, (next t).Records)

def castCodes {X Y : Shape} (e : X=Y) (P : Plan F X) (E : P.Codes) : (e ▸ P : Plan F Y).Codes :=
  by subst Y; exact E

def codes : {d l : ℕ} → {A : State d l} → (R : Run F A) → R.Records → R.plan.Codes
  | _, _, _, .done _, _ => ()
  | _, _, _, .step R next, e => (e.1,fun t => castCodes (R.target_eq t).symm (next t).plan ((next t).codes (e.2 t)))

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
