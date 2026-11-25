import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth
import OAI.ThreeFlat.Diagonal.PhysicalReadHistory

namespace OAI
/-! # Accumulated charge arrays on a selected physical history -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

/-- Child weights are accumulated at the actual owner in the selected graph rewrite. -/
def Move.parent {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (s : A.Site) : (R.next t).Site :=
  cast (congrArg HistoryContraction.Shape.Site (R.target_eq t)) (R.rules.owner t s)

def Move.push {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (new : (R.next t).Site → ℕ) (old : A.Site → ℕ) (v : (R.next t).Site) :=
  new v + ∑ i : {a // R.parent t a=v}, old i.val

theorem Move.push_sum {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (new : (R.next t).Site → ℕ) (old : A.Site → ℕ) :
    (∑ v,R.push t new old v)=(∑ v,new v)+∑ i,old i := by
  simp only [Move.push,Finset.sum_add_distrib]
  exact congrArg ((∑ v, new v)+·) (Fintype.sum_fiberwise (R.parent t) old)

namespace Run
def Charges : {d l : ℕ} → {A : State d l} → Run F A → Type
  | _,_,_,.done _ => Unit
  | _,_,_,.step R next => (∀ t,(R.next t).Site → ℕ) × (∀ t,(next t).Charges)

/-- Sum of the terminal [work,pairs] column produced by the chronological additive scan. -/
def rootTotal : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.plan.History → r.Charges → (A.Site → ℕ) → ℕ
  | _,_,_,.done _,_,_,start => ∑ v,start v
  | _,_,_,.step R next,h,C,start =>
    (next h.1).rootTotal (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start)

/-- A single work tariff applies to every real compacting operation. -/
def scaled (tariff : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.Charges → r.Charges
  | _,_,_,.done _,_ => ()
  | _,_,_,.step _ next,C => (fun t v=>tariff*C.1 t v,fun t=>(next t).scaled tariff (C.2 t))

theorem push_scaled {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (new : (R.next t).Site→ℕ) (old : A.Site→ℕ) (tariff : ℕ) :
    R.push t (fun v=>tariff*new v) (fun v=>tariff*old v) = fun v=>tariff*R.push t new old v := by
  funext v
  simp only [Move.push,Nat.mul_add,Finset.mul_sum]

theorem rootTotal_scaled {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site→ℕ) (tariff : ℕ) :
    r.rootTotal h (r.scaled tariff C) (fun v=>tariff*start v)=tariff*r.rootTotal h C start := by
  induction r with
  | done A => simp only [rootTotal,Finset.mul_sum]
  | step R next ih =>
    simp only [scaled,rootTotal,push_scaled,ih]

open HistoryContraction

def LocalFloor : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.Charges → Prop
  | _, _, _, .done _, _ => True
  | _, _, _, .step R next, C => ∀ t,
      (∀ v, 1+(R.next t).incidentWidth v ≤ C.1 t v) ∧ (next t).LocalFloor (C.2 t)

/-- Per-site output of the same chronological scan used by rootTotal. -/
def rootArray : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    r.Charges → (A.Site → ℕ) → r.readTerminal (fun X => X.Site) h → ℕ
  | _, _, _, .done _, _, _, start => start
  | _, _, _, .step R next, h, C, start =>
    (next h.1).rootArray (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start)

@[instance_reducible]
private def rootFinite : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    Fintype (r.readTerminal (fun X => X.Site) h)
  | _, _, A, .done _, _ => A.finiteSite
  | _, _, _, .step R next, h => (next h.1).rootFinite (tailHistory R next h)

private theorem rootArray_sum {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site → ℕ) :
    letI := r.rootFinite h
    (∑ v, r.rootArray h C start v) = r.rootTotal h C start := by
  induction r with
  | done A => rfl
  | step R next ih => exact ih h.1 (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start)

def finalSite {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    r.readTerminal (fun X => X.Site) h ≃ (r.plan.finish h).Site :=
  Equiv.cast ((Run.terminal_relation (fun X => X.Site) (fun X => X.shape)
    (fun s t => s=t.Site) (fun _ => rfl) r h).trans (congrArg Shape.Site (r.terminal_shape h)))

/-- The terminal-site charge indexed by the actual tensor plan's final sites. -/
def chargeAt {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (start : A.Site → ℕ) (v : (r.plan.finish h).Site) :=
  r.rootArray h C start ((r.finalSite h).symm v)

theorem chargeAt_sum {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (start : A.Site → ℕ) : (∑ v, r.chargeAt h C start v) = r.rootTotal h C start := by
  let := r.rootFinite h
  exact ((r.finalSite h).symm.sum_comp (r.rootArray h C start)).trans (r.rootArray_sum h C start)

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
