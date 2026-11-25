import OAI.Hierarchy.DescentRecordedCore
import OAI.Hierarchy.DescentBlockGroup
import OAI.Hierarchy.DescentSeedHistogram

namespace OAI
/-! # Coefficient conservation through dependent physical stage histories -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

structure Histories (F : Type*) (D : ℕ) (P : Type*) (bits : P→ℕ) where
  Choice : Type*
  finite : Fintype Choice
  state : Choice → MarkedWorld F D P bits
  weight : Choice → F

attribute [instance] Histories.finite

namespace Histories
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P→ℕ}

def value (H : Histories F D P bits) (x : Ports bits) := ∑ c,H.weight c*(H.state c).value x

def singleton (A : MarkedWorld F D P bits) : Histories F D P bits :=
  ⟨Unit,inferInstance,fun _=>A,fun _=>1⟩

@[simp] theorem singleton_value (A : MarkedWorld F D P bits) (x : Ports bits) :
    (singleton A).value x=A.value x := by
  change (∑ _ : Unit, (1 : F) * A.value x) = A.value x
  rw [Fintype.sum_unique, one_mul]

variable (H : Histories F D P bits) (G : PoweredGadget F)
variable (I : H.Choice→Type) [∀p,Fintype (I p)] (C : H.Choice→Type)
variable (pick : ∀p,I p×Fin 2 ↪ (H.state p).graph.Edge) (z : ∀p,I p→ℕ)
variable (hz : ∀p i,0<z p i)
variable (fit : ∀p i s,(H.state p).graph.width (pick p (i,s))=z p i*G.b)
variable (pack : ∀p,(H.state p).graph.Site→C p)

/-- Only realizable profile assignments are stored. Later choices may refer
to the particular immutable input history and its actual bundle list. -/
def step : Histories F D P bits where
  Choice := Σ p : H.Choice,I p→Profile G.C
  finite := inferInstance
  state h := (H.state h.1).selected G (pick h.1) (z h.1) (hz h.1) (fit h.1) (pack h.1) h.2
  weight h := H.weight h.1

theorem step_value (x : Ports bits) : (step H G I C pick z hz fit pack).value x=H.value x := by
  change (∑h : Σp : H.Choice,I p→Profile G.C, _)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  change ∑ p,H.weight c*((H.state c).selected G (pick c) (z c) (hz c) (fit c) (pack c) p).value x=_
  rw [←Finset.mul_sum,MarkedWorld.selected_sum]

/-- Put independently selected old summands from different blocks in a
single true graph before pairing their occurrences at common positions. -/
def collect {J : Type} [Fintype J] {port : J→Type*} {w : ∀j,port j→ℕ}
    (H : ∀j,Histories F D (port j) (w j)) : Histories F D (Σj,port j) (fun p=>w p.1 p.2) :=
  ⟨(∀j,(H j).Choice),inferInstance,fun c=>
    let A := fun j=>(H j).state (c j)
    ⟨blockGroup (fun j=>(A j).toWorld),blockCore (fun j=>(A j).toWorld) (fun j=>(A j).core)⟩,fun c=>∏j,(H j).weight (c j)⟩

theorem collect_value {J : Type} [Fintype J] {port : J→Type*} {w : ∀j,port j→ℕ}
    (H : ∀j,Histories F D (port j) (w j)) (x : Ports (fun p : Σj,port j=>w p.1 p.2)) :
    (collect H).value x=∏j,(H j).value (fun p=>x ⟨j,p⟩) := by
  unfold value
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.prod_mul_distrib]
  exact congrArg ((∏j,(H j).weight (c j))*·) (block_value (fun j=>((H j).state (c j)).toWorld) x)

def subdivide (q : ℕ) (mult : ∀p,(H.state p).graph.Edge→ℕ)
    (div : ∀p e,e∈(H.state p).core → (H.state p).graph.width e=mult p e*q) : Histories F D P bits :=
  ⟨H.Choice,H.finite,fun h=>(H.state h).pieces q (mult h) (div h),H.weight⟩

theorem subdivide_value (q : ℕ) (mult : ∀p,(H.state p).graph.Edge→ℕ)
    (div : ∀p e,e∈(H.state p).core → (H.state p).graph.width e=mult p e*q) (x : Ports bits) :
    (subdivide H q mult div).value x=H.value x :=
  Finset.sum_congr rfl fun p _=> congrArg (H.weight p*·) ((H.state p).pieces_value q (mult p) (div p) x)

/-- True field-weighted initial histories, before any profile or rotor has
been chosen. The actual local graph inside each summand is Boolean. -/
def seed [Fintype P] (A : MarkedWorld F D P bits) (s : ℕ) : Histories F D P (fun p=>s*bits p) :=
  ⟨(∀v, DescentInitialHost.Count A.graph s v),inferInstance,
   fun h=>⟨⟨DescentInitialHost.stacked A.graph s, DescentInitialHost.seedLocal A.graph s h⟩,A.core⟩,
   fun h=>∏v,DescentInitialHost.censusWeight A.graph A.tables s v (h v)⟩

theorem seed_value [Fintype P] (A : MarkedWorld F D P bits) (s : ℕ) (x : Ports (fun p=>s*bits p)) :
    (seed A s).value x=∏i : Fin s,A.value (fun p=>DescentInitialHost.rowAt (x p) i) :=
  DescentInitialHost.seed_value A.graph A.tables s x

end Histories
end
end Hierarchy.DescentSixParty

end OAI
