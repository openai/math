import OAI.LinearAlgebra.SpectralBooks.VNPCube.CubeNetworks
import OAI.LinearAlgebra.SpectralBooks.ProfileShortening

/-! # Integral equations for the two fixed network gadgets

There is one variable for each local table position, even when positions have coinciding
values. The coordinate polynomial of a network is the sum over shared wire labels of the
product of these variables. Its difference from the prescribed integral tensor coordinate
is the equation imposed at an output word.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace VNP
open Crossing VNPCube MvPolynomial
open scoped Classical

noncomputable section

/-- The table shape of an ordinary sum of wire networks. -/
structure NetworkShape (I A : Type) where
  count : A → ℕ
  wires : (a : A) → Fin (count a) → Wire I

namespace NetworkShape

variable {I A : Type} [Fintype I] [Fintype A] (S : NetworkShape I A) (B : I → Type)

/-- The index of a local scalar, including the network, site, free input, and local wire bits. -/
abbrev Position := (a : A) × (i : I) ×
  (B i × ((j : Fin (S.count a)) → (S.wires a j).Leg i))

def evalTables {F : Type*} [CommSemiring F] (v : S.Position B → F) (x : ∀ i, B i) : F :=
  ∑ a, network (S.wires a) (fun i t y ↦ v ⟨a,i,t,y⟩) x

def equation (target : (∀ i, B i) → ℤ) (x : ∀ i, B i) : MvPolynomial (S.Position B) ℤ :=
  S.evalTables B X x - C (target x)

theorem aeval_equation {F : Type*} [CommRing F] (t : (∀ i, B i) → ℤ) (x : ∀ i, B i)
    (v : S.Position B → F) : aeval v (S.equation B t x) = S.evalTables B v x - (t x : F) := by
  simp [equation, evalTables, network]

def Realizes {F : Type*} [CommRing F] (target : (∀ i, B i) → ℤ) (v : S.Position B → F) : Prop :=
  ∀ x, S.evalTables B v x = (target x : F)

theorem realizes_of_preserves {k F : Type*} [Field k] [Field F] {v : S.Position B → k}
    {z : S.Position B → F} {target : (∀ i, B i) → ℤ} (h : S.Realizes B target v)
    (heq : ∀ g : MvPolynomial (S.Position B) ℤ, aeval v g = 0 → aeval z g = 0) :
    S.Realizes B target z := by
  intro x
  have h0 : aeval v (S.equation B target x) = 0 := by rw [aeval_equation, h, sub_self]
  simpa [S.aeval_equation, sub_eq_zero] using heq _ h0

end NetworkShape

/-- The wire lists, tags, and every cost estimate of one profiled shortener are held fixed
through the reduction. -/
structure ProfileShape (D : ℕ) where
  m : ℕ
  terms : ℕ
  bits : ℕ
  budget : ℝ
  saving : ℝ
  network : NetworkShape (AxisSite D) (Fin terms)
  code : Fin terms ↪ BitString bits
  width_pos : 0 < m
  terms_pos : 0 < terms
  saving_pos : 0 < saving
  saving_lt : saving < 1
  cost_le : ∀ a, ∑ i, wireCost (fun p q => dist (axisPoint p) (axisPoint q)) (network.wires a i) ≤ budget
  profile_cost : ∀ j (π : Fin terms → ℕ), ∑ a, π a = j →
    profileWireCost network.count network.wires π j bits ≤ (1-saving)*2*D*m*j

namespace ProfileShape
variable {D : ℕ} (P : ProfileShape D)

abbrev Position := P.network.Position (AxisLeg P.m)
instance : Fintype P.Position := by
  letI (i : AxisSite D) : Fintype (AxisLeg P.m i)  := by
    cases i <;> unfold AxisLeg <;> infer_instance
  dsimp [Position, NetworkShape.Position]
  infer_instance

def Realizes {k : Type*} [Field k] (v : P.Position → k) : Prop :=
  P.network.Realizes (AxisLeg P.m) (crossingTensor ℤ D P.m) v

theorem cast_crossingTensor (F : Type*) [Field F] {m : ℕ} (x : ∀ i : AxisSite D, AxisLeg m i) :
    ((crossingTensor ℤ D m x : ℤ) : F) = crossingTensor F D m x := by
  let minus : AxisStrings D m := fun i ↦ x (some (i,false))
  let plus : AxisStrings D m := fun i ↦ x (some (i,true))
  change ((crossingEntry ℤ (x none) minus plus : ℤ) : F) = crossingEntry F (x none) minus plus
  rw [crossingEntry_eq_indicator ℤ (x none) minus plus, crossingEntry_eq_indicator F (x none) minus plus]
  split <;> simp

/-- A specialization satisfying the equations supplies a crossing network over the new field,
with exactly the original local dimensions. -/
def crossingNetworkSum {k : Type*} [Field k] {v : P.Position → k} (h : P.Realizes v) :
    CrossingNetworkSum k D P.m P.terms P.budget where
  count := P.network.count
  wires := P.network.wires
  tables a i t y := v ⟨a,i,t,y⟩
  realizes x := (cast_crossingTensor k x).symm.trans (h x).symm
  cost_le := P.cost_le

theorem hasProfileShortening {k : Type*} [Field k] {v : P.Position → k} (h : P.Realizes v) :
    HasProfileShortening k D := by
  let S := P.crossingNetworkSum h
  exact ⟨P.m,P.terms,P.bits,P.budget,P.saving,S,P.code,P.width_pos,P.terms_pos,
    P.saving_pos,P.saving_lt,fun j π hp ↦ ⟨P.profile_cost j π hp, profileContraction_eq S P.code π⟩⟩

theorem exists_of_shortening (k : Type*) [Field k] (h : HasProfileShortening k D) :
    ∃ (P : ProfileShape D) (v : P.Position → k), P.Realizes v := by
  obtain ⟨m,A,b,budget,ν,S,code,hm,hA,hν,hν',hp⟩ := h
  let P : ProfileShape D := ⟨m,A,b,budget,ν,⟨S.count,S.wires⟩,code,hm,hA,hν,hν',
    S.cost_le,fun j π hπ ↦ (hp j π hπ).1⟩
  refine ⟨P,fun p ↦ S.tables p.1 p.2.1 p.2.2.1 p.2.2.2,fun x ↦ ?_⟩
  rw [cast_crossingTensor]
  exact (S.realizes x).symm

end ProfileShape

/-- A fixed width, selector format, and cube-edge wiring from the antipodal identity. -/
structure CubeShape (n : ℕ) (η : ℝ) (minWidth : ℕ) where
  width : ℕ
  copies : ℕ
  steps : ℕ
  edgeWidth : ℕ
  width_gt : minWidth < width
  copies_pos : 0 < copies
  steps_pos : 0 < steps
  tag_bound : (Nat.clog 2 (copies * Fintype.card (Edge (n+1)) ^ steps) : ℝ) ≤ η * width
  cost_bound : (steps : ℝ) * edgeWidth ≤ 2 * (2:ℝ)^n * Real.sqrt (n+1) * width

namespace CubeShape
variable {n minWidth : ℕ} {η : ℝ} (C : CubeShape n η minWidth)

abbrev Leg (n b : ℕ) (i : Vertex (n+1)) :=
  (j : Fin (Fintype.card (Vertex n))) → (oppositeWire ((Fintype.equivFin (Vertex n)).symm j) b).Leg i

def network : NetworkShape (Vertex (n+1)) (Fin C.copies × (Fin C.steps → Edge (n+1))) :=
  ⟨fun _ ↦ C.steps, fun w j ↦ edgeWire (w.2 j) C.edgeWidth⟩

abbrev Position := C.network.Position (Leg n C.width)

instance : Fintype C.Position := by
  dsimp [Position, NetworkShape.Position, Leg]
  infer_instance

def target (n b : ℕ) (x : (i : Vertex (n+1)) → Leg n b i) : ℤ :=
  ∏ j, basisTensor (fun z i ↦ (oppositeWire ((Fintype.equivFin (Vertex n)).symm j) b).basisTerm z i)
    (fun i ↦ x i j)

theorem cast_target (F : Type*) [Field F] {b : ℕ} (x : (i : Vertex (n+1)) → Leg n b i) :
    ((target n b x : ℤ) : F) = (oppositeRaw F n b).coeff x := by
  simp only [target, Int.cast_prod, oppositeRaw, SiteTensor.Raw.finProduct, Wire.raw,
    basisTensor, Int.cast_sum, apply_ite (Int.cast : ℤ → F), Int.cast_one, Int.cast_zero]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp_all

def Realizes {k : Type*} [Field k] (v : C.Position → k) : Prop :=
  C.network.Realizes (Leg n C.width) (target n C.width) v

theorem admitsAntipodalNetworks {k : Type*} [Field k] {v : C.Position → k} (h : C.Realizes v) :
    AdmitsAntipodalNetworks k n η minWidth := by
  refine ⟨C.width,C.copies,C.steps,C.edgeWidth,C.width_gt,C.copies_pos,C.steps_pos,
    C.tag_bound,C.cost_bound,fun c w i t y ↦ v ⟨(c,w),i,t,y⟩,fun x ↦ ?_⟩
  exact (cast_target k x).symm.trans ((h x).symm.trans (Fintype.sum_prod_type _))

theorem exists_of_networks (k : Type*) [Field k] (h : AdmitsAntipodalNetworks k n η minWidth) :
    ∃ (C : CubeShape n η minWidth) (v : C.Position → k), C.Realizes v := by
  obtain ⟨b,K,h,s,hb,hK,hh,hwidth,hcost,T,hT⟩ := h
  let C : CubeShape n η minWidth := ⟨b,K,h,s,hb,hK,hh,hwidth,hcost⟩
  refine ⟨C,fun p ↦ T p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2,fun x ↦ ?_⟩
  exact (Fintype.sum_prod_type _).trans ((hT x).symm.trans (cast_target k x).symm)

end CubeShape
end
end VNP

end SpectralBooks
end LinearAlgebra
end OAI
