import OAI.LinearAlgebra.FiniteFourier.Companion.CompanionProfileSaving
import OAI.Computability.BorderVNP.CrossingNormalization

/-! # Transport of the spectral crossing identity to the companion's placed networks -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Companion

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.Crossing
open scoped BigOperators Classical
variable {D m L A : ℕ} {F : Type*} [Field F]

private theorem same_univ {α : Type*} (i j : Fintype α) :
    @Finset.univ α i = @Finset.univ α j := by
  rw [Subsingleton.elim i j]

/-- Reflecting all sites through the origin places each signed endpoint at the
companion's corresponding terminal and preserves every cable length. -/
def placedNetwork (W : Fin L → Wire (AxisSite D)) (m : ℕ) :
    OAI.Computability.BorderVNP.Crossing.Network D (Fin D × Bool) (fun _ => m) where
  Site := AxisSite D
  Edge := Fin L
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := (W e).left
  dst e := (W e).right
  width e := (W e).width
  attach := some
  position v := -axisPoint v
  in_ball v := by
    simpa [Metric.mem_closedBall,dist_zero_right] using axisPoint_in_ball v

theorem placedNetwork_placed (W : Fin L → Wire (AxisSite D)) :
    (placedNetwork W m).PlacedAt OAI.Computability.BorderVNP.Crossing.antipodalPosition := by
  rintro ⟨i,b⟩
  cases b <;> simp [placedNetwork,axisPoint,OAI.Computability.BorderVNP.Crossing.antipodalPosition,
    EuclideanSpace.single,PiLp.single_neg]

theorem placedNetwork_cost (W : Fin L → Wire (AxisSite D)) :
    (placedNetwork W m).cost = ∑ e, wireCost (fun p q => dist (axisPoint p) (axisPoint q)) (W e) := by
  simp only [OAI.Computability.BorderVNP.Crossing.Network.cost,placedNetwork,wireCost,dist_neg_neg]
  exact Finset.sum_congr (same_univ _ _) fun _ _ => rfl

private def portInput (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    (v : AxisSite D) → AxisLeg m v
  | none => ()
  | some p => x p

private def localPort (v : AxisSite D) :
    ((p : {p : Fin D × Bool // some p = v}) → Fin m → Bool) → AxisLeg m v :=
  match v with
  | none => fun _ => ()
  | some p => fun x => x ⟨p,rfl⟩

/-- Each table reads the bundle of its attached port and the original
bit of each incident wire. The center's external leg is the unique unit. -/
def placedTable (W : Fin L → Wire (AxisSite D)) (T : LocalTables (B:=AxisLeg m) W F) :
    (placedNetwork W m).Tables F := fun v edges ports =>
  T v (localPort v ports) (fun e j => edges ⟨e,j.2.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr h.symm)⟩ j.val)

theorem placedNetwork_value (W : Fin L → Wire (AxisSite D)) (T : LocalTables (B:=AxisLeg m) W F)
    (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    (placedNetwork W m).value (placedTable W T) x = network W T (portInput x) := by
  unfold OAI.Computability.BorderVNP.Crossing.Network.value network
  dsimp only [placedNetwork] at *
  refine Finset.sum_congr (same_univ _ _) fun a _ => ?_
  refine Finset.prod_congr (same_univ _ _) fun v _ => ?_
  cases v <;> rfl

private theorem antipodal_eq (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    OAI.Computability.BorderVNP.Crossing.antipodalTensor F D m x = crossingTensor F D m (portInput x) := by
  change (if ∀ i, x (i,false) = x (i,true) then 1 else 0) =
    crossingEntry F () (fun i => x (i,false)) (fun i => x (i,true))
  rw [crossingEntry_eq_indicator]
  simp only [funext_iff]

/-- Conversion of the original one-copy spectral identity. The selector,
number of summands, wire costs and individual table entries are preserved. -/
def paidIdentity {cap : ℝ} (S : CrossingNetworkSum F D m A cap)
    (strict : cap+2*D*(Nat.clog 2 A : ℝ)<2*D*m) : OAI.Computability.BorderVNP.Crossing.PaidIdentity F D m where
  count := A
  net a := placedNetwork (S.wires a) m
  table a := placedTable (S.wires a) (S.tables a)
  placed a := placedNetwork_placed (S.wires a)
  identity x := by
    rw [antipodal_eq,S.realizes]
    exact Finset.sum_congr rfl fun a _ => (placedNetwork_value (S.wires a) (S.tables a) x).symm
  cap := cap
  cost_le a := (placedNetwork_cost (S.wires a)).le.trans (S.cost_le a)
  strict := strict

/-- A shortening on the spectral axes supplies the field and dimension
used by the paid-column stretch theorem. -/
theorem profileShortening (hD : 2 ≤ D) (short : HasProfileShortening F D) :
    OAI.Computability.BorderVNP.Crossing.HasProfileShortening F := by
  obtain ⟨m,A,cap,hm,_,save,⟨S⟩⟩ := exists_paid_network (by omega : 0 < D) short
  exact ⟨D,hD,m,hm,(paidIdentity S save).profileShortening (by omega) hm⟩

end Companion

end

end FiniteFourier
end LinearAlgebra
end OAI
