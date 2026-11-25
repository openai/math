import OAI.LinearAlgebra.SpectralBooks.ProfileShortening
import OAI.Computability.BorderVNP.CrossingNormalization

/-! Convert the original crossing's explicit selectors and shared wire strings to
the companion's paid identity at the original block width. -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace CompanionBridge

open scoped BigOperators Classical
open Crossing
noncomputable section
variable {D m A b : ℕ} {K : Type*} [Field K] {budget : ℝ}

private def external (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    (v : AxisSite D) → AxisLeg m v
  | none => ()
  | some p => x p

private def portValue (v : AxisSite D) :
    ((p : {p : Fin D × Bool // some p = v}) → BitString m) → AxisLeg m v :=
  match v with
  | none => fun _ => ()
  | some p => fun x => x ⟨p,rfl⟩

private def net {n : ℕ} (w : Fin n → Wire (AxisSite D)) :
    OAI.Computability.BorderVNP.Crossing.Network D (Fin D × Bool) (fun _ => m) where
  Site := AxisSite D
  Edge := Fin n
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := (w e).left
  dst e := (w e).right
  width e := (w e).width
  attach := some
  position v := -axisPoint v
  in_ball v := by
    simpa only [norm_neg, Metric.mem_closedBall, dist_zero_right] using axisPoint_in_ball v

private theorem placed {n : ℕ} (w : Fin n → Wire (AxisSite D)) :
    (net (m:=m) w).PlacedAt OAI.Computability.BorderVNP.Crossing.antipodalPosition := by
  rintro ⟨i,b⟩
  cases b <;> simp [net, axisPoint, OAI.Computability.BorderVNP.Crossing.antipodalPosition, EuclideanSpace.single, PiLp.single_neg]

private def tables {n : ℕ} (w : Fin n → Wire (AxisSite D)) (T : LocalTables (B:=AxisLeg m) w K) :
    (net (m:=m) w).Tables K :=
  fun v internal ports => T v (portValue v ports) (fun e t =>
    internal ⟨e,t.property.imp Eq.symm Eq.symm⟩ t.val)

private theorem net_value {n : ℕ} (w : Fin n → Wire (AxisSite D)) (T : LocalTables (B:=AxisLeg m) w K)
    (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    (net w).value (tables w T) x = network w T (external x) := by
  classical
  unfold OAI.Computability.BorderVNP.Crossing.Network.value network
  let E : (net (m:=m) w).Assignment ≃ ((e : Fin n) → BitString (w e).width) := Equiv.refl _
  refine Fintype.sum_equiv E _ _ fun s => ?_
  let sites : (net (m:=m) w).Site ≃ AxisSite D := Equiv.refl _
  refine Fintype.prod_equiv sites _ _ fun v => ?_
  change AxisSite D at v
  cases v <;> rfl

private theorem tensor_eq (x : OAI.Computability.BorderVNP.Crossing.Ports (fun _ : Fin D × Bool => m)) :
    OAI.Computability.BorderVNP.Crossing.antipodalTensor K D m x = crossingTensor K D m (external x) := by
  simp only [OAI.Computability.BorderVNP.Crossing.antipodalTensor, crossingTensor, crossingEntry_eq_indicator, funext_iff, external]

private theorem cost_eq {n : ℕ} (w : Fin n → Wire (AxisSite D)) :
    (net (m:=m) w).cost = ∑ e, wireCost (fun s t => dist (axisPoint s) (axisPoint t)) (w e) := by
  unfold OAI.Computability.BorderVNP.Crossing.Network.cost
  let edges : (net (m:=m) w).Edge ≃ Fin n := Equiv.refl _
  refine Fintype.sum_equiv edges _ _ fun i => ?_
  simp [net, edges, wireCost]
  rfl

/-- The selector budget on each one-letter profile already pays the full one-copy selector. -/
private theorem oneHot (S : CrossingNetworkSum K D m A budget) (a : Fin A) :
    profileWireCost S.count S.wires (fun i => if i = a then 1 else 0) 1 b =
      (net (m:=m) (S.wires a)).cost + 2*D*b := by
  have unitDist (v : Fin D × Bool) : dist (axisPoint none) (axisPoint (some v)) = 1 := by
    rcases v with ⟨i,t⟩
    cases t <;> simp [axisPoint]
  rw [cost_eq, profileWireCost]
  congr 1
  · rw [Finset.sum_eq_single a]
    · simp [wireCost]
    · intro i _ h
      simp [h]
    · simp
  · simp only [Nat.one_mul, unitDist, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring

/-- A one-copy paid identity over exactly the same scalar field at exactly the certified width. -/
theorem paidIdentity_of_profile (hD : 2 ≤ D) (h : HasProfileShortening K D) :
    ∃ m > 0, Nonempty (OAI.Computability.BorderVNP.Crossing.PaidIdentity K D m) := by
  classical
  obtain ⟨m,A,b,B,ν,S,code,hm,_hA,hν,_hν',save⟩ := h
  have logWidth : Nat.clog 2 A ≤ b := by
    apply Nat.clog_le_of_le_pow
    simpa [BitString] using Fintype.card_le_of_injective _ code.injective
  let cap : ℝ := (1-ν)*2*D*m - 2*D*b
  refine ⟨m,hm,⟨{
    count := A
    net := fun a => net (m:=m) (S.wires a)
    table := fun a => tables (S.wires a) (S.tables a)
    placed := fun a => placed (S.wires a)
    identity := ?_
    cap := cap
    cost_le := ?_
    strict := ?_ }⟩⟩
  · intro x
    rw [tensor_eq, S.realizes]
    exact Finset.sum_congr rfl fun a _ => (net_value (S.wires a) (S.tables a) x).symm
  · intro a
    have step := (save 1 (fun i => if i = a then 1 else 0) (by simp)).1
    rw [oneHot, Nat.cast_one, mul_one] at step
    dsimp [cap]
    linarith
  · have scale : 0 < 2*(D : ℝ)*m := by
      have : 0 < D := by omega
      positivity
    have round : 2*(D:ℝ)*(Nat.clog 2 A : ℝ) ≤ 2*D*b := by gcongr
    dsimp [cap]
    nlinarith [mul_pos hν scale]

theorem companionProfile (hD : 2 ≤ D) (h : HasProfileShortening K D) :
    OAI.Computability.BorderVNP.Crossing.HasProfileShortening K := by
  obtain ⟨m,hm,⟨e⟩⟩ := paidIdentity_of_profile hD h
  exact ⟨D,hD,m,hm,e.profileShortening (by omega) hm⟩

end
end CompanionBridge

end SpectralBooks
end LinearAlgebra
end OAI
