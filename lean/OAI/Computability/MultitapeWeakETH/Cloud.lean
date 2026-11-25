import OAI.Computability.MultitapeWeakETH.Price
import OAI.Computability.VPVNP.WireCATZero
import OAI.Computability.VPVNP.ExpanderOrders
import OAI.Computability.VPVNP.CubeExclusion

/-! # One-cloud amplification in characteristic zero -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireGeometry VPVNP.Grassmann VPVNP.SpectralGeometry

structure SpectralTarget where
  carrier : Type
  [metric : MetricSpace carrier]
  [complete : CompleteSpace carrier]
  [inhabitedSpace : Nonempty carrier]
  fractions : HasFractions carrier
  realizable : RealizableConfigurations (AlgebraicClosure ℚ) carrier

attribute [instance] SpectralTarget.metric SpectralTarget.complete SpectralTarget.inhabitedSpace

private theorem arc_bound {o D : ℕ} (hD : 0 < D) (G : RegularArcGraph (Fin (2^o)) D)
    {X : Type*} [PseudoMetricSpace X] {β : ℝ}
    (hb : HasPoincareBound X (normalizeArcs G.multiplicity D) β)
    (place : Fin (2^o) → X) :
    (D:ℝ)*(∑ u, ∑ v, dist (place u) (place v)^2) ≤
      β*(2:ℝ)^o * ∑ u, ∑ k : Fin D, dist (place u) (place (G.reverse (u,k)).1)^2 := by
  have cost := G.sum_cost (fun i j => dist (place i) (place j)^2)
  rw [Fintype.sum_prod_type] at cost
  have energy : walkEnergy (normalizeArcs G.multiplicity D) place =
      (∑ u, ∑ k : Fin D, dist (place u) (place (G.reverse (u,k)).1)^2) / D := by
    rw [cost]
    simp only [walkEnergy, normalizeArcs, Finset.sum_div, div_mul_eq_mul_div]
    congr 1
    funext i
    congr 1
    funext j
    rw [dist_comm]
  have bound := hb place
  rw [energy,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at bound
  have pos : (0:ℝ) < D := by exact_mod_cast hD
  field_simp at bound
  nlinarith only [bound]

/-- If one dyadic cloud obeyed a uniform Poincaré bound at the amplification
scale, its iterates would witness Port. A scalar Poincaré bound suffices to
ensure that the doubled graphs are connected. -/
theorem exists_bad_placement (price : PriceZero) {s e n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (H : Matrix (Fin (2^s)) (Fin (2^s)) ℕ) (symm : ∀ i j, H i j = H j i)
    (rows : ∀ i, ∑ j, H i j = 2^e) {β : ℝ} (hβ : 1 ≤ β)
    (time : 1776 * β ≤ 2*(n:ℝ)) (divides : (2*n)*(2*(2*2^e))^(2*n) ∣ 2^s)
    (scalar : HasPoincareBound ℝ (normalizeArcs H (2^e)) β) :
    ∃ X : SpectralTarget, ∃ place : Fin (2^s) → X.carrier,
      β * walkEnergy (normalizeArcs H (2^e)) place <
      (∑ i, ∑ j, dist (place i) (place j)^2) / Fintype.card (Fin (2^s)) := by
  classical
  by_contra! bound
  apply price
  let Y := SpectralTarget.carrier
  have allCAT (a : SpectralTarget) : HasCATZeroSegments (Y a) :=
    hasCATZeroSegments_of_realizable _ a.fractions a.realizable
  have allBounds (a : Option SpectralTarget) :
      HasPoincareBound (withRealLine Y a) (normalizeArcs H (2^e)) β := by
    cases a with
    | none => exact fun x => scalar (fun i => (x i).down)
    | some a => exact bound a
  refine ⟨2^(e+2),6+12*(444*β),by positivity,by linarith,fun minimum => ?_⟩
  obtain ⟨o,ho,G,gs,gl,gr,reach,hG⟩ := exists_expander_orders (withRealLine Y)
    hs hn H symm rows hβ time divides (withRealLine_hasCATZeroSegments Y allCAT)
    allBounds none (fun a => ULift.up a) (fun _ _ => rfl) minimum
  obtain ⟨graph,mult⟩ := exists_regularArcGraph G gs gr gl
  refine ⟨o,ho,graph,?_,?_⟩
  · simpa only [mult] using reach
  · intro X metric complete fractions realizable place
    let : Nonempty X := ⟨place 0⟩
    let a : SpectralTarget := ⟨X,fractions,realizable⟩
    apply arc_bound (by positivity) graph
    rw [show graph.multiplicity = G from funext fun i => funext (mult i)]
    exact hG (some a)

/-- The dyadic cloud and walk parameters can be chosen at a logarithmic
scale in the order, uniformly in the input graph at fixed degree. -/
theorem exists_logarithmic_placement (price : PriceZero) (s e : ℕ) (large : 10000*(e+3) ≤ s)
    (H : Matrix (Fin (2^s)) (Fin (2^s)) ℕ) (symm : ∀ i j, H i j = H j i)
    (rows : ∀ i, ∑ j, H i j = 2^e)
    (scalar : HasPoincareBound ℝ (normalizeArcs H (2^e)) ((s:ℝ)/(10000*(e+3)))) :
    ∃ X : SpectralTarget, ∃ place : Fin (2^s) → X.carrier,
      ((s:ℝ)/(10000*(e+3))) * walkEnergy (normalizeArcs H (2^e)) place <
      (∑ i, ∑ j, dist (place i) (place j)^2) / Fintype.card (Fin (2^s)) := by
  let q := s / (2*(e+3))
  let n := 2^q.log2
  have denom : 0 < 2*(e+3) := by omega
  have qp : 0 < q := Nat.div_pos (by omega) denom
  have below : n ≤ q := Nat.log2_self_le qp.ne'
  have above : q < 2*n := by simpa [n,pow_succ,Nat.mul_comm] using Nat.lt_log2_self (n := q)
  have fits : (2*n)*(e+3) ≤ s := by
    calc
      _ ≤ q*(2*(e+3)) := by nlinarith only [Nat.mul_le_mul_right (2*(e+3)) below]
      _ ≤ _ := Nat.div_mul_le_self ..
  have cover : s < 4*n*(e+3) := by
    apply (Nat.div_lt_iff_lt_mul denom).mp (show s/(2*(e+3)) < 2*n from above) |>.trans_le
    exact le_of_eq (by ring)
  have fitsPow : (2*n)*(2*(2*2^e))^(2*n) ∣ 2^s := by
    have val : 2*(2*2^e) = 2^(e+2) := by ring
    rw [val,← pow_mul,show 2*n = 2^(q.log2+1) by simp [n,pow_succ,Nat.mul_comm],
      ← pow_add]
    apply pow_dvd_pow
    have limit : q.log2+1 ≤ 2*n := by dsimp [n]; have := Nat.lt_two_pow_self (n := q.log2); omega
    nlinarith only [fits,limit,show 2^(q.log2+1) = 2*n by simp [n,pow_succ,Nat.mul_comm]]
  apply exists_bad_placement price (by omega : 0 < s) (by positivity : 0 < n) H symm rows
    _ _ fitsPow scalar
  · apply (le_div_iff₀ (by positivity)).mpr
    rw [one_mul]
    exact_mod_cast large
  · have cov : (s:ℝ) < 4*n*(e+3) := by exact_mod_cast cover
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith

end OAI.Computability.MultitapeWeakETH
