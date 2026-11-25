import OAI.Computability.BorderVNP.ShortenEpochPhysicalMidpoints
import OAI.Computability.BorderVNP.ShortenRecurrence

/-!
# Both shortening estimates on the actual output at a quotient level

The paid identity fixes a length-saving factor and a scale before any
round is prepared. After choosing the round's relative bins, minimum length
and motion list, its coefficient is independent of the absolute tile count,
input fan-in, and profile counts. The only additive term is proportional to
the number of tiles, from discarding the incomplete pools.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Epoch Cover SeedIntervals Finset
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {I : Type} [Fintype I]

/-- Tile-normalized Euclidean norm of a finite population. -/
noncomputable def tileNorm {T : Type*} [Fintype T] (f : T → ℝ) :=
  Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy f)

/-- Dividing each population by the positive input multiplicity divides
the actual concentration by the same multiplicity. -/
theorem tileNorm_div {T : Type*} [Fintype T] (f : T → ℝ) {k : ℝ} (hk : 0 < k) :
    tileNorm (fun t => f t / k) = tileNorm f / k := by
  have hE : binEnergy (fun t => f t / k) = binEnergy f / k^2 := by
    simp only [binEnergy, div_pow, sum_div]
  rw [tileNorm, tileNorm, hE, Real.sqrt_div (show 0 ≤ binEnergy f from sum_nonneg fun _ _ => sq_nonneg _), Real.sqrt_sq hk.le,
    mul_div_assoc]

variable {B : Type} [Fintype B] {d : ℕ} {P : Type*} {bits : P → ℕ}

/-- The output coordinate X, using only positive-length charged cables,
counted in tiles of their physical quotient midpoints. -/
noncomputable def Placement.outputConcentration
    (p : Pack D P bits K) (bin : p.layout.Edge → Option ((I → Deck (d+1)) × B))
    (perm : Fin D → Equiv.Perm ((I → Deck (d+1)) × B)) (e : PaidIdentity K D m)
    (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1)))
    (q : Counts e p bin perm) : ℝ :=
  let tile := fun x => productTileName d (g.outputMidpoint p bin perm e positive q x)
  tileNorm fun o => testedWidth (physical p bin perm e positive q).width (g.inTile p bin perm e positive q tile o)

set_option maxHeartbeats 1500000 in
/-- A uniform coefficient for both lines of (6.3) at one prepared round.
The mean factor may be the inverse of its minimum positive segment
length, and the motion factor comes from its bounded tile predecessors.
The same estimates hold on every realized branch in every sufficiently
deep quotient satisfying the displayed input midpoint and bin identities. -/
theorem physical_rows (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ {B : Type} [Fintype B]
      (meanFactor motionFactor : ℝ), 0 ≤ meanFactor → 0 ≤ motionFactor →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d k : ℕ), 0 < k → ∀ {P : Type*} {bits : P → ℕ}
      (p : Pack D P bits K) (bin : p.layout.Edge → Option ((I → Deck (d+1)) × B))
      (perm : Fin D → Equiv.Perm ((I → Deck (d+1)) × B)) (positive : p.layout.Edge → Bool)
      (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))), g.fits p bin perm positive h ν →
      ∀ (oldMid : p.layout.Edge → SurfaceHost I (d+1)) (addr : p.layout.Edge → ((I → Deck (d+1)) × B)),
      (∀ c a, bin c = some a → addr c = a ∧ a.1 = productTileName d (oldMid c) ∧
        dist (oldMid c) (g.old (p.layout.src c)) ≤ dist (g.old (p.layout.src c)) (g.old (p.layout.dst c))/2) →
      (∀ a, (perm 0 a).1 = productTileName d (g.project a (g.chart a).center)) →
      ∀ (mean : ((I → Deck (d+1)) × B) → ℝ) (Xmax V : ℝ), 0 ≤ Xmax →
        (Fintype.card (I → Deck (d+1)) : ℝ) ≤ V →
        let W := g.input p bin perm / k
        W / 2 ≤ matchedLength perm (fun a => 2*(g.chart a).radius) mean →
        Real.sqrt (Fintype.card (I → Deck (d+1))) * Real.sqrt (binEnergy mean) ≤ meanFactor * W →
        Real.sqrt (Fintype.card (I → Deck (d+1))) *
          Real.sqrt (binEnergy fun a => count p.layout bin a / k - mean a) ≤ motionFactor * Xmax / Real.sqrt k →
        ∀ q : Counts e p bin perm,
        g.result e p bin perm positive q / k ≤ max 0 (1-(ν/2)/2) * W +
          C * (Real.sqrt k)⁻¹ * Xmax + C * V ∧
        g.outputConcentration p bin perm e positive q / k ≤ C * (W + (Real.sqrt k)⁻¹ * Xmax) := by
  obtain ⟨ν,hν,h,hh,length⟩ := normalized_length (I := I) e hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro B _ u v hu hv
  obtain ⟨M,locality⟩ := physical_midpoint_support (I := I) (B := B) e h ν hh.le hν.le
  let G : ℝ := ((1 + profileWidthBound e : ℕ) : ℝ) *
    Real.sqrt (((M * Fintype.card B : ℕ) : ℝ) * M)
  let E := (ν/2) * ((D : ℝ) * (2*h * Real.sqrt (Fintype.card B)))
  let R := (ν/2) * ((Fintype.card B : ℝ) * (2*h * (D*m : ℕ)))
  let C := max (max (E*v) R) (max (G*u) (G*v))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := (mul_nonneg hE hv).trans ((le_max_left ..).trans (le_max_left ..))
  have hEv : E*v ≤ C := (le_max_left ..).trans (le_max_left ..)
  have hR : R ≤ C := (le_max_right ..).trans (le_max_left ..)
  have hGu : G*u ≤ C := (le_max_left ..).trans (le_max_right ..)
  have hGv : G*v ≤ C := (le_max_right ..).trans (le_max_right ..)
  refine ⟨C,hC,?_⟩
  intro d k hk P bits p bin perm positive g fits oldMid addr hbin hctr mean X V hX hV W half hmean dev q
  let T := I → Deck (d+1)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  let t := (Real.sqrt k)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hw : 0 ≤ W := by
    apply div_nonneg _ hk'.le
    unfold Placement.input chargedLength
    apply sum_nonneg
    intro x _; split_ifs <;> positivity
  obtain ⟨near,hin,hout,hs⟩ := locality d
  obtain ⟨hret,hhook,hnew⟩ := hs p bin perm positive g fits oldMid addr hbin hctr q
  let tile := fun x => productTileName d (g.outputMidpoint p bin perm e positive q x)
  have hlen := length p bin perm positive g fits k hk' mean _ half dev q
  have hconc := normalized_concentration p bin perm e hm positive g q tile addr
    (fun c a hc => (hbin c a hc).1) near hret hhook hnew (M*Fintype.card B) M hin (fun a => by
      apply le_trans _ (hout a)
      apply Nat.le_of_eq
      apply congrArg Finset.card
      ext o
      simp) mean hk' hmean dev
  let n := fun o => (testedWidth (physical p bin perm e positive q).width (g.inTile p bin perm e positive q tile o) : ℝ)
  change tileNorm (fun o => n o / k) ≤ G * (u*W + v*X/Real.sqrt k) at hconc
  rw [tileNorm_div n hk'] at hconc
  have hsum : (∑ a, (2*(g.chart a).radius) * (D*m : ℕ)) ≤
      (Fintype.card T : ℝ) * ((Fintype.card B : ℝ) * (2*h * (D*m : ℕ))) := by
    calc
      _ ≤ ∑ _ : T × B, 2*h * (D*m : ℕ) := sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fits.1 a).2 (by norm_num)) (Nat.cast_nonneg _)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hsum0 : 0 ≤ ∑ a, (2*(g.chart a).radius) * (D*m : ℕ) :=
    sum_nonneg fun a _ => mul_nonneg (mul_nonneg (by norm_num) (fits.1 a).1) (Nat.cast_nonneg _)
  have hround : (ν/2) * ((∑ a, (2*(g.chart a).radius) * (D*m : ℕ)) / k) ≤ C*V := by
    have hr0 : 0 ≤ R := by dsimp [R]; positivity
    calc
      _ ≤ (ν/2) * ((Fintype.card T : ℝ) * ((Fintype.card B : ℝ) * (2*h * (D*m : ℕ)))) :=
        mul_le_mul_of_nonneg_left ((div_le_self hsum0 hk1).trans hsum) (by positivity)
      _ = R * Fintype.card T := by dsimp [R]; ring
      _ ≤ R * V := mul_le_mul_of_nonneg_left hV hr0
      _ ≤ C * V := mul_le_mul_of_nonneg_right hR ((Nat.cast_nonneg _).trans hV)
  constructor
  · refine hlen.trans (add_le_add (add_le_add ?_ ?_) hround)
    · exact mul_le_mul_of_nonneg_right (le_max_right ..) hw
    · calc
        _ = E*v * t * X := by dsimp [E,t]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEv ht) hX
  · change tileNorm n / k ≤ _
    refine hconc.trans ?_
    calc
      _ = G*u * W + (G*v)*(t*X) := by dsimp [t]; ring
      _ ≤ C * W + C*(t*X) :=
        add_le_add (mul_le_mul_of_nonneg_right hGu hw) (mul_le_mul_of_nonneg_right hGv (mul_nonneg ht hX))
      _ = _ := by ring

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
