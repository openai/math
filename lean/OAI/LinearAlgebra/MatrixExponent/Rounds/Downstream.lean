import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Packing.Beat

/-! # Combining the local and beat selectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

/-- A common upper bound on the fixed overheads, independent of the
width scale, working field and input tensor. -/
def Plan.budget (s : Plan) (A : ℕ) := s.seats + (s.K * s.cover + A * 10000) + s.K * s.D ^ s.C + s.K

variable {F : Type} [Field F] {x y : Wire} {h a r z : ℕ}
  {s : Plan} (hs : s.Fits) (p : Reduction F s.c 3 s.b s.n s.e s.K s.ρ s.loss)
  {L : ℝ} {T R g A : ℕ} {P : Input F x y h s.D T R g (10000 * L)}
include hs p

theorem LocalExpansion.finish (hT : 0 < T) (hz : 0 < z)
    (unit : (s.b * z) * s.D ^ s.c ≤ T) (unit' : T ≤ z * s.M)
    (ex : LocalExpansion P (s.b * z) s.C s.d 10 A)
    (ha : a + s.n * r ≤ h) (hr : s.budget A ≤ 2 ^ r)
    (slack : (s.budget A : ℝ) * T * (Fintype.card P.V * 2 ^ h : ℕ) ≤ L * (2 : ℝ) ^ r) :
    Expansion P.diagram.eval (s.budget A * (1 + Nat.clog 2 (T + 1))*⌈L / (T : ℝ)⌉₊)
      (fun B : Board F x y a => B.Ready 4 s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
        B.seats ≤ s.budget A * (Fintype.card P.V * 2 ^ h)) := by
  have hL : 0 ≤ L := by
    have : (0 : ℝ) ≤ 10000 * L := (by positivity : (0 : ℝ) ≤ (univ.image P.place).card * s.D * T) |>.trans P.occupied
    linarith
  let m := ⌈L / (T : ℝ)⌉₊
  let n := 1 + Nat.clog 2 (T + 1)
  have hocc : (univ.image P.place).card ≤ 10000 * m := by
    have hD : (1 : ℝ) ≤ s.D := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) (s.two hs))
    have hf := (div_le_iff₀ (Nat.cast_pos.mpr hT : (0 : ℝ) < T)).mp (Nat.le_ceil (L / (T : ℝ)))
    have hb : ((univ.image P.place).card : ℝ) * T ≤ 10000 * (m : ℝ) * T := calc
      _ ≤ ((univ.image P.place).card : ℝ) * s.D * T :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hD) (by positivity)
      _ ≤ 10000 * L := P.occupied
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hf (by norm_num)
    exact_mod_cast le_of_mul_le_mul_right hb (Nat.cast_pos.mpr hT)
  have hk : s.K ≤ s.budget A := by unfold Plan.budget; omega
  have hh : s.K * s.D ^ s.C ≤ s.budget A := by unfold Plan.budget; omega
  have hsl : (s.K * s.D ^ s.C : ℕ) * (T : ℝ) * (Fintype.card P.V * 2 ^ h : ℕ) ≤ L * (2 : ℝ) ^ r := by
    refine le_trans ?_ slack
    gcongr
  obtain ⟨I, _, Q, c, hi, he, hc⟩ := ex
  have second i := (hc i).process hs p hL hT hz rfl unit unit' ha (hk.trans hr) hsl
  choose J hJ B b hj he' hB using second
  let : ∀ i, Fintype (J i) := hJ
  refine ⟨Σ i, J i, inferInstance, fun q => B q.1 q.2, fun q => c q.1 * b q.1 q.2, ?_, ?_, ?_⟩
  · have hi' : Fintype.card I ≤ 2 ^ (A * n * (10000 * m)) :=
      hi.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hocc))
    have hn : 1 ≤ n := by unfold n; omega
    have hs' : A * 10000 + s.K * s.cover ≤ s.budget A := by unfold Plan.budget; omega
    have hnum : A * n * (10000 * m) + s.K * (s.cover * m) ≤ s.budget A * n * m := calc
      _ ≤ A * n * (10000 * m) + s.K * (s.cover * m) * n :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hn) _
      _ = (A * 10000 + s.K * s.cover) * n * m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs')
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : I, 2 ^ (s.K * (s.cover * m)) := sum_le_sum fun i _ => hj i
      _ ≤ 2 ^ (A * n * (10000 * m)) * 2 ^ (s.K * (s.cover * m)) := by
        simpa only [sum_const, card_univ, Nat.nsmul_eq_mul] using Nat.mul_le_mul_right _ hi'
      _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) hnum
  · intro x y
    rw [Fintype.sum_sigma, ← he x y]
    apply sum_congr rfl
    intro i _
    rw [← he' i x y, mul_sum]
    exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  · rintro ⟨i, j⟩
    exact ⟨(hB i j).1, (hB i j).2.trans (Nat.mul_le_mul_right _ (by unfold Plan.budget; omega))⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

section
/-!
# A round from local concentration

The subdivision factor and reset overhead are fixed over the ground
field. Only the input packet width and the necessary working-field
size change as the scale grows.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Filter

theorem downstream {k : Type} [Field k] (tag : Radix.WideTag k) (law : LocalLaw k 10)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1) (g : ℕ) (hg : 0 < g) :
    ∃ (D n v p H : ℕ) (θ : ℝ),
      g < D ∧ 0 < n ∧ 0 < v ∧ 0 < p ∧ (p : ℝ) ≤ v * (1 + δ / 3) ∧ 0 < θ ∧
      ∃ (A : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra k M),
        ∀ᶠ T : ℕ in atTop, ∃ R : ℕ, 0 < R ∧ R * D ^ 2 ≤ T ∧
          ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra M K),
            A * (1 + T) ^ A ≤ Fintype.card K →
            ∀ (x y : Wire) (h a r : ℕ) (L : ℝ) (P : Input K x y h D T R g (10000 * L)),
              a + n * r ≤ h → H ≤ 2 ^ r →
              (H : ℝ) * T * (Fintype.card P.V * 2 ^ h : ℕ) ≤ L * (2 : ℝ) ^ r →
              Expansion P.diagram.eval (H * (1 + Nat.clog 2 (T + 1))*⌈L / (T : ℝ)⌉₊)
                (fun B : Board K x y a => B.Ready 4 D (2 ^ p * T) (L / (2 : ℝ) ^ v) θ ∧
                  B.seats ≤ H * (Fintype.card P.V * 2 ^ h)) := by
  obtain ⟨C, hC⟩ := law g hg
  obtain ⟨d₀, hex⟩ := eventually_atTop.mp hC
  obtain ⟨b, n, e, H, B, hn, he, beat⟩ := beats (.inl tag) (C + 12) (by omega)
  have hB := (beat 1 (by decide) k).loss
  obtain ⟨d, v, p, hlarge, hv, hp, hvp, hb, hK, hm, hq, ha⟩ :=
    choose_restart (C + 12) e b H (d₀ + g + C + 12) (↑(10000 * (C + 1) : ℕ)) B δ (by positivity) hB hδ hd
  let s : Plan := ⟨C, d, v, p, b ^ (2 * v), n * (2 * v), e ^ (2 * v), H ^ (2 * v), B⟩
  have grow : d < s.D := Nat.lt_two_pow_self
  have fits : s.Fits := ⟨(show C + 12 ≤ s.D by omega), hK, hb, hm, hq, ha⟩
  have red (K : Type) [Field K] [Algebra k K] :
      Reduction K s.c 3 s.b s.n s.e s.K s.ρ s.loss :=
    beat (2 * v) (by omega) K
  have pos := (red k).unit
  obtain ⟨A, M, _, _, _, go⟩ := hex d (by omega)
  have hd' : 0 < s.D := by unfold Plan.D; positivity
  have hf : 0 < s.floor := by unfold Plan.floor Plan.M; positivity
  refine ⟨s.D, s.n, v, p, s.budget A, s.floor, by omega, Nat.mul_pos hn (by omega), hv, hp, hvp, hf,
    A, M, inferInstance, inferInstance, inferInstance, ?_⟩
  filter_upwards [go, eventually_ge_atTop (s.b * s.D ^ s.c)] with T hloc hT
  obtain ⟨R, hR, hRT, ex⟩ := hloc
  obtain ⟨z, hz, hunit, hunit'⟩ := s.units fits pos T hT
  refine ⟨R, hR, hRT, ?_⟩
  intro K fK tK aK hcard x y h a r L P hlen hr slack
  let : Algebra k K := ((algebraMap M K).comp (algebraMap k M)).toAlgebra
  have ok : (s.b * z) * s.D ^ s.C ≤ T :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd' s.small)).trans hunit
  have hlocal := ex K fK tK aK hcard (s.b * z) (Nat.mul_pos pos hz) ok x y h (10000 * L) P
  exact hlocal.finish fits (red K) (lt_of_lt_of_le (by positivity) hT) hz hunit hunit' hlen hr slack

end OAI.LinearAlgebra.MatrixExponent.Rounds
end
