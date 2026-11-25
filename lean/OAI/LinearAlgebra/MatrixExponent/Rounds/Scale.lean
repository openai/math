import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Packing.TetherHost
import OAI.LinearAlgebra.MatrixExponent.Shaving.Design
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import Mathlib.Analysis.Real.Sqrt
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection

/-! # Weighted expansions with independent exterior positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Finset

variable {F : Type} [Field F] {x y : Wire} {a b : ℕ}

/-- The index budget counts binary choices. Scalar factors include any
zero-arity stations removed between rounds. -/
def Expansion (f : Val x → Val y → F) (n : ℕ) (P : Board F x y a → Prop) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (q : I → Board F x y a) (c : I → F),
    Fintype.card I ≤ 2 ^ n ∧ (∀ x y, ∑ i, c i * (q i).diagram.eval x y = f x y) ∧ ∀ i, P (q i)

variable {f : Val x → Val y → F} {P P' : Board F x y a → Prop} {Q : Board F x y b → Prop}
  {n m : ℕ}

theorem Expansion.single (q : Board F x y a) (hq : P q) : Expansion q.diagram.eval n P :=
  ⟨Unit, inferInstance, fun _ => q, fun _ => 1, Nat.one_le_pow _ _ (by decide),
    fun _ _ => by simp, fun _ => hq⟩

theorem Expansion.mono (hf : Expansion f n P) (h : n ≤ m) (hp : ∀ q, P q → P' q) :
    Expansion f m P' := by
  obtain ⟨I, _, q, c, hi, he, hq⟩ := hf
  exact ⟨I, inferInstance, q, c, hi.trans (Nat.pow_le_pow_right (by decide) h), he, fun i => hp _ (hq i)⟩

theorem Expansion.bind (hf : Expansion f n P) (hg : ∀ q, P q → Expansion q.diagram.eval m Q) :
    Expansion f (n + m) Q := by
  obtain ⟨I, _, q, c, hi, he, hp⟩ := hf
  choose J hJ t d ht he' hp' using fun i => hg (q i) (hp i)
  let : ∀ i, Fintype (J i) := hJ
  refine ⟨Σ i, J i, inferInstance, fun p => t p.1 p.2, fun p => c p.1 * d p.1 p.2, ?_, ?_, ?_⟩
  · rw [Fintype.card_sigma, pow_add]
    refine le_trans (sum_le_sum (s := univ) fun i _ => ht i) ?_
    simpa only [sum_const, card_univ, Nat.nsmul_eq_mul] using Nat.mul_le_mul_right (2 ^ m) hi
  · intro x y
    rw [Fintype.sum_sigma, ← he x y]
    apply sum_congr rfl
    intro i _
    rw [← he' i x y, mul_sum]
    exact sum_congr rfl (fun j _ => mul_assoc _ _ _)
  · exact fun p => hp' p.1 p.2

omit [Field F] in
theorem Board.Ready.relax {P : Board F x y a} {g g' D T : ℕ} {L L' θ θ' : ℝ}
    (h : P.Ready g D T L θ) (hg : g ≤ g') (hL : L ≤ L') (hθ : θ' ≤ θ) :
    P.Ready g' D T L' θ' := by
  refine ⟨fun v => (h.1 v).trans hg, h.2.1.trans hL,
    h.2.2.1.trans (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg _)), fun v => ?_⟩
  exact ⟨(h.2.2.2 v).1, (h.2.2.2 v).2.imp_right fun ht =>
    (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)).trans ht⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Iterating rounds with uniform control of all summands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

/-- A round divides the total budget by `2^gain` and multiplies the
width by `2^growth`. The initial host degree bound is five. -/
structure Design (δ : ℝ) where
  D : ℕ
  steps : ℕ
  gain : ℕ
  growth : ℕ
  overhead : ℕ
  floor : ℝ
  large : 8 ≤ D
  steps_pos : 0 < steps
  gain_pos : 0 < gain
  growth_pos : 0 < growth
  overhead_large : 2 ≤ overhead
  floor_pos : 0 < floor
  floor_le : floor ≤ 4
  ratio : (growth : ℝ) ≤ gain * (1 + δ / 3)

namespace Design

variable {δ : ℝ} (p : Design δ)

def width (T i : ℕ) := 2 ^ (p.growth * i) * T

def budget (L : ℝ) (i : ℕ) := L / (2 : ℝ) ^ (p.gain * i)

def bits (T : ℕ) (L : ℝ) := p.overhead * (1 + Nat.clog 2 (T + 1)) * ⌈L / (T : ℝ)⌉₊

def Works (F : Type) [Field F] (T : ℕ) : Prop :=
  ∀ {x y : Wire} {h : ℕ} (P : Board F x y h) (r a : ℕ) (L : ℝ),
    P.Ready 5 p.D T L p.floor → a + p.steps * r ≤ h → p.overhead ≤ 2 ^ r →
    ((wd x + wd y : ℕ) : ℝ) * p.D ≤ L → (p.overhead : ℝ) * T * P.seats ≤ L * (2 : ℝ) ^ r →
    Expansion P.diagram.eval (p.bits T L) (fun Q : Board F x y a =>
      Q.Ready 5 p.D (2 ^ p.growth * T) (L / 2 ^ p.gain) p.floor ∧ Q.seats ≤ p.overhead * P.seats)

theorem width_succ (T i : ℕ) : p.width T (i + 1) = 2 ^ p.growth * p.width T i := by
  simp only [width, mul_add, mul_one, pow_add]
  ring

theorem budget_succ (L : ℝ) (i : ℕ) : p.budget L (i + 1) = p.budget L i / 2 ^ p.gain := by
  simp only [budget, mul_add, mul_one, pow_add, div_div]

theorem iterate {F : Type} [Field F] {x y : Wire} {h : ℕ} (P : Board F x y h)
    (T j a r : ℕ) (L : ℝ) (initial : P.Ready 5 p.D T L p.floor)
    (steps : a + p.steps * j * r = h) (size : p.overhead ≤ 2 ^ r)
    (ok : ∀ i < j, p.Works F (p.width T i))
    (exposed : ∀ i < j, ((wd x + wd y : ℕ) : ℝ) * p.D ≤ p.budget L i)
    (slack : ∀ i < j, (p.overhead : ℝ) * p.width T i * (p.overhead ^ i * P.seats : ℕ) ≤
      p.budget L i * (2 : ℝ) ^ r) :
    Expansion P.diagram.eval (∑ i ∈ Finset.range j, p.bits (p.width T i) (p.budget L i))
      (fun Q : Board F x y a => Q.Ready 5 p.D (p.width T j) (p.budget L j) p.floor ∧
        Q.seats ≤ p.overhead ^ j * P.seats) := by
  induction j generalizing a with
  | zero =>
    have : a = h := by simpa using steps
    subst a
    refine Expansion.single P ?_
    simpa only [width, budget, pow_zero, mul_zero, div_one, one_mul, le_refl, and_true]
  | succ j ih =>
    have he := ih (a + p.steps * r) (by rw [← steps]; ring)
      (fun i hi => ok i (by omega)) (fun i hi => exposed i (by omega))
      (fun i hi => slack i (by omega))
    rw [Finset.sum_range_succ]
    apply he.bind
    rintro q ⟨hr, hb⟩
    have hm := ok j (by omega) q r a (p.budget L j) hr le_rfl size (exposed j (by omega))
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hb) (by positivity)).trans (slack j (by omega)))
    refine hm.mono le_rfl (fun t ht => ?_)
    rw [p.width_succ, p.budget_succ, pow_succ', mul_assoc]
    exact ⟨ht.1, ht.2.trans (Nat.mul_le_mul_left _ hb)⟩

end Design
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

section
/-!
# Restarting a round after tether restoration

The full degree may grow as a power whose exponent itself grows
exponentially in the number of beats. Only its logarithm enters the
mass loss. The square loss uses the shorter tree at a frozen member.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing

private theorem tether_steps (l j : ℕ) :
    Detour.steps (Tether.width (2 ^ l) (2 ^ j) (2 ^ j)) ≤ 2 * (l + 2 * j + 2) + 3 := by
  have h : Nat.clog 2 (Tether.width (2 ^ l) (2 ^ j) (2 ^ j)) ≤ l + 2 * j + 2 := by
    apply Nat.clog_le_of_le_pow
    rw [Tether.width, Nat.clog_pow _ _ (by decide)]
    have hs : 2 ^ j + 1 ≤ 2 ^ (j + 1) := by rw [pow_succ]; have := Nat.one_le_pow j 2 (by decide); omega
    calc
      _ ≤ 2 ^ l * 2 ^ (j + 1) * 2 ^ (j + 1) := by gcongr
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  unfold Detour.steps
  omega

/-- Choose a working scale, number of beats and restart multiplier
before choosing the input network or working extension. -/
theorem choose_restart (c e b H d₀ : ℕ) (A B δ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ d v p : ℕ,
      let D : ℕ := 2 ^ d
      let t := 2 * v
      let s := D ^ (c + 15)
      let a : ℝ := Nat.clog 2 s
      let m : ℝ := Detour.steps (Tether.width (D ^ (c * e ^ t)) s s)
      d₀ ≤ d ∧ 0 < v ∧ 0 < p ∧ (p : ℝ) ≤ v * (1 + δ / 3) ∧ b ^ t ≤ D ∧ H ^ t ≤ D ∧
      2 * ((1 / 2) ^ t * A * (1 + (d : ℝ)) ^ 2 + B * ((A + 1) / Real.sqrt D)) +
        (1 + 2 * (m + a)) * (A / Real.sqrt D) ≤ 1 / (2 : ℝ) ^ v ∧
      3 * (1 + 4 * a) * A + 9 ≤ (2 : ℝ) ^ p / (2 : ℝ) ^ v ∧
      3 * (1 + A * (D : ℝ)) ≤ (D : ℝ) * (2 : ℝ) ^ p / 2 := by
  let k := 29 * A + 2 * B * (A + 1) + 9
  have hk : 0 ≤ k := by unfold k; positivity
  obtain ⟨d, v, p, hd, hv, hvd, hscale, hvp, hp, hsmall, hgain⟩ :=
    Shaving.choose_round hδ hδ' (e + b + H) (k * (c + 15)) (by positivity) 2 d₀
  let D : ℕ := 2 ^ d
  let t := 2 * v
  let s := D ^ (c + 15)
  let a : ℝ := Nat.clog 2 s
  let m : ℝ := Detour.steps (Tether.width (D ^ (c * e ^ t)) s s)
  let G := (2 : ℝ) ^ v
  let E := (D : ℝ) ^ (1 / 100 : ℝ)
  have hD : 1 ≤ (D : ℝ) := by simp only [D, Nat.cast_pow, Nat.cast_ofNat]; exact one_le_pow₀ (by norm_num)
  have hG : 1 ≤ G := one_le_pow₀ (by norm_num)
  have hGE : G ≤ E := by
    have ht : (100 : ℝ) * v ≤ d := by exact_mod_cast hvd
    unfold G E D
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast 2 v]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hE : 1 ≤ E := hG.trans hGE
  have hED : E ≤ (D : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (1 / 100 : ℝ) ≤ 1)
  have hroot : G ^ 2 * E ≤ Real.sqrt D := calc
    _ ≤ E ^ 2 * E := by gcongr
    _ = (D : ℝ) ^ ((1 / 100 : ℝ) * 3) := by
      rw [← pow_succ, show (3 : ℝ) = ↑(3 : ℕ) by norm_num, Real.rpow_mul_natCast (by positivity)]
    _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
  have grow (x : ℕ) (hx : x ≤ e + b + H) : (x : ℝ) ^ t ≤ E := calc
    _ ≤ ((e : ℝ) + b + H) ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hx) _
    _ ≤ _ := by simpa only [E, D, Nat.cast_pow, Nat.cast_ofNat] using hscale
  have bound (x : ℕ) (hx : x ≤ e + b + H) : x ^ t ≤ D := by
    exact_mod_cast (grow x hx).trans hED
  have hp' : 0 < p := by
    have : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hvp
    exact_mod_cast this
  let f := (1 + (d : ℝ)) ^ 2 * ((c : ℝ) + 15)
  have hdf : (1 + (d : ℝ)) ^ 2 ≤ f := le_mul_of_one_le_right (by positivity) (by linarith)
  have hf : 1 ≤ f := le_trans (one_le_pow₀ (by linarith)) hdf
  have hfE : f ≤ f * E := le_mul_of_one_le_right (by positivity) hE
  have hf₂ : (d : ℝ) * (c + 15) ≤ f :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have ha : a ≤ f := by
    simpa only [a, s, D, ← pow_mul, Nat.clog_pow 2 _ (by decide), Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat] using hf₂
  have hm : m ≤ 13 * f * E := by
    have hm' : Detour.steps (Tether.width (D ^ (c * e ^ t)) s s) ≤
        2 * (d * (c * e ^ t) + 2 * (d * (c + 15)) + 2) + 3 := by
      simpa only [D, s, pow_mul] using tether_steps (d * (c * e ^ t)) (d * (c + 15))
    have h : m ≤ 2 * ((d : ℝ) * (c * (e : ℝ) ^ t) + 2 * (d * (c + 15)) + 2) + 3 := by
      unfold m
      exact_mod_cast hm'
    have hi : (d : ℝ) * c * (e : ℝ) ^ t ≤ f * E := mul_le_mul
      (le_trans (by gcongr; linarith) hf₂) (grow e (by omega)) (by positivity) (by positivity)
    linarith only [h, hi, hf₂, hfE, hf]
  have hfirst : k * f ≤ G / 2 := by unfold f G; linarith only [hsmall]
  have hsecond : 2 * k * f ≤ (2 : ℝ) ^ p / G := by
    apply (le_div_iff₀ (by positivity)).mpr
    unfold G f
    linarith only [hgain]
  have hbase : 29 * A + 9 ≤ k := by unfold k; nlinarith [mul_nonneg hB hA]
  refine ⟨d, v, p, hd, hv, hp', hp, bound b (by omega), bound H (by omega), ?_, ?_, ?_⟩
  · have hcore : 2 * A * (1 + d) ^ 2 ≤ G / 2 :=
      (mul_le_mul (by linarith : 2 * A ≤ k) hdf (by positivity) hk).trans hfirst
    have htail : 2 * B * (A + 1) + (1 + 2 * (m + a)) * A ≤ G / 2 * E := by
      have h₁ := mul_le_mul_of_nonneg_right (show 1 + 2 * (m + a) ≤ 29 * f * E by linarith only [hm, ha, hf, hfE]) hA
      have h₂ := le_mul_of_one_le_right (show 0 ≤ 2 * B * (A + 1) by positivity) (hf.trans hfE)
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hfirst (by positivity : 0 ≤ E))
      unfold k
      linarith only [h₁, h₂, hf, hfE]
    have hpow : (1 / 2 : ℝ) ^ t = 1 / G ^ 2 := by simp only [t, G, one_div_pow, pow_mul']
    change 2 * ((1 / 2 : ℝ) ^ t * A * (1 + d) ^ 2 + B * ((A + 1) / Real.sqrt D)) + (1 + 2 * (m + a)) * (A / Real.sqrt D) ≤ 1 / G
    calc
      _ = (2 * A * (1 + d) ^ 2) / G ^ 2 + (2 * B * (A + 1) + (1 + 2 * (m + a)) * A) / Real.sqrt D := by rw [hpow]; ring
      _ ≤ (G / 2) / G ^ 2 + (G / 2 * E) / (G ^ 2 * E) := by gcongr
      _ = _ := by field_simp; ring
  · have hi := mul_le_mul_of_nonneg_right (show 3 * (1 + 4 * a) ≤ 15 * f by linarith only [ha, hf]) hA
    have := mul_le_mul_of_nonneg_right hbase (show 0 ≤ f by positivity)
    change 3 * (1 + 4 * a) * A + 9 ≤ (2 : ℝ) ^ p / G
    linarith only [hi, this, hf, hsecond, mul_nonneg hA (show 0 ≤ f by positivity)]
  · have hi : 6 * (1 + A) ≤ (2 : ℝ) ^ p := calc
      _ ≤ 2 * k := by linarith
      _ ≤ 2 * k * f := le_mul_of_one_le_right (by positivity) hf
      _ ≤ (2 : ℝ) ^ p / G := hsecond
      _ ≤ _ := div_le_self (by positivity) hG
    have := mul_le_mul_of_nonneg_left hi (show 0 ≤ (D : ℝ) by positivity)
    change 3 * (1 + A * (D : ℝ)) ≤ (D : ℝ) * (2 : ℝ) ^ p / 2
    linarith only [hD, this]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # From the initial stack to the terminal family of charged boards -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Design

open Finset
variable {δ : ℝ} (p : Design δ)

private theorem width_pow (t i : ℕ) : p.width (2 ^ t) i = 2 ^ (t + p.growth * i) := by
  rw [width, pow_add, mul_comm]

private theorem bits_le (t i j S : ℕ) (hi : i ≤ j) :
    p.bits (p.width (2 ^ t) i) (p.budget ((S : ℝ) * 2 ^ t) i) ≤
      p.overhead * (2 + t + p.growth * j) * S := by
  have hw : 0 < p.width (2 ^ t) i := by rw [width_pow]; positivity
  have hlog : Nat.clog 2 (p.width (2 ^ t) i + 1) ≤ 1 + t + p.growth * j := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [p.width_pow, show 1 + t + p.growth * j = (t + p.growth * j) + 1 by omega, pow_succ]
    have a : 2 ^ (t + p.growth * i) ≤ (2 : ℕ) ^ (t + p.growth * j) := by gcongr
    have b : 0 < (2 : ℕ) ^ (t + p.growth * j) := by positivity
    omega
  have hs : ⌈p.budget ((S : ℝ) * 2 ^ t) i / p.width (2 ^ t) i⌉₊ ≤ S := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (Nat.cast_pos.mpr hw)]
    refine le_trans (div_le_self (by positivity) (one_le_pow₀ (by norm_num))) ?_
    rw [width_pow, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    · norm_num
    · omega
  unfold bits
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hs

/-- Each round can spend the same exponent of two on grouping.
Both the exterior condition and slack are checked before iteration. -/
theorem run {F : Type} [Field F] {x y : Wire} (G : Diagram F x y) (t j a r m : ℕ)
    (size : G.cost ≤ m) (arity : ∀ v, G.arity v ≤ 2 ^ t)
    (ok : ∀ i < j, p.Works F (p.width (2 ^ t) i))
    (ext : (wd x + wd y) * p.D * 2 ^ (p.gain * j) ≤ m)
    (room : p.overhead ^ (j + 1) * 2 ^ ((p.gain + p.growth) * j) ≤ 2 ^ r) :
    let h := a + p.steps * j * r
    let d := 2 ^ t * 2 ^ h
    let S := 32 * m * (t + 1) * 2 ^ h
    Expansion (power G.eval d) (j * (p.overhead * (2 + t + p.growth * j) * S))
      (fun Q : Board F _ _ a =>
        Q.Ready 5 p.D (2 ^ (t + p.growth * j)) (((S : ℝ) * 2 ^ t) / (2 : ℝ) ^ (p.gain * j)) p.floor ∧
        Q.seats ≤ p.overhead ^ j * S) := by
  intro h d S
  obtain ⟨P, he, hp, initial⟩ := Stack.initial G t h p.D p.floor arity p.large p.floor_le
  have total : 16 * P.seats ≤ S := calc
    _ ≤ 16 * (2 * m * (t + 1) * 2 ^ h) := by
      unfold Board.seats
      gcongr
      exact hp.trans (by gcongr)
    _ = _ := by unfold S; ring
  have hseat : P.seats ≤ S := (Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans total
  let L := (S : ℝ) * 2 ^ t
  have start : P.Ready 5 p.D (2 ^ t) L p.floor := by
    refine initial.relax le_rfl ?_ le_rfl
    have hx : 16 * (P.seats : ℝ) ≤ S := by exact_mod_cast total
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have limit i (hi : i ≤ j) : p.overhead ^ (i + 1) * 2 ^ ((p.gain + p.growth) * i) ≤ 2 ^ r := by
    have := p.overhead_large
    refine le_trans ?_ room
    gcongr
  have hsize : p.overhead ≤ 2 ^ r := by simpa using limit 0 (Nat.zero_le j)
  have exposed i (hi : i < j) :
      ((wd (copies x d) + wd (copies y d) : ℕ) : ℝ) * p.D ≤ p.budget L i := by
    have hx : (wd x + wd y) * p.D * 2 ^ (p.gain * i) ≤ m := by
      apply le_trans _ ext
      gcongr
    rw [budget, le_div_iff₀ (by positivity), wd_copies, wd_copies, ← Nat.mul_add]
    have hm : m * 2 ^ h ≤ S := by
      unfold S
      exact Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_left _ (by decide : 0 < 32)).trans
        (Nat.le_mul_of_pos_right _ (by omega)))
    have he : d * (wd x + wd y) * p.D * 2 ^ (p.gain * i) ≤ S * 2 ^ t := calc
      _ = ((wd x + wd y) * p.D * 2 ^ (p.gain * i)) * 2 ^ h * 2 ^ t := by unfold d; ring
      _ ≤ _ := Nat.mul_le_mul_right _ ((Nat.mul_le_mul_right _ hx).trans hm)
    unfold L
    exact_mod_cast he
  have slack i (hi : i < j) :
      (p.overhead : ℝ) * p.width (2 ^ t) i * (p.overhead ^ i * P.seats : ℕ) ≤ p.budget L i * 2 ^ r := by
    have hh : p.overhead * p.width (2 ^ t) i * (p.overhead ^ i * P.seats) * 2 ^ (p.gain * i) ≤
        S * 2 ^ t * 2 ^ r := calc
      _ = (P.seats * 2 ^ t) * (p.overhead ^ (i + 1) * 2 ^ ((p.gain + p.growth) * i)) := by
        rw [width, add_mul, pow_add 2 (p.gain * i) (p.growth * i), pow_succ p.overhead]
        ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hseat) (limit i hi.le)
    rw [budget, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    unfold L
    exact_mod_cast hh
  have ht := p.iterate P (2 ^ t) j a r L start rfl hsize ok exposed slack
  have hb : (∑ i ∈ range j, p.bits (p.width (2 ^ t) i) (p.budget L i)) ≤
      j * (p.overhead * (2 + t + p.growth * j) * S) := by
    simpa using sum_le_sum (s := range j) (fun i hi => p.bits_le t i j S (mem_range.mp hi).le)
  rw [he, width_pow] at ht
  exact ht.mono hb (fun _ hq => ⟨hq.1, hq.2.trans (Nat.mul_le_mul_left _ hseat)⟩)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Design
end

/-!
# A uniform choice of stack and group sizes

The reserve exponent `M` affects the number of remaining blocks.
The exponent controlling the cost of one group is independent of `M`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter

variable {δ : ℝ} (p : Design δ)

/-- All size parameters here are exponents of two. -/
structure Levels (p : Design δ) (M : ℕ) where
  j : ℕ
  stack : ℕ
  height : ℕ

def Design.groupRate := p.overhead + (p.gain + p.growth)

namespace Levels

variable {p} {M : ℕ} (v : Levels p M)

def group := p.groupRate * (v.j + 1)
def remaining := M * v.height
def blocks := v.remaining + p.steps * v.j * v.group
def batch := 2 ^ v.stack * 2 ^ v.blocks
def finalWidth := 2 ^ (v.stack + p.growth * v.j)
def allocation (m : ℕ) := 32 * m * (v.stack + 1) * 2 ^ v.blocks
def finalBudget (m : ℕ) := (v.allocation m : ℝ) * 2 ^ v.stack / (2 : ℝ) ^ (p.gain * v.j)
def selector (m : ℕ) := v.j * (p.overhead * (2 + v.stack + p.growth * v.j) * v.allocation m)

theorem room : p.overhead ^ (v.j + 1) * 2 ^ ((p.gain + p.growth) * v.j) ≤ 2 ^ v.group := by
  unfold group Design.groupRate
  rw [add_mul p.overhead, pow_add 2, pow_mul 2 p.overhead]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.le_succ v.j)))

def Suits (n T₀ : ℕ) (a b ξ : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  0 < v.j ∧ 1 < h ∧ h ≤ (2 : ℝ) ^ v.height ∧ (2 : ℝ) ^ v.height ≤ 2 * h ∧
  h ^ b ≤ (2 : ℝ) ^ v.stack ∧ (2 : ℝ) ^ v.stack ≤ 2 * h ^ b ∧ T₀ ≤ 2 ^ v.stack ∧
  h ^ a ≤ (2 : ℝ) ^ (p.gain * v.j) ∧ (p.D : ℝ) * (2 : ℝ) ^ (p.gain * v.j) ≤ h ^ (2 * a) ∧
  (v.finalWidth : ℝ) ≤ (2 : ℝ) ^ (p.growth + 1) * h ^ (b + (1 + δ / 3) * a) ∧
  v.finalWidth ≤ (Nat.clog 2 n) ^ 4 ∧
  (2 : ℝ) ^ v.group ≤ (2 : ℝ) ^ (2 * p.groupRate) * h ^ (p.groupRate * a) ∧
  (v.batch : ℝ) ≤ (n : ℝ) ^ ξ

end Levels

theorem Design.levels (hδ : δ ≤ 1) (T₀ M : ℕ) {a b ξ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 < b) (hb' : b ≤ 1) (hξ : 0 < ξ) :
    ∀ᶠ n : ℕ in atTop, ∃ v : Levels p M, v.Suits n T₀ a b ξ := by
  have ht := Shaving.tendsto_height
  filter_upwards [Shaving.stage_parameters p.gain p.growth p.groupRate p.steps M
    p.gain_pos a b δ ξ ha ha' hb hb' p.ratio hξ, ht.eventually_gt_atTop 1,
    ((tendsto_rpow_atTop hb).comp ht).eventually_ge_atTop (T₀ : ℝ),
    ((tendsto_rpow_atTop ha).comp ht).eventually_ge_atTop ((p.D : ℝ) * (2 : ℝ) ^ p.gain),
    ht.eventually_ge_atTop ((2 : ℝ) ^ (p.growth + 1))] with n scales hh hlow hgain hmax
  let h : ℝ := Nat.clog 2 n
  have hpos : 0 < h := zero_lt_one.trans hh
  obtain ⟨j, t, l, hj, hl, hl', hw, hw', hg, hg', hq, hr, hd⟩ := scales
  let v : Levels p M := ⟨j, t, l⟩
  have hbig : (v.finalWidth : ℝ) ≤ (2 : ℝ) ^ (p.growth + 1) * h ^ (b + (1 + δ / 3) * a) := by
    calc
      _ = (2 : ℝ) ^ t * 2 ^ (p.growth * j) := by
        change ((2 ^ (t + p.growth * j) : ℕ) : ℝ) = _
        rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
      _ ≤ (2 * h ^ b) * ((2 : ℝ) ^ p.growth * h ^ ((1 + δ / 3) * a)) :=
        mul_le_mul hw' hq (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hpos, pow_succ]; ring
  refine ⟨v, hj, hh, hl, hl', hw, hw', ?_, hg, ?_, hbig, ?_, hr, ?_⟩
  · have : (T₀ : ℝ) ≤ (2 : ℝ) ^ t := hlow.trans hw
    exact_mod_cast this
  · calc
      _ ≤ (p.D : ℝ) * ((2 : ℝ) ^ p.gain * h ^ a) := mul_le_mul_of_nonneg_left hg' (by positivity)
      _ ≤ h ^ a * h ^ a := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hgain (by positivity)
      _ = _ := by rw [← Real.rpow_add hpos, two_mul]
  · have hbound : b + (1 + δ / 3) * a ≤ 3 := by nlinarith
    have hh' : (v.finalWidth : ℝ) ≤ h ^ 4 := calc
      _ ≤ _ := hbig
      _ ≤ h * h ^ (3 : ℝ) := mul_le_mul hmax (Real.rpow_le_rpow_of_exponent_le hh.le hbound)
        (by positivity) hpos.le
      _ = h ^ (4 : ℕ) := by norm_num; ring
    unfold h at hh'
    exact_mod_cast hh'
  · unfold Levels.batch Levels.blocks Levels.remaining Levels.group
    simp only [v, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    rw [show t + (M * l + p.steps * j * (p.groupRate * (j + 1))) =
        t + M * l + p.groupRate * (j + 1) * (p.steps * j) by ring]
    exact hd

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Budgets at the exit of a round -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing

/-- Fixed parameters after the number of beats has been chosen. -/
structure Plan where
  C : ℕ
  d : ℕ
  v : ℕ
  p : ℕ
  b : ℕ
  n : ℕ
  e : ℕ
  K : ℕ
  loss : ℝ

namespace Plan
variable (s : Plan)

def D := 2 ^ s.d
def c := s.C + 12
def A := 10000 * (s.C + 1)
def ρ : ℝ := (1 / 2) ^ (2 * s.v)
def full := s.D ^ (s.c * s.e)
def slots := s.D ^ (s.c + 15)
def w := Tether.width s.full s.slots s.slots
def M := s.D ^ (s.c + 2)
def floor : ℝ := 1 / ((s.M : ℝ) * (2 : ℝ) ^ s.p)
def seats := (1 + s.slots * 2 ^ (Nat.clog 2 s.slots + 1)) * (1 + 2 ^ (Nat.clog 2 s.w + 1)) * s.K * s.D ^ s.C
def cover := (s.A * (1 + s.d) ^ 2 + s.A + 1) * s.M

structure Fits : Prop where
  degree : s.c ≤ s.D
  overhead : s.K ≤ s.D
  unit : s.b ≤ s.D
  mass : 2 * (s.ρ * s.A * (1 + (s.d : ℝ)) ^ 2 + s.loss * ((s.A + 1) / Real.sqrt s.D)) +
    (1 + 2 * ((Detour.steps s.w : ℝ) + Nat.clog 2 s.slots)) * (s.A / Real.sqrt s.D) ≤ 1 / (2 : ℝ) ^ s.v
  squares : 3 * (1 + 4 * (Nat.clog 2 s.slots : ℝ)) * s.A + 9 ≤ (2 : ℝ) ^ s.p / (2 : ℝ) ^ s.v
  max : 3 * (1 + (s.A : ℝ) * s.D) ≤ (s.D : ℝ) * (2 : ℝ) ^ s.p / 2

theorem small : s.C ≤ s.c := Nat.le_add_right _ _
theorem two (hs : s.Fits) : 2 ≤ s.D := (show 2 ≤ s.c by unfold c; omega).trans hs.degree
theorem cost_le : (s.C : ℝ) * 10000 ≤ s.A := by simp [A]; linarith

/-- Round down to a multiple of the complete subdivision factor. -/
theorem units (hs : s.Fits) (hb : 0 < s.b) (T : ℕ) (ht : s.b * s.D ^ s.c ≤ T) :
    ∃ z : ℕ, 0 < z ∧ (s.b * z) * s.D ^ s.c ≤ T ∧ T ≤ z * s.M := by
  let n := s.b * s.D ^ s.c
  have hd := s.two hs
  have hn : 0 < n := by unfold n; positivity
  let z := T / n
  have hz : 0 < z := Nat.div_pos ht hn
  refine ⟨z, hz, ?_, ?_⟩
  · rw [mul_comm s.b, mul_assoc]
    exact Nat.div_mul_le_self _ _
  have hcap : 2 * n ≤ s.M := by
    unfold M n
    rw [pow_add, pow_two]
    calc
      _ = s.D ^ s.c * (2 * s.b) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul hd hs.unit)
  calc
    T ≤ z * n + n := (Nat.lt_div_mul_add hn).le
    _ ≤ z * (2 * n) := by have := Nat.le_mul_of_pos_left n hz; nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ hcap

theorem slots_cover (hs : s.Fits) (T z : ℕ) (hz : T ≤ z * s.M) :
    (s.D : ℝ) ^ 4 * T ≤ (s.slots : ℝ) * z := by
  have hd : 0 < s.D := by have := s.two hs; omega
  have bound : s.D ^ 4 * T ≤ s.slots * z := calc
    _ ≤ s.D ^ 4 * (z * s.M) := Nat.mul_le_mul_left _ hz
    _ = s.D ^ (s.c + 6) * z := by unfold M; rw [pow_add, pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hd (by omega))
  exact_mod_cast bound

theorem floor_le (T z : ℕ) (hz : T ≤ z * s.M) :
    s.floor * (2 ^ s.p * T : ℕ) ≤ z := by
  have hd : 0 < s.D := by unfold D; positivity
  have hm : (0 : ℝ) < s.M := by unfold M; positivity
  have ht : (T : ℝ) / s.M ≤ z := (div_le_iff₀ hm).mpr (by exact_mod_cast hz)
  refine le_trans ?_ ht
  unfold floor
  push_cast
  field_simp
  exact le_rfl

end Plan
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Splitting a concentrated term into core and frozen border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g u : ℕ}
  (Q : LocalTerm F x y h u) (hD : 2 ≤ D) (hu : 0 < u)

namespace LocalTerm

def fringe := Q.freeze.fringe (fun t => Q.charge t.val) (fun t => Q.cover t.val)
  (1 / (D : ℝ) ^ 4) (by positivity)
  (by exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))))

theorem divisible : Q.freeze.Divisible u := fun v w _ _ => Q.width v w

abbrev host := Q.frame.host hu Q.divisible (Q.fringe hD) rfl

theorem parallel (i : slots Q.freeze.x ⊕ slots Q.freeze.y) :
    u ≤ (Q.host hD hu).parallelBits i := Q.frame.host_parallel hu Q.divisible _ rfl Q.width i

end LocalTerm

namespace Concentrated
variable {Q hD hu} {C d : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  (hq : Concentrated P Q C d 10)
include hq

/-- Balance the count and the square sum at the scale `T √D`. -/
theorem frozen_mass (hD : 2 ≤ D) (hT : 0 < T) :
    (Q.fringe hD).Z ≤ (C : ℝ) * W / Real.sqrt D := by
  have hz : (Q.fringe hD).reserve = 0 := by simp [Fringe.reserve, LocalTerm.fringe, Freeze.fringe]
  rw [Fringe.Z, hz, add_zero]
  have hsq : (Real.sqrt D) ^ 2 = (D : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have each (i : Q.freeze.Fixed) :
      Q.charge i.val * Real.sqrt D * (2 * (T : ℝ)) ≤ (D : ℝ) * T * T + (Q.charge i.val) ^ 2 := by
    nlinarith only [sq_nonneg (Q.charge i.val - Real.sqrt D * (T : ℝ)),
      congrArg (fun x => x * (T : ℝ) ^ 2) hsq]
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => each i)
  simp only [← sum_mul, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hs
  rw [le_div_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ (show 0 < (2 : ℝ) * T by positivity)
  change (∑ i : Q.freeze.Fixed, Q.charge i.val) * Real.sqrt D * (2 * (T : ℝ)) ≤ _
  have hc := mul_le_mul_of_nonneg_right hq.frozenCount (Nat.cast_nonneg (α := ℝ) T)
  linarith [hq.frozenSquare]

theorem core_mass (hD : 2 ≤ D) (hu : 0 < u) :
    ((Q.host hD hu).X : ℝ) ≤ C * W * (1 + (d : ℝ)) ^ 2 := by
  let A := Q.host hD hu
  have size : Fintype.card Q.freeze.core.E = A.X := by
    change Fintype.card A.diagram.E = _
    simp [HostNet.X, Fintype.card_congr A.units.bits]
  have hb : A.X ≤ ∑ i, Q.freeze.core.arity i := by
    rw [Diagram.sum_arity, size]
    omega
  refine (Nat.cast_le.mpr hb).trans (le_trans ?_ hq.coreSum)
  rw [Nat.cast_sum]
  exact sum_le_sum fun i _ => Q.cover i.val

omit hq in
private theorem max_at {A B : Type} [Fintype A] (f : A → B) (hf : Function.Injective f)
    (x : A → ℝ) (n : ℝ) (hn : 0 ≤ n) (hx : ∀ i, x i ≤ n) (b : B) :
    push f x b ≤ n :=
  push_max f (fun _ => True) x n hn hx (fun _ h => (h trivial).elim) hf.injOn b

theorem bounded (hD : 2 ≤ D) (hu : 0 < u) (hC : C ≤ D) :
    (Q.host hD hu).Bounded C (D ^ C) ((T : ℝ) / D) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hd : (0 : ℝ) < D := by positivity
  refine ⟨hq.coreDegree, hq.fullDegree, fun v i => ?_⟩
  rw [show (Q.host hD hu).load v i = _ from Q.frame.host_load hu Q.divisible _ rfl (v, i)]
  have hcore : push (fun t : Q.freeze.Core => Q.frame.place t.val)
      (fun t => (Q.diagram.arity t.val : ℝ)) (v, i) ≤ (T : ℝ) / D ^ 2 := by
    apply max_at _ (Q.one.comp Subtype.val_injective) _ _ (by positivity)
    intro t
    apply (Q.cover _).trans
    refine (le_div_iff₀ (by positivity)).mpr (le_trans ?_ (hq.coreMax t))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by decide))
      ((Nat.cast_nonneg _).trans (Q.cover _))
  have hf : push (fun t : Q.freeze.Fixed => Q.frame.place t.val)
      (Q.fringe hD).charge (v, i) ≤ (D : ℝ) ^ 2 * T := by
    apply max_at _ (Q.one.comp Subtype.val_injective) _ _ (by positivity)
    intro t
    refine (hq.frozenMax t).trans ?_
    rw [pow_two]
    gcongr
  calc
    _ ≤ (T : ℝ) / D ^ 2 + 1 / (D : ℝ) ^ 4 * (D ^ 2 * T) :=
      add_le_add hcore (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 1 / (D : ℝ) ^ 4))
    _ = 2 * ((T : ℝ) / D) / D := by field_simp; ring
    _ ≤ (T : ℝ) / D := by
      rw [div_le_iff₀ hd, mul_comm 2]
      exact mul_le_mul_of_nonneg_left hD' (by positivity)

end Concentrated
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Turning a reduced core back into a charged board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

theorem Plan.restored {F V : Type} [Fintype V] {x y : Wire} {h z T : ℕ} {L : ℝ}
    {R : Fringe x y V} {G : HostNet F R h z} {s : Plan} (hs : s.Fits)
    (A : G.Restore s.full s.slots s.slots) (hL : 0 ≤ L)
    (bound : G.Bounded 3 s.full T)
    (hw : (G.X : ℝ) ≤ (s.ρ * s.A * (1 + (s.d : ℝ)) ^ 2 + s.loss * ((s.A + 1) / Real.sqrt s.D)) * L)
    (hf : R.Z ≤ s.A / Real.sqrt s.D * L)
    (hsq : (∑ i, R.charge i ^ 2) ≤ (s.A : ℝ) * L * T)
    (hmax : ∀ i, R.charge i ≤ (s.A : ℝ) * s.D * T) :
    (∑ p, A.charge p) ≤ L / (2 : ℝ) ^ s.v ∧
      (∑ p, A.charge p ^ 2) ≤ L / (2 : ℝ) ^ s.v * (2 ^ s.p * T : ℕ) ∧
      ∀ p, A.charge p ≤ (s.D : ℝ) * (2 ^ s.p * T : ℕ) / 2 := by
  have mass : (∑ p, A.charge p) ≤ L / (2 : ℝ) ^ s.v := calc
    _ ≤ _ := A.mass
    _ ≤ (2 * (s.ρ * s.A * (1 + (s.d : ℝ)) ^ 2 + s.loss * ((s.A + 1) / Real.sqrt s.D)) +
      (1 + 2 * ((Detour.steps s.w : ℝ) + Nat.clog 2 s.slots)) * (s.A / Real.sqrt s.D)) * L := by
        conv_rhs => rw [add_mul, mul_assoc 2, mul_assoc (1 + 2 * ((Detour.steps s.w : ℝ) + Nat.clog 2 s.slots))]
        exact add_le_add (mul_le_mul_of_nonneg_left hw (by norm_num))
          (mul_le_mul_of_nonneg_left hf (by positivity))
    _ ≤ _ := by simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hs.mass hL
  refine ⟨mass, ?_, ?_⟩
  · have hm : (∑ p, A.charge p) ≤ L := mass.trans (div_le_self hL (one_le_pow₀ (by norm_num)))
    calc
      _ ≤ _ := A.squares T (Nat.cast_nonneg _) bound
      _ ≤ 3 * (1 + 4 * (Nat.clog 2 s.slots : ℝ)) * (s.A * L * T) + 9 * T * L := by gcongr
      _ = (3 * (1 + 4 * (Nat.clog 2 s.slots : ℝ)) * s.A + 9) * (L * T) := by ring
      _ ≤ ((2 : ℝ) ^ s.p / (2 : ℝ) ^ s.v) * (L * T) := mul_le_mul_of_nonneg_right hs.squares (by positivity)
      _ = _ := by push_cast; ring
  · intro v
    calc
      _ ≤ _ := A.maximum T _ (Nat.cast_nonneg _) (by positivity) bound hmax v
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hs.max (Nat.cast_nonneg (α := ℝ) T)
        push_cast
        linarith

variable {F : Type} [Field F] {x y : Wire} {h a u z D : ℕ} (Q : LocalTerm F x y h u)

private abbrev recovered {hD : 2 ≤ D} {G : HostNet F (Q.fringe hD) a z}
    {N r : ℕ} (A : G.Restore N r r) : Board F x y a where
  V := A.Space
  diagram := A.graph Q.freeze.border rfl
  place := Prod.swap
  one := Prod.swap_injective
  adj := A.adj
  sym := Tether.adj_symm A.sw G.C G.cs
  edge e := ⟨(A.supported _ _ e).1.symm, (A.supported _ _ e).2⟩
  charge := A.charge
  cover := A.charge_covers Q.freeze.border rfl (fun t => Q.cover t.val)

variable {Q} {s : Plan} (hs : s.Fits) {L : ℝ} {T R g : ℕ}
  {P : Input F x y h s.D T R g (10000 * L)}
  (hq : Concentrated P Q s.C s.d 10)
include hq

omit [Field F] in
theorem Concentrated.raw (hL : 0 ≤ L) (hT : 0 < T) (hu : 0 < u) :
    (Q.fringe (s.two hs)).Z ≤ (s.A / Real.sqrt s.D) * L ∧
      ((Q.host (s.two hs) hu).X : ℝ) ≤ s.A * (1 + (s.d : ℝ)) ^ 2 * L := by
  have hc : (s.C : ℝ) * (10000 * L) ≤ s.A * L := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right s.cost_le hL
  constructor
  · refine (hq.frozen_mass _ hT).trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _)
  · refine (hq.core_mass _ hu).trans ?_
    rw [mul_right_comm (s.A : ℝ)]
    exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem Concentrated.recover (hL : 0 ≤ L) (hT : 0 < T) (hu : 0 < u) (hz : 0 < z)
    (hzu : z ≤ u) (hunit : T ≤ z * s.M) (hc : 0 ≤ s.loss)
    (G : HostNet F (Q.fringe (s.two hs)) a z)
    (same : (Q.host (s.two hs) hu).Preserves G)
    (sites : G.seats ≤ s.K * (Q.host (s.two hs) hu).seats)
    (bound : G.Bounded 3 s.full T)
    (width : (G.X : ℝ) ≤ s.ρ * (Q.host (s.two hs) hu).X +
      s.loss * ((Q.fringe (s.two hs)).Z + L / s.D)) :
    ∃ B : Board F x y a,
      B.diagram.eval = (Q.freeze.border.attach G.diagram).eval ∧
      B.Ready 4 s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
      B.seats ≤ s.seats * (Fintype.card P.V * 2 ^ h) := by
  have hd := s.two hs
  have hd' : (1 : ℝ) ≤ s.D := by exact_mod_cast (show 1 ≤ s.D by omega)
  have hcap : (s.D : ℝ) ^ 4 * T ≤ (s.slots : ℝ) * z := s.slots_cover hs T z hunit
  have lower (i : Q.freeze.Fixed) : (z : ℝ) ≤ (Q.fringe hd).charge i :=
    (Nat.cast_le.mpr hzu).trans (Q.floor _)
  have upper (i : Q.freeze.Fixed) : (Q.fringe hd).charge i ≤ (s.slots : ℝ) * z := calc
    _ ≤ (s.C : ℝ) * s.D * T := hq.frozenMax i
    _ ≤ (s.D : ℝ) ^ 2 * T := by
      rw [pow_two]
      gcongr
      exact s.small.trans hs.degree
    _ ≤ (s.D : ℝ) ^ 4 * T := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hd' (by decide)) (Nat.cast_nonneg _)
    _ ≤ _ := hcap
  have contact i : (z : ℝ) ≤ G.parallelBits i :=
    Nat.cast_le.mpr (hzu.trans ((Q.parallel hd hu i).trans (same.parallelBits _ i)))
  have allocated : (T : ℝ) ≤ (Q.fringe hd).scale * (s.slots * (z : ℝ)) := by
    change _ ≤ 1 / (s.D : ℝ) ^ 4 * _
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), mul_comm (T : ℝ)]
    exact hcap
  obtain ⟨A⟩ := G.restore s.full s.slots s.slots T z (Nat.cast_pos.mpr hz) bound allocated
    (fun i => ⟨lower i, upper i⟩) contact
  obtain ⟨hf, hx⟩ := hq.raw hs hL hT hu
  have slack : L / (s.D : ℝ) ≤ L / Real.sqrt s.D :=
    div_le_div_of_nonneg_left hL (by positivity) (Real.sqrt_le_self_iff.mpr (.inr hd'))
  have hw : (G.X : ℝ) ≤ (s.ρ * s.A * (1 + (s.d : ℝ)) ^ 2 + s.loss * ((s.A + 1) / Real.sqrt s.D)) * L := calc
    _ ≤ _ := width
    _ ≤ s.ρ * (s.A * (1 + (s.d : ℝ)) ^ 2 * L) + s.loss * (s.A / Real.sqrt s.D * L + L / Real.sqrt s.D) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (by unfold Plan.ρ; positivity))
        (mul_le_mul_of_nonneg_left (add_le_add hf slack) hc)
    _ = _ := by ring
  have hsq : (∑ i, (Q.fringe hd).charge i ^ 2) ≤ (s.A : ℝ) * L * T :=
    hq.frozenSquare.trans (mul_le_mul_of_nonneg_right (by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right s.cost_le hL) (Nat.cast_nonneg T))
  have hmax (i : Q.freeze.Fixed) : (Q.fringe hd).charge i ≤ (s.A : ℝ) * s.D * T := by
    refine (hq.frozenMax i).trans ?_
    gcongr
    unfold Plan.A
    omega
  obtain ⟨mass, square, mx⟩ := Plan.restored hs A hL bound hw hf hsq hmax
  refine ⟨recovered Q A, A.eval Q.freeze.border rfl, ⟨Tether.adj_degree _ _ bound.1, mass, square, ?_⟩, ?_⟩
  · intro v
    exact ⟨mx v, (A.floor z le_rfl contact lower v).imp_right ((s.floor_le T z hunit).trans ·)⟩
  · let N := (1 + s.slots * 2 ^ (Nat.clog 2 s.slots + 1)) * (1 + 2 ^ (Nat.clog 2 s.w + 1))
    have hb : G.seats ≤ s.K * s.D ^ s.C * (Fintype.card P.V * 2 ^ h) := calc
      _ ≤ s.K * (Fintype.card Q.V * 2 ^ h) := sites
      _ ≤ s.K * ((s.D ^ s.C * Fintype.card P.V) * 2 ^ h) := by gcongr; exact hq.cells
      _ = _ := by ring
    calc
      _ = N * G.seats := by
        change Fintype.card (Tether.Host G.V _ _ _) * 2 ^ a = _
        rw [Tether.size]
        unfold N Plan.w HostNet.seats
        ring
      _ ≤ N * (s.K * s.D ^ s.C * (Fintype.card P.V * 2 ^ h)) := Nat.mul_le_mul_left N hb
      _ = _ := by unfold N Plan.seats; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Reducing one term of the local expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a r u z : ℕ}
  {Q : LocalTerm F x y h u} {s : Plan} (hs : s.Fits)
  (p : Reduction F s.c 3 s.b s.n s.e s.K s.ρ s.loss)
  {L : ℝ} {T R g : ℕ} {P : Input F x y h s.D T R g (10000 * L)}
  (hq : Concentrated P Q s.C s.d 10)
include hs p hq

/-- Execute all beats, restore the frozen members and reattach their
tables in each summand. -/
theorem Concentrated.process (hL : 0 ≤ L) (hT : 0 < T) (hz : 0 < z)
    (hu : u = s.b * z) (hunit : u * s.D ^ s.c ≤ T) (hunit' : T ≤ z * s.M)
    (ha : a + s.n * r ≤ h) (hr : s.K ≤ 2 ^ r)
    (slack : (s.K * s.D ^ s.C : ℕ) * (T : ℝ) * (Fintype.card P.V * 2 ^ h : ℕ) ≤ L * (2 : ℝ) ^ r) :
    Expansion Q.diagram.eval (s.K * (s.cover * ⌈L / (T : ℝ)⌉₊))
      (fun B : Board F x y a => B.Ready 4 s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
        B.seats ≤ s.seats * (Fintype.card P.V * 2 ^ h)) := by
  have hd := s.two hs
  have hd' : (1 : ℝ) ≤ s.D := by exact_mod_cast (show 1 ≤ s.D by omega)
  have hd₀ : (0 : ℝ) < s.D := zero_lt_one.trans_le hd'
  have hzu : z ≤ u := by rw [hu]; exact Nat.le_mul_of_pos_left _ p.unit
  have hu₀ := hz.trans_le hzu
  have hc : 0 < s.c := by unfold Plan.c; omega
  have hdeg := Nat.le_self_pow hc.ne' s.D
  let G := Q.host hd hu₀
  let B := (T : ℝ) / s.D
  have hB : (u : ℝ) ≤ B := (le_div_iff₀ hd₀).mpr (by
    exact_mod_cast (Nat.mul_le_mul_left u hdeg).trans hunit)
  have hG : G.Bounded s.c (s.D ^ s.c) B :=
    (hq.bounded hd hu₀ (s.small.trans hs.degree)).mono s.small
      (Nat.pow_le_pow_right (by omega) s.small) le_rfl
  have hseat : G.seats ≤ s.D ^ s.C * (Fintype.card P.V * 2 ^ h) := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ hq.cells
  have hslack : (s.K : ℝ) * B * G.seats ≤ (L / s.D) * (2 : ℝ) ^ r := calc
    _ ≤ (s.K : ℝ) * B * (s.D ^ s.C * (Fintype.card P.V * 2 ^ h) : ℕ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hseat) (by unfold B; positivity)
    _ = ((s.K * s.D ^ s.C : ℕ) * (T : ℝ) * (Fintype.card P.V * 2 ^ h : ℕ)) / s.D := by
      unfold B; push_cast; ring
    _ ≤ _ := by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right slack hd₀.le
  have hcover : (G.X : ℝ) + ((Q.fringe hd).Z + L / s.D) ≤ (s.cover * ⌈L / (T : ℝ)⌉₊ : ℕ) * (z : ℝ) := by
    obtain ⟨hf, hx⟩ := hq.raw hs hL hT hu₀
    have hf' := hf.trans (mul_le_mul_of_nonneg_right
      (div_le_self (Nat.cast_nonneg s.A) (Real.one_le_sqrt.mpr hd')) hL)
    have hround : L ≤ (⌈L / (T : ℝ)⌉₊:ℝ) * (z * s.M) := calc
      _ ≤ (⌈L / (T : ℝ)⌉₊:ℝ) * T := (div_le_iff₀ (Nat.cast_pos.mpr hT)).mp (Nat.le_ceil _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hunit') (by positivity)
    have hh := mul_le_mul_of_nonneg_left hround (by positivity : (0 : ℝ) ≤ s.A * (1 + (s.d : ℝ)) ^ 2 + s.A + 1)
    have := div_le_self hL hd'
    unfold Plan.cover G
    push_cast
    linarith
  obtain ⟨I, _, Q', num, eval, ok⟩ := p.run G z r a (s.D ^ s.c) _ B (L / s.D) hz hu hB
    (hs.degree.trans hdeg) hG (by positivity) ha hr hslack hcover
  have hload : s.K * B ≤ (T : ℝ) := by
    unfold B
    rw [← mul_div_assoc, div_le_iff₀ hd₀, mul_comm]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs.overhead) (Nat.cast_nonneg _)
  have term (i : I) : ∃ Z : Board F x y a,
      Z.diagram.eval = (Q.freeze.border.attach (Q' i).diagram).eval ∧
      Z.Ready 4 s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
      Z.seats ≤ s.seats * (Fintype.card P.V * 2 ^ h) := by
    obtain ⟨same, size, hbd, wd, _⟩ := ok i
    refine hq.recover hs hL hT hu₀ hz hzu hunit' p.loss _ same size ?_ wd
    simpa only [Plan.full, pow_mul] using hbd.mono le_rfl le_rfl hload
  choose Z he hZ using term
  refine ⟨I, inferInstance, Z, fun _ => 1, num, fun x y => ?_, hZ⟩
  simp only [one_mul, he]
  exact (Q.freeze.border.attach_sum Q.freeze.core _ eval x y).trans (Q.freeze.reconstruct x y)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end
