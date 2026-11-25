import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.StartBound
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoded
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.ResetRate

section
/-!
# Size allowance for a replicated transfer

After J halvings the internal budget contributes at the reduced rate.
Exterior bits are still charged once per copy.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

def allowance (C h J k M E : ℕ) : ℕ :=
  (C + 1) * (2 ^ (h - J) * k * M + 2 ^ h * k * E)

theorem allowance_value (C h J k M E : ℕ) (hj : J ≤ h) :
    (allowance C h J k M E : ℝ) =
      (C + 1) * (2 ^ h * k : ℕ) * ((1 / 2 : ℝ) ^ J * M + E) := by
  unfold allowance
  push_cast
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hj, one_div, inv_pow]
  ring

theorem allowance_small (C : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ h J k M E : ℕ, J ≤ h → E ≤ M →
      (M : ℝ) ≤ (2 ^ w : ℕ) ^ (21 / 20 : ℝ) → ((2 ^ h * k : ℕ) : ℝ) ≤ (2 ^ w : ℕ) ^ (1 / 20 : ℝ) →
      10 ^ 38 * allowance C h J k M E ≤ 2 ^ (5 * w / 4) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  filter_upwards [eventually_ge_atTop 20, ht.eventually_ge_atTop (10 ^ 38 * (C + 1) * 2)]
    with w hw hc h J k M E hj hE hM hk
  let N := (2 : ℝ) ^ w
  have hp : 0 < N := pow_pos (by norm_num) _
  change 10 ^ 38 * ((C : ℝ) + 1) * 2 ≤ N ^ (1 / 10 : ℝ) at hc
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hM hk
  have hs : (1 / 2 : ℝ) ^ J * M + E ≤ 2 * M := by
    have he : (E : ℝ) ≤ M := Nat.cast_le.mpr hE
    have hu : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith [mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (α := ℝ) M)]
  have hf : (w : ℝ) * (6 / 5 : ℝ) ≤ (5 * w / 4 : ℕ) := by
    have he : 6 * w ≤ 5 * (5 * w / 4) := by omega
    have hr : 6 * (w : ℝ) ≤ 5 * (5 * w / 4 : ℕ) := by exact_mod_cast he
    linarith
  have hb : (10 : ℝ) ^ 38 * allowance C h J k M E ≤ (2 : ℝ) ^ (5 * w / 4) := calc
    _ ≤ 10 ^ 38 * (((C : ℝ) + 1) * (2 ^ h * k : ℕ) * (2 * M)) := by rw [allowance_value _ _ _ _ _ _ hj]; gcongr
    _ = (10 ^ 38 * ((C : ℝ) + 1) * 2) * (2 ^ h * k : ℕ) * M := by ring
    _ ≤ N ^ (1 / 10 : ℝ) * N ^ (1 / 20 : ℝ) * N ^ (21 / 20 : ℝ) := by gcongr
    _ = N ^ (6 / 5 : ℝ) := by rw [← Real.rpow_add hp, ← Real.rpow_add hp]; norm_num
    _ = (2 : ℝ) ^ ((w : ℝ) * (6 / 5 : ℝ)) := (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hf
  exact_mod_cast hb

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # A polynomial bound for the short control fields -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

theorem Limits.polynomial (L : Limits) (ha : 100 ≤ L.A) (hk : 1 ≤ L.K)
    (hs : L.steps ≤ L.A) (ht : L.start.tag ≤ L.A) :
    1 + L.code + (1 + L.steps) * L.small ^ L.K ≤ L.A ^ ((L.K + 3) ^ 5) := by
  let X := L.A ^ ((L.K + 3) ^ 2)
  have ha' : 0 < L.A := by omega
  have hAX : L.A ≤ X := by
    simpa using Nat.pow_le_pow_right ha' (show 1 ≤ (L.K + 3) ^ 2 by nlinarith)
  have hx : 100 ≤ X := ha.trans hAX
  have mono {i j : ℕ} (he : i ≤ j) : X ^ i ≤ X ^ j := Nat.pow_le_pow_right (by omega) he
  have hpow : L.A ^ L.K ≤ X := Nat.pow_le_pow_right ha' (by nlinarith)
  have he : L.extra ≤ X := calc
    _ ≤ (L.A ^ (L.K + 1)) ^ L.K := Nat.pow_le_pow_left
      (by rw [pow_succ']; exact Nat.mul_le_mul_right _ (by omega)) _
    _ ≤ X := by rw [← pow_mul]; exact Nat.pow_le_pow_right ha' (by nlinarith)
  have htag : L.maxTag ≤ X ^ 3 := calc
    _ ≤ X + X * X := Nat.add_le_add (ht.trans hAX) (Nat.mul_le_mul (hs.trans hAX) he)
    _ ≤ X ^ 3 := by nlinarith [Nat.mul_le_mul_right (X ^ 2) hx]
  have hcode : L.code ≤ X ^ 5 := calc
    _ ≤ (1 + X ^ 3) * X := Nat.mul_le_mul (Nat.add_le_add_left htag 1) he
    _ ≤ (X ^ 3 + X ^ 3) * X := by gcongr; exact Nat.one_le_pow _ _ (by omega)
    _ = 2 * X ^ 4 := by ring
    _ ≤ X ^ 5 := by rw [show X ^ 5 = X * X ^ 4 by ring]; gcongr; omega
  have hsmall : L.small ≤ X ^ 6 := calc
    _ ≤ 4 * X + X ^ 5 + X ^ 3 := by unfold Limits.small; gcongr
    _ ≤ 6 * X ^ 5 := by
      have := mono (show 3 ≤ 5 by decide)
      have := mono (show 1 ≤ 5 by decide)
      simp only [pow_one] at this
      omega
    _ ≤ X ^ 6 := by rw [show X ^ 6 = X * X ^ 5 by ring]; gcongr; omega
  have hbig : L.small ^ L.K ≤ X ^ (6 * L.K) := by rw [pow_mul]; gcongr
  have hbig' : L.code ≤ X ^ (6 * L.K) := hcode.trans (mono (by omega))
  have hone := Nat.one_le_pow (6 * L.K) X (by omega)
  calc
    _ ≤ X ^ (6 * L.K) + X ^ (6 * L.K) + (1 + X) * X ^ (6 * L.K) := by
      have := hs.trans hAX
      gcongr
    _ = (3 + X) * X ^ (6 * L.K) := by ring
    _ ≤ X ^ 2 * X ^ (6 * L.K) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = L.A ^ ((L.K + 3) ^ 2 * (2 + 6 * L.K)) := by unfold X; rw [← pow_add, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right ha' (by ring_nf; omega)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Padding the initial set of hosts to a power of two -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack

theorem hostCount {w M : ℕ} (hw : 100 ≤ w)
    (hl : 2 ^ w ≤ M) (hu : (M : ℝ) ≤ (2 ^ w : ℕ) ^ (21 / 20 : ℝ)) :
    let m := max w (Nat.clog 2 (2 * M))
    m ≤ 3 * w / 2 ∧ 2 ^ m ≤ 4 * M := by
  have hw' : (w : ℝ) * (21 / 20 : ℝ) + 1 ≤ (3 * w / 2 : ℕ) := by
    have hb : 21 * w + 20 ≤ 20 * (3 * w / 2) := by omega
    have : 21 * (w : ℝ) + 20 ≤ 20 * (3 * w / 2 : ℕ) := by exact_mod_cast hb
    linarith
  have hb : 2 * M ≤ 2 ^ (3 * w / 2) := by
    have hb' : (2 : ℝ) * M ≤ (2 : ℝ) ^ (3 * w / 2) := calc
      _ ≤ 2 * ((2 : ℝ) ^ w) ^ (21 / 20 : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2))
      _ = (2 : ℝ) ^ ((w : ℝ) * (21 / 20 : ℝ) + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast_mul (by norm_num), mul_comm]
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hw'
    exact_mod_cast hb'
  let m := Nat.clog 2 (2 * M)
  have hlo : w < m := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by have := Nat.two_pow_pos w; omega)
  have hhi : m ≤ 3 * w / 2 := (Nat.clog_le_iff_le_pow (by decide)).mpr hb
  change max w m ≤ _ ∧ 2 ^ (max w m) ≤ _
  rw [max_eq_right hlo.le]
  refine ⟨hhi, ?_⟩
  have hh : 2 ^ (m - 1) < 2 * M := (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega : m - 1 < m)
  rw [show m = (m - 1) + 1 by omega, pow_succ]
  omega

theorem name_exists {x y : Wire} {M w : ℕ}
    (size : wd x + wd y ≤ M) (bound : Nat.clog 2 (2 * M) ≤ 3 * w / 2) :
    Nonempty (Outer x y ↪ (Fin (2 * w) → Bool)) := by
  classical
  apply Function.Embedding.nonempty_of_card_le
  simp only [Outer, Fintype.card_sum, card_slots, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact size.trans ((by omega : M ≤ 2 * M).trans
    ((Nat.le_pow_clog (by decide : 1 < 2) (2 * M)).trans
      (Nat.pow_le_pow_right (by decide) (by omega))))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

section
/-!
# Paying for the last transfer of control records

The cost per host of long addresses must have an exponent independent
of the reserve. This calculation keeps it separate from the short
record cost per occurrence until after regrouping.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup

theorem raised {a b J n : ℕ} (hn : n * a ≤ b) : (2 ^ (a * J) : ℕ) ^ n ≤ 2 ^ (b * J) := by
  rw [← pow_mul, show a * J * n = (n * a) * J by ring]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hn)

theorem capacities {M h m t R J k L : ℕ} (ht : t = k + R * J) (hh : t ≤ h)
    (hs : 2 ^ m ≤ M * 2 ^ (h - t) * L) :
    2 ^ (m + t) ≤ M * 2 ^ h * L ∧ 2 ^ (m + k) ≤ M * 2 ^ (h - R * J) * L := by
  have step (i : ℕ) : 2 ^ (m + i) ≤ M * 2 ^ (h - t + i) * L := by
    rw [pow_add, pow_add]
    calc
      _ ≤ (M * 2 ^ (h - t) * L) * 2 ^ i := Nat.mul_le_mul_right _ hs
      _ = _ := by ring
  constructor
  · simpa only [Nat.sub_add_cancel hh] using step t
  · simpa only [show h - t + k = h - R * J by omega] using step k

theorem expenses {M h m t R J k A L w n i f : ℕ}
    (hl : 1000000 ≤ L) (ha : L ≤ A) (ht : t = k + R * J) (hh : t ≤ h)
    (hs : 2 ^ m ≤ M * 2 ^ (h - t) * L)
    (hn : n ≤ M * 2 ^ h * A)
    (hi : i ≤ 100 * A ^ 3 * 2 ^ (m + t) + 100 * L * 2 ^ m * w)
    (hf : f ≤ 100 * A ^ 3 * 2 ^ (m + k + (t - k)) + 100 * L * 2 ^ (m + k) * w) :
    n + 1000 * (i + f) + f ≤ M * 2 ^ h * A ^ 5 + M * 2 ^ (h - R * J) * L ^ 3 * w := by
  obtain ⟨hb, hp⟩ := capacities ht hh hs
  have hp' := (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right m k)).trans hp
  rw [show m + k + (t - k) = m + t by omega] at hf
  let X := M * 2 ^ h
  let Y := M * 2 ^ (h - R * J)
  let B := 100 * A ^ 3 * (X * A) + 100 * L * (Y * L) * w
  have hb' : 2 ^ (m + t) ≤ X * A := hb.trans (Nat.mul_le_mul_left _ ha)
  have cost (s : ℕ) (h : s ≤ Y * L) : 100 * A ^ 3 * 2 ^ (m + t) + 100 * L * s * w ≤ B := by
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hb')
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h))
  have hi' := hi.trans (cost _ hp')
  have hf' := hf.trans (cost _ hp)
  have hA : A ≤ A ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < A by omega) (by decide : 1 ≤ 4)
  calc
    _ ≤ X * A ^ 4 + 2001 * B := by
      have hn' : n ≤ X * A ^ 4 := hn.trans (Nat.mul_le_mul_left _ hA)
      omega
    _ = X * A ^ 4 * 200101 + Y * L ^ 2 * 200100 * w := by unfold B; ring
    _ ≤ X * A ^ 4 * A + Y * L ^ 2 * L * w := by gcongr <;> omega
    _ = _ := by unfold X Y; ring

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
end

/-!
# Lengths of control records throughout a sequence of beats

The loop executes a linear number of phases. Keeping an additional
quadratic number of block bits in reserve absorbs all fixed powers of
the global address width. Those extra bits are removed at the end.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
open Filter
variable {F : Type} [Field F] (P : Recipe F) (K d : ℕ)

def lane := 20 + P.b + P.n * K + P.H + d
def label := 2 * lane P K d * (K + 3) ^ 5
def result (R : ℕ) := R + label P K d + 10 * lane P K d

theorem lane_min : 20 ≤ lane P K d := by unfold lane; omega
theorem lane_label : lane P K d ≤ label P K d := by
  unfold label
  exact (by omega : _ ≤ 2 * lane P K d).trans (Nat.le_mul_of_pos_right _ (by positivity))

theorem dyad {i j : ℕ} (h : i ≤ j) : (2 : ℕ) ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h

theorem mono (J : ℕ) {i j : ℕ} (h : i ≤ j) : (2 : ℕ) ^ (i * J) ≤ 2 ^ (j * J) :=
  dyad (Nat.mul_le_mul_right _ h)

theorem power (n k : ℕ) : k ^ n ≤ 2 ^ (k * n) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le _

private theorem quadratic (k : ℕ) : ∀ᶠ j : ℕ in atTop, k * j ^ 2 ≤ 2 ^ j := by
  filter_upwards [replication (κ := 1) zero_lt_one k] with j h
  have hh := h (2 ^ j) le_rfl
  rw [Real.rpow_one] at hh
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hh

/-- The bounds that only need to hold beyond a fixed beat count. -/
structure Large [Fintype F] (R B J : ℕ) : Prop where
  beats : 20 ≤ J
  spare : (2 * B + 3) * K ≤ J
  factors : 100 + Stack.length F + K + (P.n + label P K d + 2 * B) * J +
    P.n * J * K + (K + 1) * (P.blocks (R + J) J + 1) ≤ 2 ^ J

theorem large [Fintype F] (R B : ℕ) : ∀ᶠ J : ℕ in atTop, Large P K d R B J := by
  let c := 100 + Stack.length F + K + (P.n + label P K d + 2 * B) + P.n * K +
    (K + 1) * (R + 1 + P.n * (P.H + 5) + 1)
  filter_upwards [eventually_ge_atTop 20, eventually_ge_atTop ((2 * B + 3) * K), quadratic c] with j hj hr h
  refine ⟨hj, hr, le_trans ?_ h⟩
  have hj' : j ≤ j ^ 2 := by nlinarith
  have hj'' : 1 ≤ j ^ 2 := by omega
  have hblocks : P.blocks (R + j) j + 1 ≤ (R + 1 + P.n * (P.H + 5) + 1) * j ^ 2 := by
    unfold Recipe.blocks Recipe.group
    nlinarith only [Nat.mul_le_mul_left R hj', hj'']
  unfold c
  nlinarith only [Nat.mul_le_mul_left (K + 1) hblocks,
    Nat.mul_le_mul_left (100 + Stack.length F + K) hj'',
    Nat.mul_le_mul_left (P.n + label P K d + 2 * B + P.n * K) hj']

theorem growth {J : ℕ} (hj : 1 ≤ J) :
    6 * K ^ (P.n * J) * P.b ^ J ≤ 2 ^ (lane P K d * J) ∧
    4 * 2 ^ (P.n * J * K) ≤ 2 ^ (lane P K d * J) := by
  have hm : 3 + K * (P.n * J) + P.b * J ≤ lane P K d * J := by
    unfold lane
    nlinarith only [hj, Nat.zero_le (P.H * J), Nat.zero_le (d * J)]
  constructor
  · calc
      _ ≤ 2 ^ 3 * 2 ^ (K * (P.n * J)) * 2 ^ (P.b * J) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by decide) (power _ _)) (power _ _)
      _ ≤ _ := by rw [← pow_add, ← pow_add]; exact dyad hm
  · rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]
    exact dyad (by nlinarith only [hm, Nat.zero_le (P.b * J)])

theorem tolerance {J : ℕ} (hj : 1 ≤ J) (hH : 4 ^ (P.n * (K + 2) + K + 2) ≤ P.H) :
    (24 * K * K ^ (P.n * J) * 2 ^ (P.n * J * K) : ℕ) ≤ (1 / 2 : ℝ) ^ J * (2 : ℝ) ^ P.group J := by
  have hp : 2 * K * K ^ (P.n * J) * 2 ^ (P.n * J * K) ≤ P.H ^ J := calc
    _ ≤ 2 ^ 1 * 2 ^ K * 2 ^ (K * (P.n * J)) * 2 ^ (P.n * J * K) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n := K)).le) (power _ _))
    _ ≤ (4 ^ (P.n * (K + 2) + K + 2)) ^ J := by
      rw [← pow_add, ← pow_add, ← pow_add, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_mul]
      apply dyad
      nlinarith only [hj, Nat.mul_le_mul_left K hj, Nat.zero_le (P.n * J)]
    _ ≤ _ := Nat.pow_le_pow_left hH _
  refine le_trans ?_ (P.group_room J hj)
  have ht : 24 * K * K ^ (P.n * J) * 2 ^ (P.n * J * K) ≤ 12 * P.H ^ J := by
    simpa only [← mul_assoc, show 12 * 2 = 24 from rfl] using Nat.mul_le_mul_left 12 hp
  exact_mod_cast ht

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
end

/-! # Common limits for the elementary phases -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
variable {F : Type} [Field F] [Fintype F] {x y : Wire}

def cap (P : Recipe F) (K J M copies : ℕ) := 6 * K ^ (P.n * J) * M * copies

def limits (P : Recipe F) (K d J M w : ℕ) (S : Setup F x y) : Limits :=
  ⟨max w (Nat.clog 2 (2 * M)), P.n * J, w, P.group J, K, 2 ^ ((2 * lane P K d) * J),
    Stack.initialBudget S M, (1 / 2 : ℝ) ^ J * M * S.count⟩

structure Fit (P : Recipe F) (K d R B J M w : ℕ) (S : Setup F x y) : Prop where
  large : Large P K d R B J
  pos : 1 ≤ K
  room : 4 ^ (P.n * (K + 2) + K + 2) ≤ P.H
  gain : label P K d + 10 ≤ B
  height : S.h = P.blocks (R + J) J
  size : S.U = P.b ^ J * S.z
  zpos : 0 < S.z
  unit : S.U ≤ w
  degree : S.d = 2 ^ (lane P K d * J)
  names : S.e ≤ 3 * w
  capacity : S.cap = cap P K J M S.count
  discount : S.discount = P.group J
  trivalent : S.G.Trivalent
  diagram : Fintype.card S.G.V + wd x + wd y ≤ M
  hosts : max w (Nat.clog 2 (2 * M)) ≤ 3 * w / 2
  padding : 2 ^ (max w (Nat.clog 2 (2 * M))) ≤ 4 * M
  lower : 2 ^ (B * J) ≤ w
  upper : w ≤ 2 ^ (2 * B * J)

variable {P : Recipe F} {K d R B J M w : ℕ} {S : Setup F x y}
variable (h : Fit P K d R B J M w S)
local notation "Λ" => limits P K d J M w S
local notation "l" => lane P K d
local notation "g" => label P K d
include h

theorem Fit.factors : 100 + Stack.length F + K + (P.n * J + g * J + 2 * B * J) +
    P.n * J * K + (K * (S.h + 1) + (S.h + 1)) ≤ 2 ^ J := by
  simpa only [h.height, add_mul, one_mul] using h.large.factors

theorem Fit.unit_load : (Λ).start.load = 6 * P.b ^ J := by
  change 6 * (S.U / S.z) = _
  rw [h.size, Nat.mul_div_cancel _ h.zpos]

theorem Fit.lanes : 2 ^ J ≤ S.d ∧ S.d ≤ (Λ).A := by
  rw [h.degree]
  refine ⟨dyad (Nat.le_mul_of_pos_left _ (by have := lane_min P K d; omega)), ?_⟩
  exact mono _ (by omega)

theorem Fit.headroom : 4 * 2 ^ (g * J) ≤ w := calc
  _ = 2 ^ (2 + g * J) := by rw [pow_add]; rfl
  _ ≤ _ := (dyad (by
    have := Nat.mul_le_mul_right J h.gain
    rw [add_mul] at this
    have := h.large.beats
    omega)).trans h.lower

theorem Fit.poly : 1 + (Λ).code + (1 + (Λ).steps) * (Λ).small ^ K ≤ 2 ^ (g * J) := by
  have hh := h.factors
  have hb := h.lanes.1.trans h.lanes.2
  have hp := (Λ).polynomial (by omega) h.pos (by change P.n * J ≤ _; omega)
    (by change Stack.length F + 1 ≤ _; omega)
  exact hp.trans (Regroup.raised (by unfold label; exact le_of_eq (mul_comm ..)))

theorem Fit.address :
    (Λ).host + K * (S.h + 1) ≤ 2 * w ∧ K ≤ 2 ^ (Λ).r ∧ (Λ).steps * (Λ).r ≤ S.h := by
  have ht : P.n * J * P.group J ≤ S.h := by rw [h.height]; exact Nat.le_add_left ..
  have hJ : 2 ^ J ≤ 2 ^ (g * J) := dyad (Nat.le_mul_of_pos_left _
    ((lane_min P K d).trans (lane_label P K d) |>.trans' (by decide : 1 ≤ 20)))
  have hw := h.headroom
  have hh := h.factors
  have hhi := h.hosts
  have hK : 2 ^ J ≤ 2 ^ P.group J :=
    dyad (Nat.le_mul_of_pos_left _ (show 0 < P.H + 5 by omega))
  refine ⟨?_, (show K ≤ 2 ^ J by omega).trans hK, ht⟩
  change max w (Nat.clog 2 (2 * M)) + P.n * J * (P.group J + K) + K * (S.h + 1) ≤ 2 * w
  rw [mul_add]
  omega

theorem Fit.basic :
    100 + 2 ^ (Λ).r + S.h + Nat.clog 2 (1 + S.U) + 2 ^ S.discount +
      K ^ (P.n * J) * (Λ).start.load + S.d ≤ (Λ).A := by
  have hj := h.large.beats
  have hu : Nat.clog 2 (1 + S.U) ≤ 2 * B * J + 1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [pow_succ]
    have := h.unit.trans h.upper
    have := Nat.two_pow_pos (2 * B * J)
    omega
  have hr : 2 ^ P.group J ≤ S.d := by
    rw [h.degree]
    exact mono _ (by unfold lane; omega)
  have hb : K ^ (P.n * J)* (Λ).start.load ≤ S.d := by
    rw [h.unit_load, h.degree, ← mul_assoc, mul_comm _ 6]
    exact (growth P K d (by omega)).1
  have hh := h.factors
  have hd := h.lanes.1
  have hs : 5 * S.d ≤ (Λ).A := by
    change 5 * S.d ≤ 2 ^ ((2 * l) * J)
    rw [show 2 * l * J = l * J + l * J by ring, pow_add, ← h.degree]
    exact Nat.mul_le_mul_right _ (by omega)
  change 100 + 2 ^ P.group J + _ + _ + _ + _ + _ ≤ _
  rw [h.discount]
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
end

/-!
# Uniform headroom through a batch

Reserve enough space for all incidence histories. Their discounted
mass costs at most one additional copy of the prescribed width error.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
variable {F : Type} [Field F] [Fintype F] {x y : Wire}
variable {P : Recipe F} {K d R B J M w : ℕ} {S : Setup F x y}
variable (h : Fit P K d R B J M w S)
local notation "Λ" => limits P K d J M w S
local notation "l" => lane P K d
local notation "g" => label P K d

include h

private theorem loss :
    ((24 * K * K ^ (P.n * J) * 2 ^ (P.n * J * K) * M * S.count : ℕ) : ℝ) ≤ (Λ).σ * (2 : ℝ) ^ P.group J := by
  have he := tolerance P K (J := J) (by have := h.large.beats; omega) h.room
  rw [Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ ((1 / 2 : ℝ) ^ J * (2 : ℝ) ^ P.group J) * M * S.count := by gcongr
    _ = _ := by unfold limits; dsimp only; ring

theorem Fit.exterior :
    S.fringe.Z ≤ (S.count : ℝ) * (wd x + wd y : ℕ) + (Λ).σ := by
  have hc : S.cap ≤ 24 * K * K ^ (P.n * J) * 2 ^ (P.n * J * K) * M * S.count := by
    rw [h.capacity]
    unfold cap
    have hk := h.pos
    have hK : 6 * K ^ (P.n * J) ≤ 24 * K * K ^ (P.n * J) := Nat.mul_le_mul_right _ (by omega)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hK.trans (Nat.le_mul_of_pos_right _ (by positivity))))
  have hr : S.fringe.reserve ≤ (Λ).σ := by
    change (S.cap : ℝ) / (2 : ℝ) ^ S.discount ≤ _
    rw [h.discount, div_le_iff₀ (by positivity)]
    exact (Nat.cast_le.mpr hc).trans (loss h)
  change (∑ _ : Stack.Outer S.input S.output, (1 : ℝ)) + _ ≤ _
  refine add_le_add ?_ hr
  simp [Stack.Outer, Setup.input, Setup.output, wd_copies, mul_add]

private theorem history :
    (K ^ (P.n * J) : ℕ) * ((Λ).start.mass + (Λ).start.width + (S.fringe.Z + (Λ).σ)) ≤ S.cap := by
  have he := h.exterior
  have hs : (Λ).σ ≤ (M : ℝ) * S.count := by
    have hb : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (Nat.cast_nonneg _) hb) (by positivity)
  have hm : wd x + wd y ≤ M := by have := h.diagram; omega
  have hE : (S.count : ℝ) * (wd x + wd y : ℕ) ≤ M * S.count := by rw [mul_comm]; gcongr
  have ht : (Λ).start.mass + (Λ).start.width + (S.fringe.Z + (Λ).σ) ≤ 6 * M * S.count := by
    change 0 + 3 * (M : ℝ) * S.count + _ ≤ _
    linarith only [he, hE, hs]
  rw [h.capacity]
  calc
    _ ≤ (K ^ (P.n * J) : ℕ) * (6 * (M : ℝ) * S.count) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by unfold cap; push_cast; ring

private theorem slack :
    ((K * (K ^ (P.n * J) * (Λ).start.load * S.z) * 2 ^ ((Λ).seats S.h) : ℕ) : ℝ) ≤ (Λ).σ * (2 : ℝ) ^ P.group J := by
  refine le_trans (Nat.cast_le.mpr ?_) (loss h)
  rw [h.unit_load]
  have hm : 2 ^ ((Λ).seats S.h) ≤ (4 * M) * 2 ^ S.h * 2 ^ (P.n * J * K) := by
    unfold Limits.seats
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h.padding)
  calc
    _ ≤ K * (K ^ (P.n * J) * (6 * P.b ^ J) * S.z) * ((4 * M) * 2 ^ S.h * 2 ^ (P.n * J * K)) := Nat.mul_le_mul_left _ hm
    _ = _ := by unfold Setup.count; rw [h.size]; ring

theorem Fit.enough : Enough S Λ := by
  obtain ⟨hh, hk, ht⟩ := h.address
  have hp := h.poly
  have he := h.headroom
  have hj := h.large.beats
  have hb := h.factors
  have hu := h.lanes.1.trans h.lanes.2
  refine ⟨h.trivalent, h.zpos, h.names, h.pos, ht, hk, le_max_left .., hh, h.basic, ?_, ?_, ?_,
    history h, slack h⟩
  · have hz : Nat.clog 2 (1 + (Λ).code) ≤ g * J :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
    have hx := Nat.pow_le_pow_right (show 0 < (Λ).A by omega) h.pos
    rw [pow_one] at hx
    exact hz.trans ((show g * J ≤ (Λ).A by omega).trans hx)
  · change (Λ).small ^ K ≤ w / 4
    have := Nat.le_mul_of_pos_left ((Λ).small ^ K) (show 0 < 1 + (Λ).steps by omega)
    omega
  · change 3 * (K ^ (P.n * J) * 1) ≤ S.d
    rw [h.degree, mul_one]
    refine le_trans ?_ (growth P K d (J := J) (by omega)).1
    have hb' := P.b_pos
    exact (Nat.mul_le_mul_right _ (by decide : 3 ≤ 6)).trans (Nat.le_mul_of_pos_right _ (by positivity))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
end

/-! # Uniform bounds on global computations and short labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
variable {F : Type} [Field F] [Fintype F] {x y : Wire}
variable {P : Recipe F} {K d R B J M w : ℕ} {S : Setup F x y}
variable (h : Fit P K d R B J M w S)
local notation "Λ" => limits P K d J M w S
local notation "l" => lane P K d
local notation "g" => label P K d
local notation "X" => (2 ^ (l * J) : ℕ)
local notation "Y" => (2 ^ (g * J) : ℕ)
local notation "T₀" => Stack.initialTemplate S w M
include h

theorem Fit.dominate : 10000 ≤ X ∧ 2 ^ J ≤ X ∧ X ≤ Y ∧ (Λ).A ^ K ≤ Y := by
  have hx : 2 ^ J ≤ X := h.lanes.1.trans_eq h.degree
  have hi := dyad h.large.beats
  refine ⟨(by omega), hx, mono J (lane_label P K d), ?_⟩
  apply Regroup.raised
  unfold label
  rw [mul_comm K]
  gcongr
  exact (Nat.le_add_right _ _).trans (Nat.le_self_pow (by decide) _)

theorem Fit.terminalHeight : S.h = (Λ).steps * (Λ).r + (J ^ 2 + R * J) := by
  change S.h = P.n * J * P.group J + (J ^ 2 + R * J)
  rw [h.height, Recipe.blocks]
  ring

theorem Fit.reservePower : (100 + w + (Λ).small) ^ K ≤ 2 ^ (J ^ 2) ∧ w ≤ 2 ^ S.h := by
  obtain ⟨hx, hj, hxy, _⟩ := h.dominate
  have hw := h.headroom
  have hu := h.upper
  have hk := h.pos
  have hb : (Λ).small ≤ w := by
    have hsmall : (Λ).small ^ K ≤ w / 4 := h.enough.labels
    have hh := Nat.le_self_pow (by omega : K ≠ 0) (Λ).small
    omega
  have ht : 100 + w + (Λ).small ≤ 2 ^ (2 * B * J + 3) := by rw [pow_add]; omega
  have ha : (100 + w + (Λ).small) ^ K ≤ 2 ^ (J ^ 2) := calc
    _ ≤ (2 ^ (2 * B * J + 3)) ^ K := Nat.pow_le_pow_left ht _
    _ ≤ _ := by
      rw [← pow_mul]
      apply dyad
      have hJ := h.large.beats
      have hR := Nat.mul_le_mul_right J h.large.spare
      nlinarith only [hR, Nat.mul_le_mul_left K (show 1 ≤ J by omega)]
  refine ⟨ha, le_trans ?_ (ha.trans (dyad (by have := h.terminalHeight; omega)))⟩
  exact (by omega : w ≤ 100 + w + (Λ).small).trans (Nat.le_self_pow (by omega) _)

theorem Fit.hosts_bound : 2 ^ (Λ).host ≤ M * 2 ^ ((Λ).steps * (Λ).r) * X ∧
    2 ^ ((Λ).seats S.h) ≤ M * 2 ^ S.h * X := by
  have hj := h.large.beats
  have hs : 4 * 2 ^ ((Λ).steps * (Λ).K) ≤ X := (growth P K d (by omega)).2
  have hm (t : ℕ) : 2 ^ ((Λ).m + t + (Λ).steps * (Λ).K) ≤ M * 2 ^ t * X := calc
    _ = 2 ^ (Λ).m * 2 ^ t * 2 ^ ((Λ).steps * (Λ).K) := by rw [pow_add, pow_add]
    _ ≤ (4 * M) * 2 ^ t * 2 ^ ((Λ).steps * (Λ).K) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h.padding)
    _ = M * 2 ^ t * (4 * 2 ^ ((Λ).steps * (Λ).K)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hs
  exact ⟨by rw [Limits.host, mul_add, ← add_assoc]; exact hm _, hm _⟩

private theorem phases : (Λ).steps * (Λ).cost S.h ≤ M * 2 ^ S.h * (2 * X * Y) := by
  have hp := h.poly
  have hh : (Λ).steps * (Λ).small ^ K ≤ Y :=
    (Nat.mul_le_mul_right _ (Nat.le_add_left _ 1)).trans (by omega)
  have hi : (Λ).steps ≤ Y := by
    obtain ⟨_, hx, hy, _⟩ := h.dominate
    have := h.factors
    change P.n * J ≤ Y
    omega
  have ht : (Λ).host + J ^ 2 ≤ (Λ).seats S.h := by
    have := h.terminalHeight
    unfold Limits.host Limits.seats
    rw [mul_add]
    omega
  have hw : 2 ^ (Λ).host * (100 + w + (Λ).small) ^ K ≤ 2 ^ ((Λ).seats S.h) := calc
    _ ≤ 2 ^ (Λ).host * 2 ^ (J ^ 2) := Nat.mul_le_mul_left _ h.reservePower.1
    _ ≤ _ := by rw [← pow_add]; exact dyad ht
  have hs := h.hosts_bound.2
  change (Λ).steps * (2 ^ (Λ).host * (100 + w + (Λ).small) ^ K + 2 ^ ((Λ).seats S.h) * (Λ).small ^ K) ≤ _
  calc
    _ = (Λ).steps * (2 ^ (Λ).host * (100 + w + (Λ).small) ^ K) + 2 ^ ((Λ).seats S.h) * ((Λ).steps * (Λ).small ^ K) := by ring
    _ ≤ Y * (M * 2 ^ S.h * X) + (M * 2 ^ S.h * X) * Y := Nat.add_le_add (Nat.mul_le_mul hi (hw.trans hs)) (Nat.mul_le_mul hs hh)
    _ = _ := by ring

theorem Fit.cost : Snapshot.sweepCost S T₀ + (Λ).steps * (Λ).cost S.h + (S.format T₀).width ≤
    M * 2 ^ S.h * 2 ^ (result P K d R * J) := by
  obtain ⟨hx, hx', hy, _⟩ := h.dominate
  have hF := h.factors
  have hM := h.hosts
  have hw := h.headroom
  have hpre := Stack.start_bound (S := S) (w := w) (M := M)
    (by omega : 8 ≤ X) le_rfl (by omega) (by omega) h.names h.degree.le (by omega) (by omega)
  have hinit : Snapshot.sweepCost S T₀ + (S.format T₀).width ≤ M * 2 ^ S.h * (4800 * X ^ 3) := calc
    _ ≤ _ := hpre
    _ ≤ 600 * X ^ 3 * ((4 * M) * 2 ^ S.h) + 600 * X ^ 3 * (4 * M) * 2 ^ S.h := by
      have hm : 2 ^ (T₀).scheme.m ≤ 4 * M := h.padding
      have hd := h.reservePower.2
      have he : X ≤ X ^ 3 := Nat.le_self_pow (by decide) _
      rw [pow_add]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm))
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ he) hm) hd)
    _ = _ := by ring
  have hc : 4800 * X ^ 3 + 2 * X * Y ≤ X ^ 4 * Y := calc
    _ ≤ 4800 * X ^ 3 * Y + 2 * X ^ 3 * Y := Nat.add_le_add (Nat.le_mul_of_pos_right _ (by positivity))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)))
    _ = 4802 * (X ^ 3 * Y) := by ring
    _ ≤ X * (X ^ 3 * Y) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have hd : X ^ 4 * Y ≤ 2 ^ (result P K d R * J) := by
    rw [← pow_mul, ← pow_add, show l * J * 4 + g * J = (4 * l + g) * J by ring]
    exact mono _ (by unfold result; omega)
  rw [add_right_comm]
  exact (Nat.add_le_add hinit (phases h)).trans (by rw [← mul_add]; exact Nat.mul_le_mul_left _ (hc.trans hd))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
end

/-! # Finishing an iteration of framed phases -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
open Assembly

variable {F : Type} [Field F] {x y : Wire}
    {D : Dimensions} {G : Diagram F x y} {name : Stack.Outer x y ↪ (Fin D.e → Bool)}
    {cap discount k Δ : ℕ} {T : Template F}
    {P : Budget} {M C c e R J w a l : ℕ}

local notation "src" => D.setup G name cap discount
local notation "dst" => target T.scheme k
local notation "A" => (2 ^ (a * J) : ℕ)
local notation "L" => (2 ^ (l * J) : ℕ)

theorem transfer (hn : Nonempty G.V) (hj : 20 ≤ J) (hl : 1 ≤ l) (ha : l ≤ a)
    (hc : 3 * l ≤ c) (he : 5 * a ≤ e) (hr : R ≤ a) (hw : 1 ≤ w)
    (ht : T.scheme.h = k + R * J) (hh : T.scheme.h ≤ D.h)
    (hk : T.scheme.k = 0) (hm : T.scheme.m + k ≤ 3 * w) (hw' : D.e ≤ 3 * w)
    (hd : T.scheme.d ≤ l * J) (hd' : D.d ≤ L) (hh' : D.h ≤ A)
    (tag : T.scheme.ℓ ≤ A) (spans : 2 ^ T.scheme.e ≤ A) (cnt : T.count ≤ A)
    (hosts : 2 ^ T.scheme.m ≤ M * 2 ^ (D.h - T.scheme.h) * L)
    (reach : P.reach * D.q ≤ 2 ^ (R * J)) (load : P.load ≤ 2 ^ (c * J) * D.b)
    (width : P.width ≤ C * (D.copies : ℝ) * ((1 / 2 : ℝ) ^ J * M + (wd x + wd y : ℕ)))
    {X : Assembly.Snapshot.{1} F (src).input (src).output}
    {u n : ℕ} (labels : Finset (Table F)) (few : labels.card ≤ 2 ^ (w / 4))
    (small : ∀ v ∈ labels, Processor.arity v ≤ w / 4)
    (f : Transforms F u (Allowed F w ∪ (labels : Set (Table F))) X (frame src T D.z Δ P) n)
    (first : X.state) (code : X.port.obj) (enc : ∀ i j, X.encode first i j = code)
    (eq : X.eval first = MatrixExponent.power G.eval D.copies)
    (hcost : n + X.port.width ≤ M * 2 ^ D.h * A) :
    Nonempty (Transfer G D M C c e R J w) := by
  have hp {i j : ℕ} (h : i ≤ j) : (2 : ℕ) ^ (i * J) ≤ 2 ^ (j * J) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)
  have large : 1000000 ≤ L := calc
    _ ≤ 2 ^ 20 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (hj.trans (Nat.le_mul_of_pos_left _ hl))
  have ha' := hp ha
  have hf : (dst).h = R * J := by change T.scheme.h - k = _; omega
  have hs := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  obtain ⟨Y, V, hy, net, ok⟩ := terminal (name := name) (k := k) hn (by omega) hh
    (Ready (S := src) Δ P) (by change P.reach * D.q ≤ 2 ^ (dst).h; rwa [hf]) (fun _ r => r.tracks) (le_max_left 3 u)
    (Allowed F w ∪ (labels : Set (Table F)))
  have f' := (f.widen (le_max_right 3 u) Set.Subset.rfl).comp net
  refine ⟨⟨X, Y, _, _, labels, few, small, f', first, code, enc, eq, ?_, dst, ?_, ?_, ?_, ?_, _, ?_, V, ?_⟩⟩
  · have hpre := format_bound (S := src) (T := T) (by omega : 2 ≤ L) ha' hw hk
      (by omega : T.scheme.m ≤ 3 * w) hw' hs hd' hh' tag spans cnt
    have hpost := tape_bound (S := src) (N := dst) (by omega : 2 ≤ L) ha' hw hk
      hm hw' hs hd' hh' tag spans
    have bound := expenses large ha' ht hh hosts hcost hpre (hy.le.trans hpost)
    have hsmall := Nat.mul_le_mul_left (M * 2 ^ D.h) (raised (J := J) he)
    have hlong := Nat.mul_le_mul_right w (Nat.mul_le_mul_left (M * 2 ^ (D.h - R * J)) (raised (J := J) hc))
    exact (by omega : _ ≤ (n + X.port.width) + 1000 * (((src).format T).width + Y.port.width) + Y.port.width).trans
      (bound.trans (Nat.add_le_add hsmall hlong))
  · change 2 ^ (T.scheme.m + k) * 2 ^ (R * J) ≤ _
    rw [← pow_add, add_assoc, ← ht]
    exact (capacities ht hh hosts).1.trans (Nat.mul_le_mul_left _ (hp (by omega)))
  · rw [hf]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · exact hd.trans (Nat.mul_le_mul_right J (by omega))
  · exact tag.trans (hp (by omega))
  · calc
      _ ≤ 100 * A ^ 3 * 2 ^ (dst).h := meta_bound (S := src) (N := dst) (by omega) hk
        (hd'.trans ha') hh' tag spans
      _ ≤ A * A ^ 3 * A := by rw [hf]; exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (hp hr)
      _ = A ^ 5 := by ring
      _ ≤ _ := raised he
  · intro i p q
    obtain ⟨v, t, ready, hx, load', heval, hv⟩ := ok i p q
    refine ⟨t, ?_, ?_, heval, hv⟩
    · rw [hx]
      exact ready.width.trans width
    · apply load'
      intro v b
      refine (ready.bounded.2.2 v b).trans ?_
      exact_mod_cast Nat.mul_le_mul_right D.z load

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
end

/-! # Joining the initial sweep, the contraction sequence and the last transfer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
open Assembly
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire}
variable {P : Recipe F} {K d R B J M w C : ℕ} {S : Setup F x y}

private theorem width (h : Fit P K d R B J M w S) (hc : P.C ≤ C) :
    let L := limits P K d J M w S
    (1 / 2 : ℝ) ^ J * L.start.width + P.C * (S.fringe.Z + L.σ) ≤
      (3 + 2 * C : ℕ) * (S.count : ℝ) * ((1 / 2 : ℝ) ^ J * M + (wd x + wd y : ℕ)) := by
  let L := limits P K d J M w S
  have hz : 0 ≤ S.fringe.Z := add_nonneg (Finset.sum_nonneg (fun i _ => S.fringe.nonneg i)) S.fringe.reserve_nonneg
  have hσ : 0 ≤ L.σ := by change 0 ≤ (1 / 2 : ℝ) ^ J * M * S.count; positivity
  have hb : P.C * (S.fringe.Z + L.σ) ≤ C * ((S.count : ℝ) * (wd x + wd y : ℕ) + 2 * L.σ) :=
    mul_le_mul hc (by linarith only [h.exterior]) (by positivity) (by positivity)
  change (1 / 2 : ℝ) ^ J * (3 * (M : ℝ) * S.count) + P.C * (S.fringe.Z + L.σ) ≤ _
  refine (add_le_add_right hb _).trans ?_
  change _ + C * ((S.count : ℝ) * (wd x + wd y : ℕ) + 2 * ((1 / 2 : ℝ) ^ J * M * S.count)) ≤ _
  rw [show ((3 + 2 * C : ℕ) : ℝ) = 3 + 2 * C by norm_cast]
  nlinarith only [show 0 ≤ (3 + (C : ℝ)) * (S.count : ℝ) * (wd x + wd y : ℕ) by positivity]

variable {D : Dimensions} {G : Diagram F x y}
    {name : Stack.Outer x y ↪ (Fin D.e → Bool)} {budget discount : ℕ}

local notation "src" => D.setup G name budget discount
local notation "Λ" => limits P K d J M w src
local notation "T₀" => Stack.initialTemplate src w M
local notation "lanes" => lane P K d
local notation "g" => label P K d
local notation "gains" => result P K d R

theorem collected (h : Fit P K d R B J M w src) (hc : P.C ≤ C)
    (hn : Nonempty G.V) (hq : 2 ^ (lanes * J) * D.q ≤ 2 ^ (R * J))
    (z : Completion src Λ (T₀).sweep (Stack.initialBudget src M)
      (src).U D.z 8 8 d 0 (P.n * J) ((1 / 2) ^ J) P.C) :
    Nonempty (Transfer G D M (3 + 2 * C) (3 * lanes) (5 * gains) R J w) := by
  have hj := h.large.beats
  have hl := lane_min P K d
  obtain ⟨hx, hx', hy, hy'⟩ := h.dominate
  have hf := h.factors
  have hw := h.headroom
  have hz : (src).z ∣ (src).U := dvd_mul_left _ _
  have hU : 0 < (src).U := Nat.mul_pos D.bpos D.zpos
  obtain ⟨X, i, b, hX, hi, hb, net⟩ := Stack.begin_frame src w M h.trivalent hn
    (by have := h.diagram; omega) hU hz (by rw [h.degree]; omega)
  let L := insert (Snapshot.sweepTable T₀) z.labels
  let allowed := Allowed F w ∪ (L : Set (Table F))
  let scale := max (3 + 2 * Stack.length F) z.scale
  have h₁ := net.widen (v := scale) (L' := allowed) (le_max_left ..)
    (Set.singleton_subset_iff.mpr (.inr (Finset.mem_insert_self ..)))
  have h₂ := z.transfer.widen (v := scale) (L' := allowed) (le_max_right ..)
    (Set.union_subset_union_right _ (Finset.subset_insert ..))
  have ht : Inside src Λ z.next z.budget D.z d (Λ).steps := by
    rw [show (Λ).steps = P.n * J from rfl]
    simpa only [zero_add] using z.inside
  have hh : z.next.scheme.h + (Λ).steps * (Λ).r = D.h := ht.height
  have hheight : D.h = (Λ).steps * (Λ).r + (J ^ 2 + R * J) := h.terminalHeight
  have hu : z.next.scheme.m ≤ (Λ).host := ht.upper
  have htop : (Λ).host + K * (D.h + 1) ≤ 2 * w := h.address.1
  have ha' : 2 ^ (g * J) ≤ 2 ^ (gains * J) := mono _ (by unfold result; omega)
  have hpoly := h.poly
  have hsize : D.h ≤ 2 ^ J := by
    have ht' : (src).h ≤ 2 ^ J := by omega
    exact ht'
  refine Regroup.transfer (k := J ^ 2) (l := lane P K d) (a := result P K d R)
    (name := name) (cap := budget) (discount := discount)
    hn hj (by omega) (by unfold result; omega) le_rfl le_rfl (by unfold result; omega)
    (by omega) (by omega) (by omega) ht.single (by omega) h.names ?_ h.degree.le
    (hsize.trans (hx'.trans (hy.trans ha'))) ?_ (ht.spans.trans (hy'.trans ha'))
    (ht.counters.trans (hy'.trans ha')) ?_ ?_ ?_ (z.width.trans (width h hc))
    L ?_ ?_ (h₁.comp h₂) i b hb hi ?_
  · have hd : d ≤ lanes := by unfold lane; omega
    exact ht.degree.trans (hd.trans (Nat.le_mul_of_pos_right _ (by omega)))
  · exact ht.bits.trans ((by omega : (Λ).code ≤ 2 ^ (g * J)).trans ha')
  · rw [show D.h - z.next.scheme.h = (Λ).steps * (Λ).r by omega]
    exact (dyad hu).trans h.hosts_bound.1
  · have ht' : z.budget.reach ≤ 2 ^ (lanes * J) :=
      (ht.origins.trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 3)).trans h.enough.origins)).trans_eq h.degree
    exact (Nat.mul_le_mul_right _ ht').trans hq
  · have hp : K ^ (P.n * J) * (Λ).start.load ≤ 2 ^ (lanes * J) := by
      rw [h.unit_load, ← mul_assoc, mul_comm _ 6]
      exact (growth P K d (by omega)).1
    exact (ht.load.trans hp).trans ((mono J (by omega)).trans (Nat.le_mul_of_pos_right _ D.bpos))
  · have sz := Finset.card_insert_le (Snapshot.sweepTable T₀) z.labels
    have hh' : z.labels.card ≤ (1 + (Λ).steps) * (Λ).small ^ K :=
      z.few.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ 1))
    have hl' : L.card ≤ w / 4 := by unfold L; omega
    exact hl'.trans (Nat.lt_two_pow_self (n := w / 4)).le
  · intro q hq'
    rcases Finset.mem_insert.mp hq' with rfl|hq'
    · change wd (word (Coloring.Format.addr (Stack.length F)).width) +
        wd (word (Coloring.Format.addr (Stack.length F)).width) ≤ w / 4
      rw [wd_word, Coloring.Format.width_addr]
      have he := dyad (show J + 1 ≤ lanes * J by nlinarith only [hj, hl])
      rw [pow_succ] at he
      omega
    · exact (z.small _ hq').trans h.enough.labels
  · rw [hX]
    refine le_trans ?_ h.cost
    exact Nat.add_le_add_right (Nat.add_le_add_left z.cost _) _

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Horizon
end

/-!
# Encoding the sequence of contractions

Choose the exponent for the number of lanes first. The reserve can
then be chosen arbitrarily large before setting the exponent charged
to short control records. A single sequence of circuits handles
every branch of the resulting weighted expansion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter Horizon

variable {F : Type} [Field F] [Fintype F]

private theorem complete {x y : Wire} {S : Setup F x y} {P : Recipe F}
    {K d R B J M w : ℕ} (h : Fit P K d R B J M w S) (hd : 3 ≤ d)
    (q : Sequence F K 8 8 d d (P.b ^ J) (P.n * J) ((1 / 2) ^ J) P.C) :
    Nonempty (Completion S (limits P K d J M w S) (Stack.initialTemplate S w M).sweep
      (Stack.initialBudget S M) S.U S.z 8 8 d 0 (P.n * J) ((1 / 2) ^ J) P.C) := by
  let L := limits P K d J M w S
  have hz : S.z ∣ S.U := by rw [h.size]; exact dvd_mul_left _ _
  have hl : Stack.length F + 1 ≤ L.A := by
    have := h.factors
    have hx : 2 ^ J ≤ L.A := h.lanes.1.trans h.lanes.2
    omega
  have ht := Stack.first_inside S L M d h.enough hd rfl rfl hz hl
  have hσ : 0 ≤ L.σ := by change 0 ≤ (1 / 2 : ℝ) ^ J * M * S.count; positivity
  exact q.run h.enough hσ ht (by rw [zero_add]; exact le_rfl) h.size h.zpos (dvd_refl _) (dvd_refl _) le_rfl

theorem encoded_of_rules (ht : ¬Tagged.Hard F) (hgroup : SubroundRule F) (hreset : ResetRule F) :
    Encoded F := by
  obtain ⟨P, K, d, hK, hd, hH, seq⟩ := sequence_recipe ht hgroup hreset
  obtain ⟨C, hC⟩ := exists_nat_gt P.C
  let l := lane P K d
  refine ⟨P, 3 + 2 * C, 3 * l, l, by omega, ?_⟩
  intro Q R V _ hR _
  refine ⟨5 * result P K d R, ?_⟩
  intro B hB
  have hg : label P K d + 10 ≤ B := by unfold result at hB; omega
  filter_upwards [large P K d R B] with J hJ
  intro w z T hQ hV hh hz hv hlo hhi hwidth _ x y G M hn htri hsize hM hM'
  let D := P.dimensions w J z (R + J) Q V (2 ^ (l * J)) T hQ hV hh hz hv
  have hj := hJ.beats
  have hw : 100 ≤ w := by
    have hb : J ≤ B * J := Nat.le_mul_of_pos_left _ (by omega)
    have := (dyad (hj.trans hb)).trans hlo
    omega
  obtain ⟨hm, hp⟩ := Stack.hostCount hw hM hM'
  obtain ⟨e⟩ := Stack.name_exists (x := x) (y := y)
    (by omega : wd x + wd y ≤ M) ((le_max_right _ _).trans hm)
  let S := D.setup G e (cap P K J M D.copies) (P.group J)
  have hu : S.U ≤ w := by
    change P.b ^ J * D.z ≤ w
    rw [Recipe.dimensions_z]
    refine le_trans ?_ hwidth
    rw [← mul_assoc 16, mul_assoc (16 * 2 ^ (Q * J))]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have h : Fit P K d R B J M w S :=
    ⟨hJ, hK, hH, hg, rfl, rfl, D.zpos, hu, rfl, by change 2 * w ≤ _; omega,
      rfl, rfl, htri, hsize, hm, hp, hlo, hhi⟩
  obtain ⟨t⟩ := complete h hd (seq J (by omega))
  have hr : 2 ^ (l * J) * D.q ≤ 2 ^ (R * J) := by
    change 2 ^ (l * J) * 2 ^ (Q * J) ≤ _
    rw [← pow_add, ← add_mul]
    exact mono J (by omega)
  exact collected h hC.le hn hr t

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
