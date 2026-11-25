import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Terminal
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.ContractRates
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Log
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare
import OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Price

/-! # Common majorants for the three scales of terminal work -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) (s : Plan)
  {F : Type} [Field F] {x y : Wire} (W : Prices F)

def bitPrice := 1000 + W.W + 2 * (v.span + s.d + s.p)
def recordPrice (E : ℕ) := v.bitPrice s W + 8 + v.box (E + E)
def hostPrice (n E : ℕ) := v.recordPrice s W E + 4 * Nat.clog 2 n + W.w + W.w ^ W.power
def endCap (E : ℕ) := 3 + 32 * s.D * v.finalWidth + 64 * v.recordPrice s W E

def endCost (n m E e J : ℕ) :=
  ⌊((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) *
      ((v.hostPrice s W n E : ℝ) ^ J / (2 : ℝ) ^ v.remaining + (v.recordPrice s W E : ℝ) ^ J) +
    ((e : ℝ) + 256 * s.D / s.floor * v.finalBudget m) * (v.bitPrice s W : ℝ) ^ J⌋₊

abbrev bill (m : ℕ) (Q : Layer F x y) :=
  Assembly.Terminal.Rates.Size.mk F Q.template.scheme W (v.capacity s m Q) (v.depth s) Q.volume Q.height

theorem prices (n E : ℕ) : 1000 ≤ v.bitPrice s W ∧ v.bitPrice s W ≤ v.recordPrice s W E ∧
    v.recordPrice s W E ≤ v.hostPrice s W n E := by
  unfold hostPrice recordPrice bitPrice
  have := Nat.zero_le (W.w ^ W.power)
  omega

namespace Current
variable {v s} {Q : Layer F x y} {n m E : ℕ} (h : v.Current s n m v.j E Q)
  (upper : Q.template.scheme.m ≤ 4 * Nat.clog 2 n)

local notation "B" => v.bitPrice s W
local notation "T" => v.recordPrice s W E
local notation "H" => v.hostPrice s W n E
local notation "bill₀" => v.bill s W m Q
local notation "Y" => (2 ^ Q.template.scheme.m)
local notation "Z" => (2 ^ (Q.template.scheme.m + Q.template.scheme.h))
local notation "X" => (v.capacity s m Q - 2 ^ Q.template.scheme.m + (wd x + wd y))
include h

theorem bill_bits : (bill₀).B ≤ B := by
  have hh := h.terminal_height
  change 1000 + W.W + Assembly.Terminal.height Q.template.scheme (v.depth s) + Q.height ≤ _
  unfold bitPrice
  omega

theorem bill_records : (bill₀).T ≤ T := by
  have hu := h.bill_bits W
  have hℓ := h.bits le_rfl
  change (bill₀).B + 2 ^ Q.template.scheme.d + Q.template.scheme.ℓ ≤ B + 8 + v.box (E + E)
  rw [h.degree]
  omega

include upper in
theorem bill_hosts : (bill₀).M ≤ H := by
  have ht := h.bill_records W
  change (bill₀).T + Q.template.scheme.m + W.w + W.w ^ W.power ≤ _
  unfold hostPrice
  omega

theorem bill_spans : (bill₀).spans ≤ Z * 32 := by
  change Y * 2 ^ (Q.template.scheme.h + Q.template.scheme.k + Q.template.scheme.e) ≤ _
  rw [h.ready.1, add_zero, pow_add, ← mul_assoc, ← pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h.ports)

theorem bill_volume : (bill₀).volume = 2 * Y + X := by
  change v.capacity s m Q + Q.volume = _
  have := h.volume
  have hh : Y ≤ v.capacity s m Q := Nat.le_add_right ..
  omega

theorem bill_arity : 2 ^ (Q.template.scheme.e + v.depth s) + 64 * (bill₀).T ≤ v.endCap s W E := by
  have hb := h.bill_records W
  have he := Nat.mul_le_mul_right (s.D * v.finalWidth) (show 2 ^ Q.template.scheme.e ≤ 32 from
    Nat.pow_le_pow_right (by decide) h.ports)
  rw [pow_add, v.depth_eq, endCap, mul_assoc]
  omega

include upper in
theorem readCost : 4 * Q.snapshot.port.width ≤ Y * (100 * H) + Z * (4 * T) + X * (8 * B) := by
  have hp := v.prices s W n E
  have hH : Q.template.scheme.m + 2 ≤ H := by
    unfold hostPrice
    have := Nat.zero_le (W.w ^ W.power)
    omega
  have hT : Q.template.scheme.ℓ + Q.template.count ≤ T := (h.bits le_rfl).trans (Nat.le_add_left ..)
  have hB : Q.height + 1 ≤ B := by have := h.height; unfold bitPrice; omega
  have hX : Q.volume ≤ Y + X := by have := h.volume; omega
  have hfmt : Q.template.format.width ≤ Y * (8 * H + 2 + 2 ^ Q.template.scheme.h * T) := by
    rw [Template.width, h.degree]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hH) 2)
      (Nat.mul_le_mul_left _ hT))
  calc
    4 * Q.snapshot.port.width ≤ 4 * (Y * (8 * H + 2 + 2 ^ Q.template.scheme.h * T) + B * (2 * (Y + X))) :=
      Nat.mul_le_mul_left _ (Q.width.trans (Nat.add_le_add hfmt (Nat.mul_le_mul hB (Nat.mul_le_mul_left _ hX))))
    _ = Y * (32 * H + 8 + 8 * B) + Z * (4 * T) + X * (8 * B) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr; omega

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Paying for the final evaluator from the common seat and charge budgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
open Assembly Contraction

private theorem absorb (x j : ℕ) (hx : 1000 ≤ x) : 100 * x + 32 * x ^ j ≤ x ^ (j + 2) := by
  have h := Nat.le_self_pow (show j + 1 ≠ 0 by omega) x
  have g : x ^ j ≤ x ^ (j + 1) := Nat.pow_le_pow_right (show 0 < x by omega) (Nat.le_succ j)
  calc
    _ ≤ x ^ (j + 1) * 132 := by omega
    _ ≤ x ^ (j + 1) * x := Nat.mul_le_mul_left _ (by omega)
    _ = _ := (pow_succ ..).symm

private theorem combine (Y Z X H T B j : ℕ) (hb : 1000 ≤ B) (ht : B ≤ T) (hh : T ≤ H) :
    (Y * (100 * H) + Z * (4 * T) + X * (8 * B)) + (Y * H ^ j + Z * 32 * T ^ j + (2 * Y + X) * B ^ j) ≤
    Y * H ^ (j + 2) + Z * T ^ (j + 2) + X * B ^ (j + 2) := by
  have hz := Nat.pow_le_pow_left (ht.trans hh) j
  have h₁ := absorb H j (hb.trans (ht.trans hh))
  have h₂ := absorb T j (hb.trans ht)
  have h₃ := absorb B j hb
  calc
    _ = Y * (100 * H + H ^ j + 2 * B ^ j) + Z * (4 * T + 32 * T ^ j) + X * (8 * B + B ^ j) := by ring
    _ ≤ _ := by gcongr <;> omega

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m E : ℕ}
  (h : v.Current s n m v.j E Q) (W : Prices F) (upper : Q.template.scheme.m ≤ 4 * Nat.clog 2 n)

local notation "B" => v.bitPrice s W
local notation "T" => v.recordPrice s W E
local notation "H" => v.hostPrice s W n E
local notation "bill₀" => v.bill s W m Q
local notation "Y" => (2 ^ Q.template.scheme.m)
local notation "Z" => (2 ^ (Q.template.scheme.m + Q.template.scheme.h))
local notation "X" => (v.capacity s m Q - 2 ^ Q.template.scheme.m + (wd x + wd y))
include h upper

private theorem terminal_bill (j : ℕ) :
    4 * Q.snapshot.port.width + (bill₀).bound j ≤ Y * H ^ (j + 2) + Z * T ^ (j + 2) + X * B ^ (j + 2) := by
  have ht := h.bill_records W
  have hb := h.bill_bits W
  have hm := h.bill_hosts W upper
  have hz := h.bill_spans W
  have hs : (bill₀).bound j ≤ Y * H ^ j + Z * 32 * T ^ j + (2 * Y + X) * B ^ j := by
    rw [Terminal.Rates.Size.bound, h.bill_volume W]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm j))
      (Nat.mul_le_mul hz (Nat.pow_le_pow_left ht j))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb j))
  obtain ⟨h₁, h₂, h₃⟩ := v.prices s W n E
  exact (Nat.add_le_add (h.readCost W upper) hs).trans (combine _ _ _ _ _ _ _ h₁ h₂ h₃)

theorem endCost_le (j : ℕ) :
    4 * Q.snapshot.port.width + (bill₀).bound j ≤ v.endCost s W n m E (wd x + wd y) (j + 2) := by
  refine (h.terminal_bill W upper j).trans (Nat.le_floor ?_)
  let N := p.overhead ^ v.j * v.allocation m
  have h₁ : (Y : ℝ) ≤ N / (2 : ℝ) ^ v.remaining := v.host_budget (h.terminal rfl).2.1.ge h.seats
  have h₂ : (Z : ℝ) ≤ N := by exact_mod_cast h.seats
  have h₃ : ((X : ℕ) : ℝ) ≤ ((wd x + wd y : ℕ) : ℝ) + 256 * s.D / s.floor * v.finalBudget m := by
    have hc := h.capacity_le
    have hu : Y ≤ v.capacity s m Q := Nat.le_add_right ..
    rw [Nat.cast_add, Nat.cast_sub hu, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  calc
    _ = (Y : ℝ) * (H : ℝ) ^ (j + 2) + (Z : ℝ) * (T : ℝ) ^ (j + 2) + ((X : ℕ) : ℝ) * (B : ℝ) ^ (j + 2) := by push_cast; rfl
    _ ≤ (N / (2 : ℝ) ^ v.remaining) * (H : ℝ) ^ (j + 2) + N * (T : ℝ) ^ (j + 2) +
        (((wd x + wd y : ℕ) : ℝ) + 256 * s.D / s.floor * v.finalBudget m) * (B : ℝ) ^ (j + 2) := by gcongr
    _ = _ := by unfold N; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end

/-!
# Paying for the terminal network

Long addresses are charged once per host. The short records are
charged once per block, and the bit price applies only to live
terminal volume and the original exterior.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Contraction

variable {δ : ℝ} {p : Design δ} {M n E B C J q T₀ R : ℕ}
    {a b ξ τ σ J₀ : ℝ} {F : Type} [Field F]

def terminalFactor (p : Design δ) (s : Plan) (q J : ℕ) (J₀ : ℝ) :=
  (1000 + 64 * (2 : ℝ) ^ (2 * p.groupRate * q) + 32 * s.D + 256 * s.D / s.floor) * (2048 * (J₀ + 1)) ^ (J + 1)

theorem terminalFactor_one (p : Design δ) (s : Plan) (q J : ℕ) (hJ : 0 ≤ J₀) :
    1 ≤ terminalFactor p s q J J₀ := by
  have hs : 0 ≤ 256 * (s.D : ℝ) / s.floor := by unfold Plan.floor; positivity
  unfold terminalFactor
  refine one_le_mul_of_one_le_of_one_le ?_ (one_le_pow₀ (by linarith))
  linarith [show 0 ≤ (2 : ℝ) ^ (2 * p.groupRate * q) by positivity, Nat.cast_nonneg (α:=ℝ) s.D]

theorem paid_finish (v : Levels p M) (s : Plan) (W : Prices F) (m e : ℕ)
    (ready : v.Suits n T₀ a b ξ) (fit : v.Fits n B C)
    (exponent : (E + E) * (J + 1) ≤ C)
    (hh : 2 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n))
    (hτ : 0 ≤ τ) (hτσ : ((J + 1 : ℕ) : ℝ) * τ ≤ σ)
    (hw : (W.W : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ τ)
    (wide : W.w + W.w ^ W.power ≤ (Nat.clog 2 n) ^ R)
    (reserve : (7 + max R 1) * (J + 1) ≤ M) (enough : C ≤ q * p.groupRate)
    (hq : (p.groupRate * q : ℕ) * a ≤ b) (hJ : 0 ≤ J₀)
    (logSpan : ((v.span + s.d + s.p + 1 : ℕ) : ℝ) ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2) :
    let h : ℝ := Nat.clog 2 n
    let K := terminalFactor p s q J J₀ * (Real.log h) ^ (2 * (J + 1)) * h ^ σ
    (v.endCap s W E : ℝ) ≤ K * (p.D * (v.finalWidth : ℝ)) ∧
      (v.endCost s W n m E (v.batch * e) J : ℝ) ≤ K * v.expense h m e q := by
  intro h K
  let Z := 2048 * (J₀ + 1) * (Real.log h) ^ 2 * h ^ τ
  let V := (2048 * (J₀ + 1)) ^ (J + 1) * (Real.log h) ^ (2 * (J + 1)) * h ^ σ
  let X : ℝ := v.box (E + E)
  let D := (2 : ℝ) ^ (2 * p.groupRate * q)
  let c : ℝ := 256 * s.D / s.floor
  have hc : 0 ≤ c := by unfold c Plan.floor; positivity
  have hd : 0 ≤ D := by unfold D; positivity
  have hK : K = (1000 + 64 * D + 32 * s.D + c) * V := by unfold K terminalFactor D c V; ring
  have hh' : 1 ≤ h := by linarith
  have hy : 1 ≤ h ^ τ := Real.one_le_rpow hh' hτ
  have hz₀ : 1 ≤ (J₀ + 1) * (Real.log h) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hl)
  have hz₁ : 1 ≤ Z := by
    unfold Z
    exact one_le_mul_of_one_le_of_one_le (by linarith only [hz₀]) hy
  have hv : Z ^ (J + 1) ≤ V := by
    unfold Z V
    rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by positivity), mul_comm τ]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh' hτσ) (by positivity)
  have hz : Z ^ J ≤ V := (pow_le_pow_right₀ hz₁ (Nat.le_succ J)).trans hv
  have large : Z ≤ V := by simpa using (pow_le_pow_right₀ hz₁ (Nat.le_add_left 1 J)).trans hv
  have vv := hz₁.trans large
  have small : V ≤ K := by
    rw [hK]
    exact le_mul_of_one_le_left (by linarith) (by linarith [Nat.cast_nonneg (α:=ℝ) s.D])
  have hp : 1 ≤ X := by unfold X box; push_cast; exact one_le_pow₀ (by norm_num)
  have budget : X ^ (J + 1) ≤ (v.box C : ℝ) := by
    unfold X
    rw [← Nat.cast_pow, ← box_mul]
    exact_mod_cast v.box_mono exponent
  have cap : X ≤ (v.box C : ℝ) := by
    simpa using (pow_le_pow_right₀ hp (Nat.le_add_left 1 J)).trans budget
  have hs : (v.box C : ℝ) ≤ (2 : ℝ) ^ (q * v.group) := by exact_mod_cast v.box_le_group_power enough
  have hX : X ^ J ≤ (2 : ℝ) ^ (q * v.group) := (pow_le_pow_right₀ hp (Nat.le_succ J)).trans (budget.trans hs)
  have bit : (v.bitPrice s W : ℝ) + 9 ≤ Z := by
    let U := (J₀ + 1) * (Real.log h) ^ 2
    have hi : ((v.span + s.d + s.p : ℕ) : ℝ) ≤ U := by
      refine (Nat.cast_le.mpr (Nat.le_succ _)).trans (logSpan.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hv : 1 ≤ U := hz₀
    have h₁ := le_mul_of_one_le_right (by linarith : 0 ≤ U) hy
    have h₂ := le_mul_of_one_le_left (by positivity : 0 ≤ h ^ τ) hv
    have he : Z = 2048 * (U * h ^ τ) := by unfold Z U; ring
    rw [he, bitPrice, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
    change (W.W : ℝ) ≤ h ^ τ at hw
    linarith only [hi, hv, hw, h₁, h₂]
  have recd : (v.recordPrice s W E : ℝ) ≤ Z * X := by
    rw [recordPrice, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat]
    change (v.bitPrice s W : ℝ) + 8 + X ≤ _
    nlinarith only [bit, mul_nonneg (sub_nonneg.mpr hz₁) (sub_nonneg.mpr hp)]
  have hlive : 1 ≤ (v.finalWidth : ℝ) := by unfold finalWidth; push_cast; exact one_le_pow₀ (by norm_num)
  constructor
  · have hD : 1 ≤ (p.D : ℝ) := by exact_mod_cast (show 1 ≤ p.D by have := p.large; omega)
    have hR : (v.recordPrice s W E : ℝ) ≤ V * (D * v.finalWidth) :=
      recd.trans (mul_le_mul large (cap.trans (hs.trans (ready.group_power_le_width hq))) (by linarith) (by linarith))
    calc
      _ = 3 + 32 * (s.D : ℝ) * v.finalWidth + 64 * v.recordPrice s W E := by unfold endCap; push_cast; rfl
      _ ≤ 3 * (V * v.finalWidth) + 32 * (s.D : ℝ) * (V * v.finalWidth) + 64 * (V * (D * v.finalWidth)) := by
        have h₁ := one_le_mul_of_one_le_of_one_le vv hlive
        have h₂ := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ v.finalWidth) vv
        gcongr; linarith
      _ = (3 + 64 * D + 32 * s.D) * V * v.finalWidth := by ring
      _ ≤ K * v.finalWidth := by
        rw [hK]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hc]) (by positivity))
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hD) (by linarith)
  · have hhost : (v.hostPrice s W n E : ℝ) ≤ Z * h ^ (7 + max R 1) := by
      let r := max R 1
      have hx : X ≤ h := cap.trans (Nat.cast_le.mpr fit.small)
      have hhR : h ≤ h ^ r := by simpa only [pow_one] using pow_le_pow_right₀ hh' (le_max_right R 1)
      have hu : (W.w : ℝ) + (W.w : ℝ) ^ W.power ≤ h ^ R := by unfold h; exact_mod_cast wide
      have hu' := hu.trans (pow_le_pow_right₀ hh' (le_max_left R 1))
      have ht : (v.recordPrice s W E : ℝ) ≤ Z * h ^ r :=
        recd.trans (mul_le_mul_of_nonneg_left (hx.trans hhR) (by linarith))
      have hp' := le_mul_of_one_le_left (by positivity : 0 ≤ h ^ r) hz₁
      have hwide : (6 : ℝ) ≤ h ^ 7 := le_trans (by norm_num : (6 : ℝ) ≤ 2 ^ 7)
        (pow_le_pow_left₀ (by norm_num) hh _)
      calc
        _ ≤ 6 * (Z * h ^ r) := by
          unfold hostPrice; push_cast
          change (v.recordPrice s W E : ℝ) + 4 * h + W.w + (W.w : ℝ) ^ W.power ≤ _
          linarith only [ht, hu', hhR, hp']
        _ ≤ h ^ 7 * (Z * h ^ r) := mul_le_mul_of_nonneg_right hwide (by positivity)
        _ = _ := by rw [pow_add]; ring
    have hosts : (v.hostPrice s W n E : ℝ) ^ J ≤ V * h ^ M := calc
      _ ≤ (Z * h ^ (7 + max R 1)) ^ J := pow_le_pow_left₀ (by positivity) hhost _
      _ ≤ _ := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul hz (pow_le_pow_right₀ hh' ((Nat.mul_le_mul_left _ (Nat.le_succ J)).trans reserve))
          (by positivity) (by positivity)
    have recs : (v.recordPrice s W E : ℝ) ^ J ≤ V * (2 : ℝ) ^ (q * v.group) :=
      (pow_le_pow_left₀ (by positivity) recd _).trans (by rw [mul_pow]; gcongr)
    have bits : (v.bitPrice s W : ℝ) ^ J ≤ V := (pow_le_pow_left₀ (by positivity) (by linarith only [bit]) J).trans hz
    have hfin : 0 ≤ v.finalBudget m := by unfold finalBudget; positivity
    have hcv : c * V ≤ K := by rw [hK]; gcongr; linarith [Nat.cast_nonneg (α:=ℝ) s.D]
    let N : ℝ := (p.overhead ^ v.j * v.allocation m : ℕ)
    let U : ℝ := (v.batch * e : ℕ)
    have hN : 0 ≤ N := Nat.cast_nonneg _
    have hU : 0 ≤ U := Nat.cast_nonneg _
    unfold endCost
    refine (Nat.floor_le (by positivity)).trans ?_
    calc
      _ ≤ N * ((V * h ^ M) / (2 : ℝ) ^ v.remaining + V * (2 : ℝ) ^ (q * v.group)) + (U + c * v.finalBudget m) * V := by gcongr
      _ = V * (N * ((2 : ℝ) ^ (q * v.group) + h ^ M / (2 : ℝ) ^ v.remaining) + U) + c * V * v.finalBudget m := by ring
      _ ≤ K * (N * ((2 : ℝ) ^ (q * v.group) + h ^ M / (2 : ℝ) ^ v.remaining) + U) + K * v.finalBudget m :=
        add_le_add (mul_le_mul_of_nonneg_right small (by positivity)) (mul_le_mul_of_nonneg_right hcv hfin)
      _ = _ := by unfold expense N U; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # An absolute bound for finishing any admissible terminal layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

theorem Current.finish : ∃ J : ℕ,
    ∀ {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
      {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m E B C : ℕ}
      (W : Prices F), v.Current s n m v.j E Q → v.Fits n B C → m ≤ n ^ 2 →
        s.d + s.p ≤ 2 ^ v.j → 16 * Nat.clog 2 n ≤ W.w →
        ∃ L : Finset (Table F), L.card ≤ 3 ∧
          Finishes F (v.endCap s W E) L Q.snapshot (v.endCost s W n m E (wd x + wd y) J) := by
  obtain ⟨J, run⟩ := Layer.terminal
  refine ⟨J + 2, ?_⟩
  intro δ p M v s F _ x y Q n m E B C W h fit hm hs hw
  let z := v.bill s W m Q
  obtain ⟨hm', _, hr⟩ := h.terminal_space fit hm hs hw
  have cap : 3 ≤ v.endCap s W E := by unfold endCap; omega
  have room : 2 ^ z.p * (z.w * (2 ^ z.S.m + 2 ^ z.S.m)) < 2 ^ W.w := by
    rw [max_comm] at hr
    exact hr
  have arity := (Terminal.arity_le z).trans (h.bill_arity W)
  let L := Terminal.labels z.S z.t z.w
  refine ⟨L, Terminal.labels_card .., ?_⟩
  obtain ⟨k, hk, done⟩ := run F x y Q W z.V z.t hm' room h.fits_terminal _ (↑L) cap arity Set.Subset.rfl
  exact ⟨k, hk.mono (h.endCost_le W ((Nat.le_add_right ..).trans (h.long fit le_rfl hm)) J), done⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Selecting the grouping of every state at an intermediate round -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m i E : ℕ}

theorem Suits.exterior {T₀ : ℕ} {a b ξ : ℝ} (hs : v.Suits n T₀ a b ξ) (hi : i ≤ v.j)
    (he : ((wd x + wd y : ℕ) : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a))) :
    ((wd (copies x v.batch) + wd (copies y v.batch) : ℕ) : ℝ) * p.D ≤ v.budget m i := by
  obtain ⟨_, hh, _, _, _, _, _, _, hsize, _⟩ := hs
  have hgain : (p.D : ℝ) * (2 : ℝ) ^ (p.gain * i) ≤ (Nat.clog 2 n : ℝ) ^ (2 * a) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hi))
      (by positivity)).trans hsize
  have hscale : ((wd x + wd y : ℕ) : ℝ) * (p.D * (2 : ℝ) ^ (p.gain * i)) ≤ m := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv] at he
    exact (mul_le_mul_of_nonneg_left hgain (by positivity)).trans ((le_div_iff₀ (by positivity)).mp he)
  rw [budget, Design.budget, le_div_iff₀ (by positivity), wd_copies, wd_copies, ← mul_add, Nat.cast_mul]
  calc
    _ = (v.batch : ℝ) * (((wd x + wd y : ℕ) : ℝ) * (p.D * (2 : ℝ) ^ (p.gain * i))) := by ring
    _ ≤ (v.batch : ℝ) * m := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ 256 * (m : ℝ) * v.batch * (v.stack + 1) := by
      rw [mul_comm (v.batch : ℝ)]
      exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num))
        (by positivity)).trans (le_mul_of_one_le_right (by positivity) (by simp))
    _ = _ := by rw [← budget_zero, budget, Design.budget, mul_zero, pow_zero, div_one]

theorem live (Q : Layer F x y) (he : 0 < wd x + wd y) (j : Q.State) : Nonempty (Q.board j).V := by
  have hp : Nonempty (slots x ⊕ slots y) := Fintype.card_pos_iff.mp (by simpa using he)
  obtain ⟨w⟩ := hp
  exact ⟨((Q.board j).place (Packing.portEnd (Q.board j).diagram w)).1⟩

namespace Current
variable (cur : v.Current s n m i E Q)
include cur

theorem group_le (hi : i < v.j) : v.group ≤ Q.template.scheme.h :=
  (Nat.le_mul_of_pos_left _ p.steps_pos).trans (cur.enough hi)

theorem binning (hi : i < v.j) {P b d : ℕ}
    (sc : SphereScale.Scales ((4 * 5) ^ 300) 10 s.D (v.width i) P b d) :
    Q.template.Binning (Q.template.scheme.h - v.group) s.D (v.width i) (d * b) s.floor := by
  have hg : 0 < v.group := lt_of_lt_of_le (by have := p.overhead_large; omega : 0 < p.overhead)
    v.overhead_le_group
  have ht := cur.group_le hi
  refine ⟨by omega, ?_, sc.Tpos, sc.Rpos, sc.smallR, by unfold Plan.floor Plan.M Plan.D; positivity⟩
  exact (lt_mul_of_one_lt_left (by positivity) (by decide)).trans_le sc.degree

def trials {a R : ℕ} (b : Q.template.Binning a s.D (v.width i) R s.floor)
    (ha : a + v.group = Q.template.scheme.h) (hd : s.D ≤ p.overhead) (hi : i ≤ v.j)
    (he : ((wd x + wd y : ℕ) : ℝ) * s.D ≤ v.budget m i) :
    ∀ j, b.Trial (Q.presents j) (v.budget m i) := by
  refine Q.trial b cur.ready cur.loopless ?_ he
  intro j
  have hc : Fintype.card (Q.board j).V ≤ 2 ^ Q.template.scheme.m := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (Q.presents j).host.injective
  have hs : (Q.board j).seats ≤ 2 ^ (Q.template.scheme.m + Q.template.scheme.h) := by
    rw [Board.seats, pow_add]
    exact Nat.mul_le_mul_right _ hc
  rw [show Q.template.scheme.h - a = v.group by omega]
  refine le_trans ?_ (cur.slack hi hd)
  rw [mul_assoc, mul_comm ((Q.board j).seats : ℝ)]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs) (by positivity)

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Domination of the grouping cost by the common phase scale -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

def groupPower : ℕ := 2 * Layer.masked_bound.choose + 1

namespace Current

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m i E a R : ℕ}

theorem group_size (cur : v.Current s n m i E Q)
    (bin : Q.template.Binning a s.D (v.width i) R s.floor) (price : Prices F)
    {B J K : ℕ} (ha : a + v.group = Q.template.scheme.h) (hm : bin.target.m ≤ price.w)
    (hk : groupPower ≤ K) :
    let u := v.groupPayload s B J Q.height
    bin.programArity (Q.height + 1) ≤ (BoundaryScale.short Q.template 1 u v.group price) ^ K ∧
      Q.maskedCost bin price ≤ BoundaryScale.cost (x := x) (y := y) Q.template 1 u v.group price K := by
  intro u
  let k := Layer.masked_bound.choose
  have hj : k ≤ K := by change 2 * k + 1 ≤ K at hk; omega
  have hd : Q.template.scheme.d ≤ 4 := by rw [cur.degree]; decide
  let t := Q.grouping bin price hd cur.ready.1
  let S := BoundaryScale.short Q.template 1 u v.group price
  let A := BoundaryScale.long Q.template 1 u v.group price
  let O := BoundaryScale.outer Q.template 1 u price
  have h₁ : t.short ≤ S := by
    change 1000000 + s.D + 2 ^ Template.Presents.Plan.depth s.D s.floor + Q.template.scheme.ℓ + Q.template.count+
      2 ^ Q.template.scheme.e + Q.template.scheme.h + 2 ^ (Q.template.scheme.h - a) + price.W + Q.height ≤ S
    rw [show Q.template.scheme.h - a = v.group by omega]
    unfold S BoundaryScale.short BoundaryScale.metadata BoundaryScale.base u groupPayload groupCoefficient
    omega
  have h₂ : t.bitBase ≤ O := by
    change 1000 + price.W + Q.height + Q.height ≤ O
    unfold O BoundaryScale.outer u groupPayload groupCoefficient
    have := Nat.two_pow_pos (Template.Presents.Plan.depth s.D s.floor)
    omega
  have hw := Nat.zero_le (price.w ^ price.power)
  have hl : 2 ≤ A := by change 2 ≤ 100 + price.w + price.w ^ price.power + S; omega
  have h₃ : t.long ≤ A ^ 2 := calc
    _ ≤ A + A := by
      have hh : Q.template.scheme.m ≤ price.w := (Nat.le_add_right ..).trans hm
      change t.short + Q.template.scheme.m + price.w + price.w ^ price.power ≤ A + A
      change _ ≤ (100 + price.w + price.w ^ price.power + S) + (100 + price.w + price.w ^ price.power + S)
      omega
    _ ≤ _ := by rw [← two_mul, pow_two]; exact Nat.mul_le_mul_right _ hl
  have hg : t.short ^ k ≤ S ^ K := (Nat.pow_le_pow_left h₁ k).trans
    (Nat.pow_le_pow_right ((lt_of_lt_of_le (by decide) t.short_two).trans_le h₁) hj)
  have he : t.bitBase ^ k ≤ O ^ K := (Nat.pow_le_pow_left h₂ k).trans
    (Nat.pow_le_pow_right ((lt_of_lt_of_le (by decide) t.bitBase_two).trans_le h₂) hj)
  have ht : t.long ^ k ≤ A ^ K :=
    ((Nat.pow_le_pow_left h₃ k).trans_eq (pow_mul ..).symm).trans
      (Nat.pow_le_pow_right (by omega) ((Nat.le_add_right _ _).trans hk))
  obtain ⟨w, c⟩ := Layer.masked_bound.choose_spec F x y _ _ _ _ _ Q bin price hd cur.ready.1 cur.volume
  exact ⟨w.trans hg, c.trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ ht)
    (Nat.mul_le_mul_left _ hg)) (Nat.mul_le_mul_left _ he))⟩

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Uniformly admitting the controlled sphere terms to contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {K F : Type} [Field K] [Field F] [Fintype F] [Algebra K F]
  {x y : Wire} {Q : Layer F x y} {n m i E B C a : ℕ}
  {char l b d z A J : ℕ} [ExpChar F char]
  (cur : v.Current s n m i E Q) (fit : v.Fits n B C)

include cur fit in
theorem publish (law : SphereScale.Controlled K s char l b A J)
    (sc : SphereScale.Scales ((4 * 5) ^ 300) 10 s.D (v.width i) (char ^ l) b d)
    (ready : SphereScale.Ready K 10 s.D ((4 * 5) ^ 300) (char ^ l) b d)
    (repr : A * (1 + v.width i) ^ A ≤ Fintype.card F) (field : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (unit : 0 < s.b) (hz : 0 < z) (small : (s.b * z) * s.D ^ s.c ≤ v.width i) (big : v.width i ≤ z * s.M)
    (bin : Q.template.Binning a s.D (v.width i) (d * b) s.floor)
    (trial : ∀ j, bin.Trial (Q.presents j) (v.budget m i)) (price : Contraction.Prices F)
    (ha : a + v.group = Q.template.scheme.h) (hi : i ≤ v.j) (hm : m ≤ n ^ 2)
    (he : 0 < wd x + wd y) (margin : J + s.d + s.p + 1 ≤ 2 ^ v.j) (hw : 16 * Nat.clog 2 n ≤ price.w) :
    ∃ (U : Template F) (labels : Finset (Table F)),
      v.Passage Q U (1 + J) ∧ v.FrameBound Q U Q.height (frameRate s J) ∧
        U.scheme.k = 0 ∧ U.scheme.d ≤ J ∧ labels.card ≤ J ∧
        Transforms F (SphereScale.fullArity bin.target Q.height (v.precision s B) J) (↑labels)
          (Q.masked bin trial (Layer.panelRadius s.D)) (Contraction.publication U s (v.width i) (v.budget m i) z Q.height)
          (SphereScale.fullCost bin.target price Q.height (v.precision s B) (wd x + wd y) J) := by
  have hl := (Nat.mul_le_mul_left (s.b * z) (Nat.pow_le_pow_right sc.Dpos s.small)).trans small
  have hr := big.trans (Nat.mul_le_mul_right s.M (Nat.le_mul_of_pos_left z unit))
  obtain ⟨U, labels, height, lo, up, hk, hd, hp, hw', few, run⟩ :=
    law F (v.width i) d (v.precision s B) z sc ready repr (width_precision hi) (fit.field field)
      (Nat.mul_pos unit hz) hl hr x y Q a s.floor (v.budget m i) bin trial price
      (Levels.live Q he) (by rw [cur.degree]; decide) (cur.binSpace fit bin hi hm margin hw)
  exact ⟨U, labels, Passage.fromBin bin ha height lo up, cur.fromBin fit bin (by omega) hp hw', hk, hd, few, run⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end

/-! Charge a controlled concentration step to the pre-grouping budget. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
open Assembly Contraction SphereScale

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m i E a R : ℕ}

/-- A quadratic change of base and a quadratic multiplicity loss. -/
private theorem grouped_pow {x y b c J K : ℕ} (hx : x ≤ y * b ^ 2) (hb : 2 ≤ b)
    (hc : c ≤ b ^ 2) (hk : 3 * J + 4 ≤ K) : x * c ^ J ≤ y * b ^ K := by
  calc
    _ ≤ (y * b ^ 2) * (b ^ 2) ^ J := Nat.mul_le_mul hx (Nat.pow_le_pow_left hc J)
    _ = y * b ^ (2 + 2 * J) := by rw [mul_assoc, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

theorem sphere_work (cur : v.Current s n m i E Q)
    (bin : Q.template.Binning a s.D (v.width i) R s.floor) (price : Prices F)
    {B J K : ℕ} (ha : a + v.group = Q.template.scheme.h) (hm : bin.target.m ≤ price.w)
    (hk : 3 * J + 4 ≤ K) :
    let u := v.groupPayload s B J Q.height
    fullArity bin.target Q.height (v.precision s B) J ≤
      (BoundaryScale.short Q.template 1 u v.group price) ^ K ∧
    fullCost bin.target price Q.height (v.precision s B) (wd x + wd y) J ≤
      BoundaryScale.cost (x := x) (y := y) Q.template 1 u v.group price K := by
  let u := v.groupPayload s B J Q.height
  let T := BoundaryScale.short Q.template 1 u v.group price
  let L := BoundaryScale.long Q.template 1 u v.group price
  let O := BoundaryScale.outer Q.template 1 u price
  let A := portBase bin.target price Q.height
  let S := rowBase bin.target price Q.height (v.precision s B)
  have hu : 1000 + 2 * Levels.binBits s + binFactor s + v.precision s B + Q.height + J ≤ u := by
    unfold u groupPayload groupCoefficient
    have := Nat.two_pow_pos (Template.Presents.Plan.depth s.D s.floor)
    omega
  have hT : 2 + 2 ^ v.group + Q.template.scheme.h + u + Q.template.scheme.ℓ + price.W ≤ T := by
    unfold T BoundaryScale.short BoundaryScale.metadata BoundaryScale.base
    have := Nat.two_pow_pos Q.template.scheme.e
    omega
  have hL : T + price.w + price.w ^ price.power ≤ L := by
    change _ ≤ 100 + price.w + price.w ^ price.power + T
    omega
  have h₂ := Nat.two_pow_pos v.group
  have hp := Nat.zero_le (price.w ^ price.power)
  have hbits := cur.binBits bin
  have he := (Nat.lt_two_pow_self (n := bin.target.e)).le.trans hbits
  have ht := bin.shape.2.1
  have hA : A ≤ O := by unfold A O portBase BoundaryScale.outer; omega
  have hs : A + 2 ^ bin.target.e + v.precision s B ≤ T := by unfold A portBase; omega
  have hlabel := cur.binLabel bin
  have hshort : S ≤ T ^ 2 := calc
    _ ≤ T + binFactor s * T := by
      have hx := hlabel.trans (Nat.mul_le_mul_left _ (show Q.template.scheme.ℓ + 1 ≤ T by omega))
      change A + 2 ^ bin.target.e + bin.target.ℓ + v.precision s B ≤ _
      omega
    _ = (1 + binFactor s) * T := by ring
    _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hlong : hostBase bin.target price Q.height (v.precision s B) ≤ L ^ 2 := calc
    _ ≤ 2 * L + binFactor s * L := by
      have hx := hlabel.trans (Nat.mul_le_mul_left _ (show Q.template.scheme.ℓ + 1 ≤ L by omega))
      change A + 2 ^ bin.target.e + bin.target.ℓ + v.precision s B + bin.target.m + price.w + price.w ^ price.power ≤ _
      omega
    _ = (2 + binFactor s) * L := by ring
    _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  constructor
  · calc
      _ ≤ J * S := by
        unfold fullArity S rowBase portBase
        apply Nat.mul_le_mul_left
        have := Nat.two_pow_pos bin.target.e
        omega
      _ ≤ T * T ^ 2 := Nat.mul_le_mul (by omega) hshort
      _ = T ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < T) (by omega)
  · have hosts : 2 ^ bin.target.m ≤ 2 ^ Q.template.scheme.m * L ^ 2 := by
      rw [bin.shape.1, show Q.template.scheme.h - a = v.group by omega, pow_add, pow_succ, pow_two]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have seats : 2 ^ (bin.target.m + bin.target.h) ≤ 2 ^ (Q.template.scheme.m + Q.template.scheme.h) * T ^ 2 := by
      rw [pow_add, bin.capacity, ← pow_add, mul_comm 2]
      exact Nat.mul_le_mul_left _ ((show 2 ≤ T by omega).trans (Nat.le_self_pow (by decide) T))
    have ho : 0 < O := by unfold O BoundaryScale.outer; omega
    exact Nat.add_le_add
      (Nat.add_le_add (grouped_pow hosts (by omega : 2 ≤ L) hlong hk)
        (grouped_pow seats (by omega : 2 ≤ T) hshort hk))
      (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hA J).trans (Nat.pow_le_pow_right ho (by omega))))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end

/-! # A complete encoded round, with a uniform budget -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
open Assembly Contraction
open scoped Classical

variable {F K k : Type} [Field F] [Fintype F] [Field K] [Algebra K F] [Field k] [Algebra k F]
  {x y : Wire} {δ : ℝ} {p : Design δ} {M n m i E B C J G H q T₀ R z : ℕ}
  {v : Levels p M} {s : Plan} {Q : Layer F (copies x v.batch) (copies y v.batch)}
  {price : Prices F} {a b ξ τ σ J₀ : ℝ}

def roundCostFactor (s : Plan) (B J G H : ℕ) (J₀ : ℝ) :=
  2 * (2 * ((groupCoefficient s J + B + 128 : ℕ) : ℝ) * (J₀ + 1)) ^ G +
    (2 * ((frameRate s J + 2 : ℕ) : ℝ) * (J₀ + 1)) ^ H

set_option maxHeartbeats 2000000 in
theorem paid_round (cur : v.Current s n m i E Q) (level : v.Suits n T₀ a b ξ) (fit : v.Fits n B C)
    {char l b₀ d A : ℕ} [ExpChar F char]
    (law : SphereScale.Controlled K s char l b₀ A J)
    (restart : Restarts k s J H)
    (ok : Admissible p s (1 + J) (frameRate s J) H E C)
    (sc : SphereScale.Scales ((4 * 5) ^ 300) 10 s.D (v.width i) (char ^ l) b₀ d)
    (ready : SphereScale.Ready K 10 s.D ((4 * 5) ^ 300) (char ^ l) b₀ d)
    (repr : A * (1 + v.width i) ^ A ≤ Fintype.card F) (field : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (hs : s.Fits) (unit : 0 < s.b) (overhead : 0 < s.K)
    (hz : 0 < z) (low : (s.b * z) * s.D ^ s.c ≤ v.width i) (high : v.width i ≤ z * s.M)
    (hD : p.D = s.D) (hOver : s.D ≤ p.overhead)
    (hi : i < v.j) (hm : n ≤ m) (hm' : m ≤ n ^ 2)
    (he₀ : 0 < wd x + wd y) (he : ((wd x + wd y : ℕ) : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a)))
    (margin₁ : J + s.d + s.p + 1 ≤ 2 ^ v.j)
    (margin₂ : groupCoefficient s J + s.d + s.p + 2 * E + 6 ≤ 2 ^ v.j)
    (margin₃ : frameRate s J + 2 * E + 1 ≤ 2 ^ v.j)
    (hG₁ : groupPower ≤ G) (hG₂ : 3 * J + 4 ≤ G) (hH : 0 < H)
    (exponent : (5 + 2 * E + p.groupRate + 6) * G ≤ C) (enough : C ≤ q * p.groupRate)
    (hq : (p.groupRate * q : ℕ) * a ≤ b) (hh : 2 ≤ (Nat.clog 2 n : ℝ))
    (hl : 1 ≤ Real.log (Nat.clog 2 n)) (hτ : 0 ≤ τ)
    (hGτσ : (G : ℝ) * τ ≤ σ) (hHτσ : (H : ℝ) * τ ≤ σ) (hσ : σ ≤ 1)
    (hw : (price.W : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ τ)
    (space : 16 * Nat.clog 2 n ≤ price.w)
    (wide : price.w + price.w ^ price.power ≤ (Nat.clog 2 n) ^ R)
    (reserveG : (7 + max R 1) * G ≤ M) (reserveH : (7 + max R 1) * H ≤ M)
    (hJ : 0 ≤ J₀)
    (span : ((v.span + s.d + s.p + 1 : ℕ) : ℝ) ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2) :
    let h : ℝ := Nat.clog 2 n
    ∃ (P : Layer F (copies x v.batch) (copies y v.batch)) (L : Finset (Table F)) (u t : ℕ),
      v.Current s n m (i + 1) E P ∧ L.card ≤ (5 + J + 2 ^ H) * (Nat.clog 2 n) ^ 2 ∧
      (u : ℝ) ≤ (2 : ℝ) ^ (max G H + 2 * p.groupRate * q) * h ^ σ * (p.D * (v.finalWidth : ℝ)) ∧
      (t : ℝ) ≤ roundCostFactor s B J G H J₀ * (Real.log h) ^ (2 * max G H) * h ^ σ * v.expense h m (wd x + wd y) q ∧
      Transforms F u L Q.snapshot P.snapshot t := by
  let t := Q.template.scheme.h - v.group
  let bin := cur.binning hi sc
  have ht : t + v.group = Q.template.scheme.h := Nat.sub_add_cancel (cur.group_le hi)
  have he₁ := level.exterior hi.le he
  rw [hD] at he₁
  let trial := cur.trials bin ht hOver hi.le he₁
  have he₂ : 0 < wd (copies x v.batch) + wd (copies y v.batch) := by
    rw [wd_copies, wd_copies, ← mul_add]
    exact Nat.mul_pos (by unfold Levels.batch; positivity) he₀
  have hzT : z ≤ v.width i :=
    ((Nat.le_mul_of_pos_left _ unit).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by have := s.two hs; omega) _))).trans low
  obtain ⟨D, L₁, pass, data, hk, hd, hL₁, sphere⟩ := cur.publish fit law sc ready repr field unit hz low high
    bin trial price ht hi.le hm' he₂ margin₁ space
  have field' : Nat.card F ≤ (Nat.clog 2 n) ^ B := by rw [Nat.card_eq_fintype_card]; exact field
  have rq := cur.requirements pass data ok fit hi margin₃ hs unit overhead hm hm' hz low high hd hk field' space
  obtain ⟨finish, next, finishFew, finishArity, finishCost⟩ := cur.paid_restart level fit pass data ok hi margin₃
    hH overhead hzT rq restart hh hl hτ hHτσ hσ hw wide reserveH enough hq hJ span
  have extSpace : Q.template.scheme.m + 5 * (Q.template.scheme.h - t) + Q.height + 4 ≤ price.w := by
    have h₁ := cur.long fit hi.le hm'
    have h₂ := fit.group
    have h₃ := Nat.lt_two_pow_self.le.trans h₂
    have h₄ : 4 * v.span ≤ Nat.clog 2 n := fit.four_span.trans fit.group
    have h₅ := margin₁.trans ((Nat.pow_le_pow_right (by decide) v.rounds_le_group).trans h₂)
    have h₆ := cur.height
    have h₇ : 2 ≤ Nat.clog 2 n := by exact_mod_cast hh
    omega
  have hp₀ : 1 ≤ Nat.clog 2 n := by
    exact_mod_cast (show (1 : ℝ) ≤ (Nat.clog 2 n : ℝ) by linarith)
  have baseAddr : 1 ≤ Q.template.scheme.m := hp₀.trans cur.address
  have masked := Q.masked_transfer bin trial price (Layer.panelRadius s.D)
    (by rw [cur.degree]; decide) baseAddr extSpace
  have newAddr : bin.target.m ≤ price.w :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (cur.binSpace fit bin hi.le hm' margin₁ space))
  have maskBound := cur.group_size bin price (B:=B) (J:=J) (K:=G) ht newAddr hG₁
  have waveBound := cur.sphere_work bin price (B:=B) (J:=J) (K:=G) ht newAddr hG₂
  obtain ⟨_, groupArity, groupCost⟩ := cur.paid_group level fit hi.le margin₂ (by omega : 0 < G) exponent
    hh hl hτ hGτσ hσ hw wide reserveG enough hq hJ span
  have h₀ := (Nat.cast_le.mpr maskBound.1).trans groupArity
  have h₁ := (Nat.cast_le.mpr waveBound.1).trans groupArity
  let keys := (bin.programKeys (Q.height + 1) ∪ L₁) ∪ finish.keys
  have net := (masked.comp_union sphere).comp_union finish.transfer
  refine ⟨finish.next, keys, _, _, next, ?_, ?_, ?_, net⟩
  · have hc₁ := Finset.card_union_le (bin.programKeys (Q.height + 1) ∪ L₁) finish.keys
    have hc₂ := Finset.card_union_le (bin.programKeys (Q.height + 1)) L₁
    have hc := hc₁.trans (Nat.add_le_add hc₂ le_rfl)
    refine hc.trans ((Nat.add_le_add (Nat.add_le_add (bin.few _) hL₁) finishFew).trans ?_)
    rw [add_mul]
    have hp₂ : 0 < (Nat.clog 2 n) ^ 2 := pow_pos (Nat.zero_lt_one.trans_le hp₀) _
    exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hp₂) le_rfl
  · have hₛ : (2 : ℝ) ^ (G + 2 * p.groupRate * q) ≤ (2 : ℝ) ^ (max G H + 2 * p.groupRate * q) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (Nat.le_max_left ..) _)
    have hᵣ : (2 : ℝ) ^ (H + 2 * p.groupRate * q) ≤ (2 : ℝ) ^ (max G H + 2 * p.groupRate * q) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (Nat.le_max_right ..) _)
    have hpow : 0 ≤ (Nat.clog 2 n : ℝ) ^ σ := by positivity
    have hwidth : 0 ≤ (p.D : ℝ) * (v.finalWidth : ℝ) := by positivity
    have g := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hₛ hpow) hwidth
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hᵣ hpow) hwidth
    rw [Nat.cast_max, Nat.cast_max]
    exact max_le (max_le (h₀.trans g) (h₁.trans g)) (finishArity.trans h)
  · let h : ℝ := Nat.clog 2 n
    let d₁ : ℝ := (2 * ((groupCoefficient s J + B + 128 : ℕ) : ℝ) * (J₀ + 1)) ^ G
    let d₂ : ℝ := (2 * ((frameRate s J + 2 : ℕ) : ℝ) * (J₀ + 1)) ^ H
    let U := h ^ σ * v.expense h m (wd x + wd y) q
    have hU : 0 ≤ U := by unfold U Levels.expense Levels.finalBudget; positivity
    have g₀ := (Nat.cast_le.mpr maskBound.2).trans groupCost
    have g₁ := (Nat.cast_le.mpr waveBound.2).trans groupCost
    have g₂ : (_ : ℝ) ≤ d₂ * (Real.log h) ^ (2 * H) * U := finishCost.trans_eq (by unfold U; ring)
    have hleG : (Real.log h) ^ (2 * G) ≤ (Real.log h) ^ (2 * max G H) :=
      pow_le_pow_right₀ hl (Nat.mul_le_mul_left _ (Nat.le_max_left ..))
    have hleH : (Real.log h) ^ (2 * H) ≤ (Real.log h) ^ (2 * max G H) :=
      pow_le_pow_right₀ hl (Nat.mul_le_mul_left _ (Nat.le_max_right ..))
    have cG : d₁ * (Real.log h) ^ (2 * G) * h ^ σ * v.expense h m (wd x + wd y) q ≤
        d₁ * (Real.log h) ^ (2 * max G H) * U := by
      calc
        _ = d₁ * (Real.log h) ^ (2 * G) * U := by unfold U; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hleG (by unfold d₁; positivity)) hU
    have cH : d₂ * (Real.log h) ^ (2 * H) * U ≤ d₂ * (Real.log h) ^ (2 * max G H) * U :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleH (by unfold d₂; positivity)) hU
    push_cast
    have sum : d₁ * (Real.log h) ^ (2 * max G H) * U + d₁ * (Real.log h) ^ (2 * max G H) * U+
        d₂ * (Real.log h) ^ (2 * max G H) * U =
        roundCostFactor s B J G H J₀ * (Real.log h) ^ (2 * max G H) * h ^ σ * v.expense h m (wd x + wd y) q := by
      unfold roundCostFactor d₁ d₂ U
      ring
    simpa only [Layer.maskedCost, Nat.cast_mul, Nat.cast_ofNat] using
      (add_le_add (add_le_add (g₀.trans cG) (g₁.trans cG)) (g₂.trans cH)).trans_eq sum

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end
