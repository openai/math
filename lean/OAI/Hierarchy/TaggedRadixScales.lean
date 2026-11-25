import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace OAI
/-! # Integer heights of the two radix-packing grids -/

noncomputable section
namespace Hierarchy.Tagged.Radix

open Filter Real Asymptotics

def digitBits (a : ℝ) (h : ℕ) : ℕ := ⌊(h:ℝ)^(1/a)⌋₊
def packBits (B : ℝ) (h : ℕ) : ℕ := ⌈(B-1)*logb 2 (h:ℝ)⌉₊
def passBits (h : ℕ) : ℕ := ⌈logb 2 (h:ℝ)⌉₊ + 1

/-- Integer side conditions for the deterministic padding budget, and the two
factor-of-two rounding estimates used to price the calls. -/
structure GridScales (a B : ℝ) (h : ℕ) : Prop where
  positive : 1 ≤ h
  digit_lo : (h:ℝ)^(1/a)/2 ≤ (digitBits a h:ℝ)
  digit_hi : (digitBits a h:ℝ) ≤ (h:ℝ)^(1/a)
  digit_fraction : 8*digitBits a h ≤ h
  pack_lo : (h:ℝ)^(B-1) ≤ (2:ℝ)^(packBits B h)
  pack_hi : (2:ℝ)^(packBits B h) < 2*(h:ℝ)^(B-1)
  passes : h+1 ≤ 2^(passBits h)
  digit_room : passBits h + packBits B h + 3 ≤ digitBits a h
  last_room : passBits h + 2*digitBits a h + 2 ≤ h

private theorem tpow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : ℕ => (h:ℝ)^c) atTop atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop

theorem eventual_grid_scales {a B : ℝ} (ha : 1<a) (hB : 1<B) :
    ∀ᶠ h : ℕ in atTop, GridScales a B h := by
  have rpos : 0 < 1/a := one_div_pos.mpr (by linarith)
  have rlt : 1/a < 1 := (div_lt_one (show 0<a by linarith)).2 ha
  have small := (isLittleO_log_rpow_atTop rpos).const_mul_left (B/log 2)
  filter_upwards [eventually_ge_atTop (1:ℕ), (tpow rpos).eventually_ge_atTop 16,
    (tpow (sub_pos.mpr rlt)).eventually_ge_atTop 8,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (small.def (by norm_num : (0:ℝ)<1/2))]
    with h one grow extra logarithm
  have hp : 0 < (h:ℝ) := by exact_mod_cast (show 0<h from one)
  have hr : 1 ≤ (h:ℝ) := by exact_mod_cast one
  let x := (h:ℝ)^(1/a)
  let L := logb 2 (h:ℝ)
  have xpos : 0 < x := rpow_pos_of_pos hp _
  have logpos : 0 ≤ L := logb_nonneg (by norm_num) hr
  have logSmall : B*L ≤ x/2 := by
    have aux : |(B/log 2)*log (h:ℝ)| ≤ 1/2*x := by
      change ‖(B/log 2)*log (h:ℝ)‖ ≤ 1/2*‖x‖ at logarithm
      simpa only [Real.norm_eq_abs,abs_of_nonneg xpos.le] using logarithm
    calc
      _ = (B/log 2)*log (h:ℝ) := by dsimp [L,logb]; ring
      _ ≤ _ := (le_abs_self _).trans aux
      _ = _ := by ring
  have rootSmall : 8*x ≤ (h:ℝ) := by
    have fit := mul_le_mul_of_nonneg_left extra xpos.le
    change x*8 ≤ x*(h:ℝ)^(1-1/a) at fit
    dsimp [x] at fit ⊢
    rw [← rpow_add hp, show 1/a + (1-1/a) = 1 by ring, rpow_one] at fit
    linarith
  have qlo : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil _
  have qhi := Nat.ceil_lt_add_one logpos
  have jlo := Nat.le_ceil ((B-1)*L)
  have jhi := Nat.ceil_lt_add_one (mul_nonneg (sub_nonneg.mpr hB.le) logpos)
  have floorHi : (digitBits a h:ℝ) ≤ x := Nat.floor_le xpos.le
  have floorLo : x < (digitBits a h:ℝ)+1 := Nat.lt_floor_add_one x
  have room : passBits h + packBits B h + 3 ≤ digitBits a h := by
    apply Nat.le_floor
    change (((⌈L⌉₊+1)+⌈(B-1)*L⌉₊+3:ℕ):ℝ) ≤ x
    push_cast
    change 16 ≤ x at grow
    linarith only [qhi,jhi,logSmall,grow]
  have dyadic : (2:ℝ)^((B-1)*L) = (h:ℝ)^(B-1) := by
    rw [mul_comm (B-1),rpow_mul (by norm_num : (0:ℝ)≤2),rpow_logb (by norm_num) (by norm_num) hp]
  refine ⟨one,?_,floorHi,?_,?_,?_,?_,room,?_⟩
  · change x/2 ≤ _
    change 16 ≤ x at grow
    linarith
  · exact_mod_cast (show 8*(digitBits a h:ℝ) ≤ (h:ℝ) by linarith only [floorHi,rootSmall])
  · rw [← dyadic, ← rpow_natCast]
    exact rpow_le_rpow_of_exponent_le (by norm_num) jlo
  · rw [← dyadic, ← rpow_natCast (2:ℝ) (packBits B h)]
    calc
      _ < (2:ℝ)^((B-1)*L+1) := rpow_lt_rpow_of_exponent_lt (by norm_num) jhi
      _ = _ := by rw [rpow_add_one (by norm_num : (2:ℝ)≠0)]; ring
  · have reach : (h:ℝ) ≤ (2:ℝ)^⌈L⌉₊ := by
      rw [← rpow_natCast]
      exact (logb_le_iff_le_rpow (by norm_num) hp).mp qlo
    have hn : h ≤ 2^⌈L⌉₊ := by exact_mod_cast reach
    change h+1 ≤ 2^(⌈L⌉₊+1)
    rw [pow_succ]
    omega
  · have qr : (passBits h:ℝ) ≤ (digitBits a h:ℝ) := by
      exact_mod_cast (show passBits h ≤ digitBits a h by omega)
    have cap : (passBits h:ℝ)+2*(digitBits a h:ℝ)+2 ≤ (h:ℝ) := by
      change 16 ≤ x at grow
      linarith only [qr,floorHi,rootSmall,grow]
    exact_mod_cast cap

/-- The pack height loses at most a constant times the binary logarithm. -/
theorem GridScales.pack_shift {a B : ℝ} {h u : ℕ} (g : GridScales a B h)
    (hB : 1 < B) (height : h-packBits B h ≤ u) :
    (h:ℝ) ≤ (u:ℝ)+B*logb 2 (2*(h:ℝ)) := by
  have hr : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  have hp : 0 < (h:ℝ) := by linarith
  have logpos := logb_nonneg (by norm_num : (1:ℝ)<2) hr
  have shift := Nat.ceil_lt_add_one (mul_nonneg (sub_nonneg.mpr hB.le) logpos)
  change (packBits B h:ℝ) < (B-1)*logb 2 (h:ℝ)+1 at shift
  have span : (h:ℝ) ≤ (u:ℝ)+(packBits B h:ℝ) := by
    exact_mod_cast (show h ≤ u+packBits B h by omega)
  rw [logb_mul (by norm_num : (2:ℝ)≠0) hp.ne',logb_self_eq_one (by norm_num)]
  linarith only [shift,span,hB,logpos]

/-- Block and pack addressing preserve the row count exactly before padding. -/
theorem GridScales.batch_counts {a B : ℝ} {h : ℕ} (g : GridScales a B h) :
    2^(h-2*digitBits a h)*2^(2*digitBits a h) = (2:ℕ)^h ∧
    2^(h-packBits B h)*2^(packBits B h) = (2:ℕ)^h := by
  have digit := g.digit_room
  have last := g.last_room
  constructor
  · rw [← pow_add, Nat.sub_add_cancel (show 2*digitBits a h ≤ h by omega)]
  · rw [← pow_add, Nat.sub_add_cancel (show packBits B h ≤ h by omega)]

/-- The advertised block width covers a record of height-many bits. -/
theorem GridScales.block_width {a B : ℝ} {h t : ℕ} (g : GridScales a B h) (ha : 0<a)
    (height : 2*digitBits a h ≤ t) : h ≤ ⌈(t:ℝ)^a⌉₊ := by
  have hh := g.digit_lo
  have ht : 2*(digitBits a h:ℝ) ≤ (t:ℝ) := by exact_mod_cast height
  have le : (h:ℝ)^(1/a) ≤ (t:ℝ) := by linarith
  have p := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg h) _) le ha.le
  rw [← rpow_mul (Nat.cast_nonneg h), one_div_mul_cancel ha.ne', rpow_one] at p
  exact_mod_cast p.trans (Nat.le_ceil _)

/-- A packed wide record needs only a bounded number of payload slices at
the pack-call exponent, uniformly in the parent height. -/
theorem GridScales.pack_width {a B : ℝ} {h u : ℕ} (g : GridScales a B h) (hB : 1<B)
    (height : h-packBits B h ≤ u) :
    (h:ℝ)*(2:ℝ)^packBits B h ≤ (2*2^B)*(⌈(u:ℝ)^B⌉₊:ℝ) := by
  have hp : 0 < (h:ℝ) := by exact_mod_cast (show 0<h from g.positive)
  have digit := g.digit_room
  have last := g.last_room
  have hle : (h:ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast (show h ≤ 2*u by omega)
  have power := rpow_le_rpow hp.le hle (show 0≤B by linarith)
  rw [mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg u)] at power
  calc
    _ ≤ (h:ℝ)*(2*(h:ℝ)^(B-1)) := mul_le_mul_of_nonneg_left g.pack_hi.le hp.le
    _ = 2*(h:ℝ)^B := by rw [rpow_sub_one hp.ne']; field_simp
    _ ≤ 2*((2:ℝ)^B*(u:ℝ)^B) := by linarith only [power]
    _ ≤ _ := by
      have bound := mul_le_mul_of_nonneg_left (Nat.le_ceil ((u:ℝ)^B))
        (show 0 ≤ 2*(2:ℝ)^B by positivity)
      linarith only [bound]

/-- For any fixed amount of padding the block's rate exponent converts from
its own height to the parent height at exponent r/a. -/
theorem GridScales.block_rate {a B r : ℝ} {h t : ℕ} (g : GridScales a B h)
    (ha : 0<a) (hr : 0≤r) (d : ℕ) (height : t ≤ 2*digitBits a h+d) :
    (t:ℝ)^r ≤ (2+(d:ℝ))^r*(h:ℝ)^(r/a) := by
  have one : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  have root : 1 ≤ (h:ℝ)^(1/a) := one_le_rpow one (one_div_pos.mpr ha).le
  have upper : (t:ℝ) ≤ 2*(digitBits a h:ℝ)+(d:ℝ) := by exact_mod_cast height
  have fit : (t:ℝ) ≤ (2+(d:ℝ))*(h:ℝ)^(1/a) := by
    nlinarith only [upper,g.digit_hi,mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) (sub_nonneg.mpr root)]
  calc
    _ ≤ ((2+(d:ℝ))*(h:ℝ)^(1/a))^r := rpow_le_rpow (Nat.cast_nonneg _) fit hr
    _ = _ := by
      rw [mul_rpow (by positivity : 0≤2+(d:ℝ)) (rpow_nonneg (Nat.cast_nonneg h) _),
        ← rpow_mul (Nat.cast_nonneg h),
        show 1/a*r = r/a by ring]

/-- Price a whole batch of local calls at the component rate, with its actual
integer payload width, whenever the batch occupies at most a constant times
the parent row count. -/
theorem GridScales.block_batch_price {a B r s K : ℝ} {h t : ℕ} (g : GridScales a B h)
    (ha : 0<a) (hr : 0≤r) (hs : 0≤s) (d : ℕ) (height : t ≤ 2*digitBits a h+d)
    (rows : s*(2:ℝ)^t ≤ K*(2:ℝ)^h) :
    s*((2:ℝ)^t*(⌈(t:ℝ)^a⌉₊:ℝ)*(t:ℝ)^r) ≤
      K*(((2+(d:ℝ))^a+1)*(2+(d:ℝ))^r)*((2:ℝ)^h*h*(h:ℝ)^(r/a)) := by
  have one : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((mul_nonneg hs (by positivity)).trans rows)
    (by positivity : 0<(2:ℝ)^h)
  have bound := g.block_rate ha ha.le d height
  rw [div_self ha.ne',rpow_one] at bound
  have payload : (⌈(t:ℝ)^a⌉₊:ℝ) ≤ ((2+(d:ℝ))^a+1)*(h:ℝ) := by
    have ceil := Nat.ceil_lt_add_one (show 0≤(t:ℝ)^a by positivity)
    linarith only [ceil,bound,one]
  calc
    _ = (s*(2:ℝ)^t)*(⌈(t:ℝ)^a⌉₊:ℝ)*(t:ℝ)^r := by ring
    _ ≤ (K*(2:ℝ)^h)*(((2+(d:ℝ))^a+1)*(h:ℝ))*((2+(d:ℝ))^r*(h:ℝ)^(r/a)) := by
      exact mul_le_mul (mul_le_mul rows payload (by positivity) (by positivity))
        (g.block_rate ha hr d height) (by positivity) (by positivity)
    _ = _ := by ring

/-- Price a single pack call at its actual shorter address length. The saved
factor of 2^j pays the larger width of the packed records. -/
theorem GridScales.pack_price {a B r : ℝ} {h u : ℕ} (g : GridScales a B h)
    (hB : 1<B) (hr : 0≤r) (d : ℕ) (height : u ≤ h-packBits B h+d) :
    (2:ℝ)^u*(⌈(u:ℝ)^B⌉₊:ℝ)*(u:ℝ)^r ≤
      ((2:ℝ)^d*((1+(d:ℝ))^B+1)*(1+(d:ℝ))^r)*((2:ℝ)^h*h*(h:ℝ)^r) := by
  have one : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  have hp : 0 < (h:ℝ) := by linarith
  have digit := g.digit_room
  have last := g.last_room
  have rows : (2:ℝ)^u*(2:ℝ)^packBits B h ≤ (2:ℝ)^d*(2:ℝ)^h := by
    rw [← pow_add,← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have upper : (u:ℝ) ≤ (h:ℝ)+(d:ℝ) := by exact_mod_cast (show u ≤ h+d by omega)
  have size : (u:ℝ) ≤ (1+(d:ℝ))*(h:ℝ) := by
    nlinarith only [upper,mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) (sub_nonneg.mpr one)]
  have rate (e : ℝ) (he : 0≤e) : (u:ℝ)^e ≤ (1+(d:ℝ))^e*(h:ℝ)^e := by
    rw [← mul_rpow (by positivity : 0≤1+(d:ℝ)) (Nat.cast_nonneg h)]
    exact rpow_le_rpow (Nat.cast_nonneg u) size he
  have mass : (h:ℝ)^B ≤ (2:ℝ)^packBits B h*(h:ℝ) := by
    calc
      _ = (h:ℝ)^(B-1)*(h:ℝ) := by rw [rpow_sub_one hp.ne']; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right g.pack_lo hp.le
  have wide : (⌈(u:ℝ)^B⌉₊:ℝ) ≤ (2:ℝ)^packBits B h*(((1+(d:ℝ))^B+1)*(h:ℝ)) := by
    have price := rate B (by linarith)
    have ceil := Nat.ceil_lt_add_one (show 0≤(u:ℝ)^B by positivity)
    have base := one_le_rpow one (show 0≤B by linarith)
    have bud := mul_le_mul_of_nonneg_left mass (show 0≤(1+(d:ℝ))^B by positivity)
    linarith only [price,ceil,base,mass,bud]
  calc
    _ ≤ (2:ℝ)^u*((2:ℝ)^packBits B h*(((1+(d:ℝ))^B+1)*(h:ℝ)))*
        ((1+(d:ℝ))^r*(h:ℝ)^r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left wide (by positivity)) (rate r hr)
        (by positivity) (by positivity)
    _ = ((2:ℝ)^u*(2:ℝ)^packBits B h)*((((1+(d:ℝ))^B+1)*(h:ℝ))*((1+(d:ℝ))^r*(h:ℝ)^r)) := by ring
    _ ≤ ((2:ℝ)^d*(2:ℝ)^h)*((((1+(d:ℝ))^B+1)*(h:ℝ))*((1+(d:ℝ))^r*(h:ℝ)^r)) :=
      mul_le_mul_of_nonneg_right rows (by positivity)
    _ = _ := by ring

/-- The aggregate row bound on a local batch implies the polynomial bound
on its log cardinality required by the tagged amplification theorem. -/
theorem GridScales.batch_log {a B K : ℝ} {h t s : ℕ} (g : GridScales a B h)
    (ha : 0<a) (hK : 0<K) (large : logb 2 K ≤ h)
    (height : 2*digitBits a h ≤ t) (hs : 0<s) (slots : (s:ℝ)*(2:ℝ)^t ≤ K*(2:ℝ)^h) :
    logb 2 (s:ℝ) ≤ (t:ℝ)^(a+1) := by
  have sp : 0 < (s:ℝ) := by exact_mod_cast hs
  have unit : (1:ℝ) ≤ 2^t := one_le_pow₀ (by norm_num)
  have whole : (s:ℝ) ≤ K*(2:ℝ)^h :=
    (le_mul_of_one_le_right sp.le unit).trans slots
  have logarithm := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) sp whole
  rw [logb_mul hK.ne' (by positivity : (2:ℝ)^h≠0),logb_pow,logb_self_eq_one (by norm_num),
    mul_one] at logarithm
  have digs := g.digit_room
  have t2 : (2:ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
  have root := g.digit_lo
  have ht : 2*(digitBits a h:ℝ) ≤ t := by exact_mod_cast height
  have base : (h:ℝ)^(1/a) ≤ t := by linarith
  have power := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg h) _) base ha.le
  rw [← rpow_mul (Nat.cast_nonneg h),one_div_mul_cancel ha.ne',rpow_one] at power
  rw [rpow_add_one (show (t:ℝ) ≠ 0 by linarith)]
  calc
    _ ≤ 2*(h:ℝ) := by linarith
    _ ≤ (t:ℝ)^a * (t:ℝ) := by
      rw [mul_comm ((t:ℝ)^a)]
      exact mul_le_mul t2 power (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem tendsto_digitBits {a : ℝ} (ha : 0<a) : Tendsto (digitBits a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [(tpow (one_div_pos.mpr ha)).eventually_ge_atTop (N:ℝ)] with h hh
  exact Nat.le_floor hh

/-- All eventual component estimates apply simultaneously on the two grids,
including bounded padding added to either address height. -/
theorem eventual_grid_components {a B : ℝ} (ha : 1<a) (hB : 1<B) {P Q : ℕ → Prop}
    (small : ∀ᶠ t in atTop, P t) (large : ∀ᶠ t in atTop, Q t) :
    ∀ᶠ h : ℕ in atTop, ∀ t u : ℕ, 2*digitBits a h ≤ t → h-packBits B h ≤ u → P t ∧ Q u := by
  obtain ⟨m,hm⟩ := eventually_atTop.mp small
  obtain ⟨n,hn⟩ := eventually_atTop.mp large
  filter_upwards [eventual_grid_scales ha hB,
    (tendsto_digitBits (show 0<a by linarith)).eventually_ge_atTop m,
    eventually_ge_atTop (2*n)] with h scale block height
  have digits := scale.digit_room
  have last := scale.last_room
  intro t u ht hu
  exact ⟨hm _ (by omega),hn _ (by omega)⟩

end Hierarchy.Tagged.Radix

end
end OAI
