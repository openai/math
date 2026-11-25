import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Eval
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.ResetRate
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Mixer.Apply
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Plan
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat.Rule
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat.HeaderCost

/-! # The common template and label capacity for a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore

open Packing Assembly Assembly.History
variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} (P : Rotor F Y l)
    (S : Setup F x y) (T : Template F) (u Δ t : ℕ) (R : Budget) (a : ℕ)

def gain := 89 * 2 ^ t
def e := Nat.clog 2 (gain t * R.load)
def c := Nat.clog 2 (2 ^ S.discount * (gain t * R.load) * S.U + 1)

abbrev meter := Template.Meter.bounded (c S t R) 1 (1 / (2 : ℝ) ^ S.discount)
abbrev cap := Reset.overhead T.scheme (e t R) + R.tag * (2 ^ S.discount * (gain t * R.load))
abbrev book := Reset.Book.make T.scheme u (e t R) (cap S T t R) T.order {S.U}
abbrev next := T.reset P Δ (degreeBound S T Δ) a (book S T u t R) (meter S t R)
abbrev added (Y : ℕ) := (Post.headerFmt (Reset.Child.width (degreeBound S T Δ) Y T.full) (e t R)
    (Reset.Book.lenBits {S.U})).width + Reset.overhead T.scheme (e t R)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Electing a valid reset uniformly over a batch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Packing Assembly
open scoped Classical

def tolerance (Δ Y : ℕ) : ℝ := 1 / ((Detour.steps (terminalWidth Δ Y) : ℝ) + 1)

structure Slice (Δ Y l t : ℕ) : Prop where
  enough : 4 * coreBins Δ ≤ Y
  space : Y ^ 2 * l ≤ 2 ^ t
  small : 144 * resetWeight t / (2 : ℝ) ^ t + 4 * (Template.Encodes.margin Δ : ℝ) ^ 2 / (2 : ℝ) ^ t ≤ tolerance Δ Y
  core : 3 ≤ Δ

theorem exists_slice (Δ Y l : ℕ) (he : 4 * coreBins Δ ≤ Y) (hd : 3 ≤ Δ) : ∃ t, Slice Δ Y l t := by
  obtain ⟨t, ht, hs⟩ := small_resetWeight (Template.Encodes.margin Δ) (tolerance Δ Y)
    (by unfold tolerance; positivity) (Nat.clog 2 (Y ^ 2 * l))
  exact ⟨t, he, (Nat.clog_le_iff_le_pow (by decide)).mp ht, hs, hd⟩

variable {F : Type} [Field F] {x y : Wire}

def indices (S : Setup F x y) (r : ℕ) (R : Budget) (Δ : ℕ) :=
  Phase.base S r R + 4 * (Template.Encodes.margin Δ) ^ 2

variable {S : Setup F x y} {T : Template F} {R : Budget}
  {w r u d K Δ Y l t : ℕ} {σ : ℝ} (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state)

local notation "a" => (T.scheme.h - r)
local notation "D" => degreeBound S T Δ
local notation "W" => ((2 : ℝ) ^ t * (R.load * S.z : ℕ))
local notation "g" => Template.Encodes.margin Δ
local notation "b" => indices S r R Δ

include h in
omit [Field F] in
private theorem capacity : 0 < W := by
  have := h.vpos.trans_le h.load
  positivity

include h in
omit [Field F] in
private theorem normalized (v : ℝ) (hv : v ≤ (R.load * S.z : ℕ)) : v / W ≤ 1 / (2 : ℝ) ^ t := by
  rw [div_le_div_iff₀ (capacity h) (by positivity), one_mul, mul_comm v]
  exact mul_le_mul_of_nonneg_left hv (by positivity)

include h in
omit [Field F] in
theorem unit (_s : Slice Δ Y l t) : (u : ℝ) / W ≤ 1 / (2 : ℝ) ^ t := normalized h u (Nat.cast_le.mpr h.load)

include h in
theorem slack (_s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state) : W * (Fintype.card q.val.G.V * 2 ^ a : ℕ) ≤ σ := by
  have hv : Fintype.card q.val.G.V ≤ 2 ^ T.scheme.m := by
    simpa using Fintype.card_le_of_injective _ q.val.encodes.post.host.injective
  apply le_of_mul_le_mul_right _ (show (0 : ℝ) < 2 ^ r by positivity)
  apply le_trans _ h.slack
  push_cast
  rw [mul_assoc, mul_assoc (Fintype.card q.val.G.V : ℝ), ← pow_add, Nat.sub_add_cancel h.group, pow_add]
  gcongr
  · exact_mod_cast hk
  · exact_mod_cast hv

include h in
omit [Field F] in
private theorem limits :
    4 * g ^ 2 < 2 ^ b ∧ 6 * 2 ^ T.scheme.h < 2 ^ b ∧ R.load * S.z * 2 ^ S.discount < 2 ^ b := by
  have hbase : 3 + S.h + Nat.clog 2 (1 + S.U) + S.discount + R.load ≤ b := by
    unfold indices Phase.base
    have := Nat.two_pow_pos r
    have := Nat.lt_two_pow_self (n := S.discount)
    omega
  refine ⟨(Nat.le_add_left ..).trans_lt (Nat.lt_two_pow_self (n := b)), ?_, ?_⟩
  · calc
      _ < 2 ^ 3 * 2 ^ T.scheme.h := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
      _ = 2 ^ (3 + T.scheme.h) := (pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by have := h.height; omega)
  · have hz := (Nat.le_of_dvd h.vpos h.divides).trans h.ceiling
    have hz' : S.z ≤ 2 ^ Nat.clog 2 (1 + S.U) :=
      (hz.trans (Nat.le_add_left ..)).trans (Nat.le_pow_clog (by decide) _)
    calc
      _ < 2 ^ R.load * S.z * 2 ^ S.discount := by gcongr; exact h.zpos; exact Nat.lt_two_pow_self
      _ ≤ 2 ^ R.load * 2 ^ Nat.clog 2 (1 + S.U) * 2 ^ S.discount := by gcongr
      _ = 2 ^ (R.load + Nat.clog 2 (1 + S.U) + S.discount) := by rw [pow_add, pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

include h in
private theorem integer (v : q.val.G.V) (i : Cell T.scheme.h) :
    ∃ n : Coloring.B b, q.val.G.load v i * (2 ^ S.discount : ℕ) = n.val := by
  let G := q.val.G
  let c := (v, i)
  have hm : G.mass ≤ S.fringe.cap := by
    have hp := q.property.mass
    have := h.width
    exact_mod_cast (show (G.mass : ℝ) ≤ S.cap by linarith only [hp, h.history, this])
  let z := ∑ j, if G.park j = c then 1 else 0
  have hp : push G.park S.fringe.charge c = (z : ℝ) := by
    simp only [z, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, push]
    rfl
  let n := (G.tetherLoad c + degree G.pair c * u + z) * 2 ^ S.discount + G.past c
  have he : G.load v i * (2 ^ S.discount : ℕ) = (n : ℝ) := by
    rw [HostNet.load, hp, HostNet.rate, ite_eq_left hm]
    change (_ + 1 * (z : ℝ) + (1 / (2 : ℝ) ^ S.discount) * G.past c) * _ = _
    simp only [n, c, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, one_mul]
    field_simp
  have hn : n ≤ R.load * S.z * 2 ^ S.discount := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [← he, Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (q.property.bounded.2.2 v i) (Nat.cast_nonneg _)
  exact ⟨⟨n, hn.trans_lt (limits h).2.2⟩, he⟩

include h s hk in
theorem ok : Template.Encodes.Fits (G := q.val.G) a t Δ D g (2 ^ S.discount)
    (Nat.clog 2 (T.scheme.h + 1)) b W (tolerance Δ Y) where
  corePos := by have := s.core; omega
  full := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  late _ := by
    have he : 2 ^ S.h ≤ 2 * D := by
      unfold degreeBound
      have := Nat.two_pow_pos T.scheme.m
      have := Nat.two_pow_pos S.h
      omega
    have ht := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (he.trans (Nat.le_pow_clog (by decide) _))
    have := h.height
    omega
  gap := by
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk.trans h.room)
    have := h.group
    omega
  depth := Nat.le_pow_clog (by decide : 1 < 2) _
  integer := integer h q
  denominator := Nat.two_pow_pos _
  width := h.vpos
  margin := by unfold Template.Encodes.margin; have := s.core; positivity
  widthLimit := (limits h).1
  weightLimit := (limits h).2.1
  capacity := capacity h
  bound v i := normalized h _ (by rw [Nat.cast_mul]; exact q.property.bounded.2.2 v i)
  cdeg := q.property.bounded.1
  ndeg := q.property.bounded.2.1
  small := s.small

abbrev poll := q.val.encodes.elected (ok h s hk q) s.enough s.space (unit h s)

theorem fits (P : Rotor F Y l) {c : ℝ} (hc : 1 ≤ c) (cost : (Fintype.card P.E : ℝ) ≤ c * Y * l) :
    (poll h s hk q).Fits P c where
  upper := (ok h s hk q).full
  full := q.property.bounded.2.1
  nonneg := zero_le_one.trans hc
  cost := cost
  small := by
    change (Detour.steps (terminalWidth Δ Y) : ℝ) * tolerance Δ Y ≤ 1
    unfold tolerance
    rw [mul_one_div, div_le_one (by positivity)]
    exact le_add_of_nonneg_right zero_le_one

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-!
# Budgeting a common permutation of old blocks

The permutation table itself is computed once, then broadcast.
The work quadratic in the number of block indices fits in the
host budget. Per host the circuit is linear in the number of indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore

open Assembly Phase Phase.Case Coloring

variable {F : Type} [Field F] {d : ℕ}
local notation "I" => Case F 1 d

theorem height_short : Short (fun i : I => i.height) :=
  levels.rate.short.mono fun i => i.h.height

theorem four_heights (i : I) : 4 * i.height ≤ i.m := by
  have ha : i.S.h ≤ i.base := by
    unfold Case.base Phase.base
    have := Nat.zero_le (2 ^ i.r)
    have := Nat.zero_le (2 ^ i.S.discount)
    omega
  have hb := (((i.h.height.trans ha).trans i.base_rate).trans i.rate_short).trans
    ((Nat.le_self_pow i.h.positive.ne' i.short).trans i.h.small)
  have hc := i.h.lower
  unfold Case.height Case.m
  omega

theorem data_short : Short (fun i : I => (History.Reset.Tile.data i.T).width) := by
  simpa only [History.Reset.Tile.data, Format.width_pair, Format.width_addr] using
    (Case.bits.add counters : Short (fun i : I => _))

theorem application (h m : ℕ) (A : Format) (hh : h ≤ m) :
    Mixing.applyCost h A m ≤
      2 ^ (m + h) * (100 * (1 + h + A.width) ^ 2 + (100 + (h + A.width)) ^ 8) := by
  let M := 2 ^ m
  let H := 2 ^ h
  let a := A.width
  let p := (100 + (h + a)) ^ 8
  have hM : 0 < M := by unfold M; positivity
  have hH : 0 < H := by unfold H; positivity
  have hm : H ≤ M := Nat.pow_le_pow_right (by decide) hh
  change h + Install.localCost h * (H * h) + (Mixing.Data h A m).width + (Perm h).width +
    (Mixing.Data h A m).width + 2 * (Format.vec m (.pair (.vec h A) (Perm h))).width +
    M * (H * p) + 3 * (Mixing.Data h A m).width ≤ _
  simp only [Mixing.Data, Perm, Format.width_vec, Format.width_pair, Format.width_addr, Install.localCost,
    pow_add, pow_one]
  change h + (2 * h + 8 * (H * 2)) * (H * h) + M * (H * a) + H * h + M * (H * a) + 2 * (M * (H * a + H * h)) +
    M * (H * p) + 3 * (M * (H * a)) ≤ M * H * (100 * (1 + h + a) ^ 2 + p)
  have h₁ := Nat.le_mul_of_pos_left (H * h) hM
  have h₂ := Nat.le_mul_of_pos_left (H * h * h) hM
  have h₃ := Nat.mul_le_mul_right (H * h) hm
  have h₄ := Nat.le_mul_of_pos_left h hH
  ring_nf at h₁ h₂ h₃ h₄ ⊢
  omega

theorem apply_bound (d : ℕ) : Cost (fun i : Case F 1 d =>
    Mixing.applyCost i.height (History.Reset.Tile.data i.T) i.m) := by
  let w (i : Case F 1 d) := (History.Reset.Tile.data i.T).width
  have a : Short (fun i : Case F 1 d => 100 * (1 + i.height + w i) ^ 2 + (100 + (i.height + w i)) ^ 8) :=
    ((short_const 100).mul ((((short_const 1).add height_short).add data_short).pow 2)).add
      (((short_const 100).add (height_short.add data_short)).pow 8)
  exact (Mixed.short Case.m a).mono (fun i => application _ _ _ (by have := four_heights i; omega))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-!
# Electing a mixer

All pairwise tests of block indices take place on a single aggregated
array. There are fewer such pairs than host addresses. The only
arithmetic repeated at every block operates on short words.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Assembly Phase Phase.Case Coloring

variable {F : Type} [Field F] {d : ℕ}
local notation "I" => Case F 1 d
variable {g e k s : Case F 1 d → ℕ}

private theorem once (hg : Long g) : Cost (fun i : I => 2 ^ i.height * g i) :=
  (Mixed.long Case.m hg).mono fun i : I => Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by decide) (by have := four_heights i; omega))

private theorem twice (hg : Long g) : Cost (fun i : I => 2 ^ i.height * (2 ^ i.height * g i)) := by
  refine (Mixed.long Case.m hg).mono fun i : I => ?_
  rw [← mul_assoc, ← pow_add]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by have := four_heights i; omega))

private theorem precision (hg : Short g) : Short (fun i : I => Mixing.precision i.height (g i)) :=
  ((short_const 2).mul (height_short.add hg)).add (short_const 1)

variable (he : Short (fun i : Case F 1 d => 2 ^ (e i))) (hk : Short (fun i : Case F 1 d => 2 ^ (k i))) (hg : Short g)

include he hk hg in
theorem mixer_arity (hs : Short s) :
    Short (fun i : I => Mixing.arity (e i) i.height (k i) (s i) (g i)) := by
  have h₁ := (short_const 4).mul (precision hg)
  have h₂ := hs.add (he.mul hg)
  have h₃ := ((short_const 2).add hk.of_exp).add (hk.mul hg)
  refine (h₁.add (h₂.add h₃)).mono fun i : I => ?_
  unfold Mixing.arity
  omega

include hk hg in
private theorem row : Phase.Case.Row (fun i : I => Mixing.rowCost i.height (k i) (g i)) := by
  let p := precision hg
  let a := height_short (F := F) (d := d)
  let x (j) := short_const (F := F) (b := 1) (d := d) j
  have hcorr : Phase.Case.Row (fun i : I => Mixing.corrCost i.height (g i)) :=
    Short.blocks ((((x 1).add hg).add p).add ((((x 2).mul a).add (x 3)).mul
      ((x 1).add ((x 4).mul p))) |>.add (((x 1).add p).add p))
  have small := Long.row (Short.long (hk.mul hg))
  have hp : Phase.Case.Row (fun i : I => Mixing.pairCost i.height (k i) (Mixing.precision i.height (g i)) (g i)) := by
    refine (((p.blocks.add small).add (((Short.blocks (p.add hg)).left hk).scale 2))).mono fun i : I => ?_
    simp only [Mixing.pairCost, pow_add, mul_assoc]
    exact le_rfl
  have hword := p.add hg
  have last := (Short.blocks (((x 1).add hword).add hword)).left hk
  refine (((hcorr.add (small.scale 4)).add (hp.scale 4)).add last).mono fun i : I => ?_
  simp only [Mixing.rowCost, Mixing.wordLength, pow_add, mul_assoc]
  exact le_rfl

include he hk hg in
private theorem test : Cost (fun i : I => Mixing.testCost (i.m + e i) (k i + i.height) (g i) i.height) := by
  let M := hosts.add (Short.long he.of_exp)
  let l := (hg.long.add M)
  let c (n) := short_const (F := F) (b := 1) (d := d) n
  have hc : Cost (fun i : I => Mixing.collectCost (i.m + e i) (k i + i.height) (g i)) := by
    have a := ((c 3).mul hg).add (((c 100).add hg).pow 5)
    refine ((Short.blocks a).expand he |>.left hk).mono fun i : I => ?_
    unfold Mixing.collectCost
    rw [pow_add]
    exact le_of_eq (by ac_rfl)
  have hm : Cost (fun i : I => Mixing.maskCost (k i + i.height) i.height (g i + (i.m + e i))) := by
    refine (((once l).left hk).add (((twice l).left hk).scale (Install.localCost 1))).mono fun i : I => ?_
    unfold Mixing.maskCost
    rw [pow_add]
    exact le_of_eq (by ac_rfl)
  let t := height_short (F := F) (d := d)
  have h₁ := (twice (((long_const 100).add l).pow 5)).left hk
  have h₂ := once (((long_const 100).add (t.long.add (l.add (Short.long (hk.of_exp.add t))))).pow 42)
  refine ((hc.add hm).add (h₁.add h₂)).mono fun i : I => ?_
  unfold Mixing.testCost
  rw [mul_add, pow_add]
  exact le_of_eq (by ac_rfl)

include he hk hg in
theorem mixer_cost : Cost (fun i : I => Mixing.cost (i.m + e i) i.height (k i) (g i)) :=
  ((row hk hg).expand he).add ((test he hk ((precision hg).add hg)).scale 4)

include he hk hg in
theorem mixer_extract (hs : Short s) :
    Cost (fun i : I => Mixing.extractionCost i.m (e i) i.height (k i) (s i) (g i)) := by
  let a := (short_const 1).add (mixer_arity he hk hg hs)
  have hd := Long.row (Short.long (hk.mul hg))
  have h₁ := ((he.long.row.add ((short_const 1).blocks)).mul a)
  have h₂ := ((hd.left he).add (Short.blocks (he.mul hg)))
  have h₃ := Phase.Case.Row.expand (hg.blocks.add hd) he
  refine ((Phase.Case.Row.hosts h₁).add (((Phase.Case.Row.hosts h₂).add (h₃.scale 2)).scale 4)).mono fun i : I => ?_
  change _ + 4 * ((Format.vec i.m (.pair (Mixing.Matrix (e i) (k i) (g i))
    (Mixing.Matrix i.height (e i) (g i)))).width + 2 * (Mixing.Rows _ _ _ _).width) ≤ _
  simp only [Mixing.Matrix, Mixing.Rows, Mixing.Input, Mixing.Num, Format.width_vec, Format.width_pair,
    Format.width_addr, mul_one]
  exact le_rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-!
# A sequence of encoded phases

The bound on elementary coefficients stays fixed across concatenation.
The rate and additive loss compose affinely. Separate limits keep long
addresses out of the polynomial charged at every block.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire}

/-- The indices are incoming and outgoing core degrees and neighbor
widths, subdivision, step count, and the two affine coefficients. -/
inductive Sequence (F : Type) [Field F] (K : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → Prop
  | one {Δ Δ' d d' b k ρ C} : Phase F Δ Δ' d d' b k ρ C →
      0 < b → 0 < k → k ≤ K → 0 ≤ ρ → 0 ≤ C → 4 + ρ + C ≤ K →
      Sequence F K Δ Δ' d d' b 1 ρ C
  | comp {Δ Δ' Δ'' d d' d'' b b' n n' ρ ρ' C C'} :
      Sequence F K Δ Δ' d d' b n ρ C → Sequence F K Δ' Δ'' d' d'' b' n' ρ' C' →
      Sequence F K Δ Δ'' d d'' (b * b') (n + n') (ρ' * ρ) (ρ' * C + C')
  | relax {Δ Δ' Δ'' d d' d'' b n ρ ρ' C C'} :
      Sequence F K Δ Δ' d d' b n ρ C → Δ' ≤ Δ'' → d' ≤ d'' → ρ ≤ ρ' → C ≤ C' →
      Sequence F K Δ Δ'' d d'' b n ρ' C'

structure Limits where
  m : ℕ
  steps : ℕ
  w : ℕ
  r : ℕ
  K : ℕ
  A : ℕ
  start : Budget
  σ : ℝ

namespace Limits
variable (L : Limits)
def extra := (3 * L.A ^ L.K) ^ L.K
def maxTag := L.start.tag + L.steps * L.extra
def code := (1 + L.maxTag) * L.extra
def small := 4 * L.A ^ L.K + L.code + L.maxTag
def host := L.m + L.steps * (L.r + L.K)
def seats (h : ℕ) := L.m + h + L.steps * L.K
def cost (h : ℕ) :=
  2 ^ L.host * (100 + L.w + L.small) ^ L.K + 2 ^ (L.seats h) * L.small ^ L.K
end Limits

variable (S : Setup F x y) (L : Limits)

/-- Uniform headroom, established once for the whole sequence. -/
structure Enough : Prop where
  trivalent : S.G.Trivalent
  zpos : 0 < S.z
  names : S.e ≤ 3 * L.w
  positive : 0 < L.K
  height : L.steps * L.r ≤ S.h
  room : L.K ≤ 2 ^ L.r
  lower : L.w ≤ L.m
  upper : L.host + L.K * (S.h + 1) ≤ 2 * L.w
  basic : 100 + 2 ^ L.r + S.h + Nat.clog 2 (1 + S.U) + 2 ^ S.discount +
    L.K ^ L.steps * L.start.load + S.d ≤ L.A
  logarithm : Nat.clog 2 (1 + L.code) ≤ L.A ^ L.K
  labels : L.small ^ L.K ≤ L.w / 4
  origins : 3 * (L.K ^ L.steps * L.start.reach) ≤ S.d
  history : (L.K ^ L.steps : ℕ) * (L.start.mass + L.start.width + (S.fringe.Z + L.σ)) ≤ S.cap
  slack : ((L.K * (L.K ^ L.steps * L.start.load * S.z) * 2 ^ (L.seats S.h) : ℕ) : ℝ) ≤ L.σ * (2 : ℝ) ^ L.r

/-- Invariants after exactly `i` elementary steps. -/
structure Inside (T : Template F) (P : Budget) (u d i : ℕ) : Prop where
  height : T.scheme.h + i * L.r = S.h
  lower : L.w ≤ T.scheme.m
  upper : T.scheme.m ≤ L.m + i * (L.r + L.K)
  degree : T.scheme.d ≤ d
  core : T.full = false
  single : T.scheme.k = 0
  spans : 2 ^ T.scheme.e ≤ L.A ^ L.K
  counters : T.count ≤ L.A ^ L.K
  bits : T.scheme.ℓ ≤ L.code
  tag : P.tag ≤ L.start.tag + i * L.extra
  capacity : u ≤ P.load * S.z
  load : P.load ≤ L.K ^ i * L.start.load
  reach : 0 < P.reach
  origins : P.reach ≤ L.K ^ i * L.start.reach
  width : 0 ≤ P.width
  mass : 0 ≤ P.mass
  potential : P.mass + P.width + (S.fringe.Z + L.σ) ≤
    (L.K ^ i : ℕ) * (L.start.mass + L.start.width + (S.fringe.Z + L.σ))

structure Completion (T : Template F) (P : Budget) (u v Δ Δ' d' i n : ℕ) (ρ C : ℝ) where
  next : Template F
  budget : Budget
  inside : Inside S L next budget v d' (i + n)
  width : budget.width ≤ ρ * P.width + C * (S.fringe.Z + L.σ)
  labels : Finset (Table F)
  few : labels.card ≤ n * L.small ^ L.K
  small : ∀ k ∈ labels, Processor.arity k ≤ L.small ^ L.K
  scale : ℕ
  size : ℕ
  cost : size ≤ n * L.cost S.h
  transfer : Transforms F scale (Allowed F L.w ∪ (labels : Set (Table F)))
    (frame S T u Δ P) (frame S next v Δ' budget) size

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Choosing one repeatable block of encoded phases

Use the same gadget, subdivision and reset rotor for the quantitative
reduction and for the encoded sequence. The neighbor allowance after
reset is chosen before fixing the incoming allowance.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Packing

def SubroundRule (F : Type) [Field F] : Prop :=
  ∀ (P : Gadget F) Δ, 3 ≤ Δ → ∀ d, ∃ d' K, 0 < K ∧
    Phase F Δ (Δ ^ degreePower) d d' P.b K P.ratio 1

def ResetRule (F : Type) [Field F] : Prop :=
  ∀ (y w Δ : ℕ) (R : Rotor F (2 ^ y) w) (c : ℝ), 0 < w → 3 ≤ Δ → 4 * coreBins Δ ≤ 2 ^ y →
    1 ≤ c → (Fintype.card R.E : ℝ) ≤ c * (2 : ℝ) ^ y * w →
    ∃ d', ∀ d, ∃ K, 0 < K ∧ Phase F Δ 3 d d' 1 K (2 * resetWidth c w) (2 * resetWidth c w)

variable {F : Type} [Field F]
namespace Sequence

variable {Δ Δ' d d' b n K K' : ℕ} {ρ C : ℝ}

theorem enlarge (q : Sequence F K Δ Δ' d d' b n ρ C) (hk : K ≤ K') :
    Sequence F K' Δ Δ' d d' b n ρ C := by
  induction q with
  | one g hb hp hu hρ hc hm => exact .one g hb hp (hu.trans hk) hρ hc (hm.trans (Nat.cast_le.mpr hk))
  | comp _ _ ih ih' => exact ih.comp ih'
  | relax _ hΔ hd hρ hc ih => exact ih.relax hΔ hd hρ hc

private theorem single {k : ℕ} (q : Phase F Δ Δ' d d' b k ρ C) (hb : 0 < b) (hk : 0 < k)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ C) : ∃ K, Sequence F K Δ Δ' d d' b 1 ρ C :=
  ⟨max k ⌈4 + ρ + C⌉₊, .one q hb hk (le_max_left _ _) hρ hc
    ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _)))⟩

private theorem contractions (φ : SubroundRule F) (P : Gadget F) (Δ d : ℕ)
    (hΔ : 3 ≤ Δ) (t : ℕ) (ht : 0 < t) :
    ∃ d' K, Sequence F K Δ (Δ ^ (degreePower ^ t)) d d' (P.b ^ t) t (P.ratio ^ t) t := by
  have hp : 0 < degreePower := by decide
  have group (Δ d : ℕ) (hΔ : 3 ≤ Δ) :
      ∃ d' K, Sequence F K Δ (Δ ^ degreePower) d d' P.b 1 P.ratio 1 := by
    obtain ⟨d', k, hk, hq⟩ := φ P Δ hΔ d
    exact ⟨d', single hq P.pos hk P.ratio_bounds.1 zero_le_one⟩
  induction t, ht using Nat.le_induction with
  | base => simpa only [pow_one, Nat.cast_one] using group Δ d hΔ
  | succ t _ ih =>
    obtain ⟨e, K, p⟩ := ih
    obtain ⟨d', K', q⟩ := group (Δ ^ (degreePower ^ t)) e (hΔ.trans (Nat.le_self_pow (by positivity) _))
    refine ⟨d', max K K', ?_⟩
    have h := (p.enlarge (le_max_left K K')).comp (q.enlarge (le_max_right K K'))
    rw [← pow_mul Δ (degreePower ^ t) degreePower, ← pow_succ degreePower, ← pow_succ P.b,
      ← pow_succ' P.ratio] at h
    refine h.relax le_rfl le_rfl le_rfl ?_
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (mul_le_of_le_one_left (Nat.cast_nonneg _) P.ratio_bounds.2.le) _

private theorem iterate (p : Sequence F K Δ Δ d d b n (1 / 2) C) (hC : 0 ≤ C)
    (j : ℕ) (hj : 0 < j) : Sequence F K Δ Δ d d (b ^ j) (n * j) ((1 / 2) ^ j) (2 * C) := by
  induction j, hj using Nat.le_induction with
  | base =>
    simp only [Nat.succ_eq_add_one, Nat.zero_add, pow_one, mul_one]
    exact p.relax le_rfl le_rfl le_rfl (by linarith)
  | succ j _ ih =>
    rw [pow_succ b, Nat.mul_succ, pow_succ' (1 / 2 : ℝ)]
    exact (ih.comp p).relax le_rfl le_rfl le_rfl (by linarith)

end Sequence

theorem sequence_recipe (ht : ¬Tagged.Hard F) (hgroup : SubroundRule F) (hreset : ResetRule F) :
    ∃ (P : Recipe F) (K d : ℕ), 0 < K ∧ 3 ≤ d ∧ 4 ^ (P.n * (K + 2) + K + 2) ≤ P.H ∧
      ∀ j : ℕ, 0 < j → Sequence F K 8 8 d d (P.b ^ j) (P.n * j) ((1 / 2) ^ j) P.C := by
  obtain ⟨P⟩ := gadget_exists F
  obtain ⟨t, y, w, R, c, ht, hw, hc, hsize, en, hdecay⟩ :=
    choose_rotor (.inr ht) 8 degreePower P.ratio 250 P.ratio_bounds.1 P.ratio_bounds.2 (by norm_num)
  let D := 8 ^ (degreePower ^ t)
  have : 0 < degreePower := by decide
  have hD : 3 ≤ D := (show 3 ≤ 8 by decide).trans (Nat.le_self_pow (by positivity) _)
  have enough : 4 * coreBins D ≤ 2 ^ y := by simpa only [coreBins, mul_assoc] using en D le_rfl
  have hR : (Fintype.card R.E : ℝ) ≤ c * (2 : ℝ) ^ y * w :=
    (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsize
  let r := 2 * resetWidth c w
  have hr : 0 ≤ r := by unfold r resetWidth; positivity
  have bound : r ≤ 250 * (1 + c + Nat.clog 2 w) := by
    unfold r resetWidth
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 w)]
  have decrease := (mul_le_mul_of_nonneg_right bound (pow_nonneg P.ratio_bounds.1 t)).trans hdecay
  let b := P.b ^ t * 1
  let n := t + 1
  let e := degreePower ^ t * (900 + 2 ^ y + 1)
  let C := r * t + r
  obtain ⟨X, g⟩ := Reduction.subrounds P 8 (by decide) t ht
  obtain ⟨Y, q⟩ := Reduction.reset R (by positivity) hw hD enough c (by linarith) (by simpa using hR)
  let H₀ := Reduction.fee X (P.ratio ^ t) t * Y
  have step : Reduction F 8 3 b n e H₀ (1 / 2) C :=
    ((g F).comp (q F)).relax le_rfl decrease le_rfl
  obtain ⟨d', reset⟩ := hreset y w D R c hw hD enough hc hR
  let d := max 3 d'
  obtain ⟨v, k, hg⟩ := Sequence.contractions hgroup P 8 d (by decide) t ht
  obtain ⟨k', hk, hq⟩ := reset v
  obtain ⟨l, hl⟩ := Sequence.single hq (by decide) hk hr hr
  let K := max k l + 1
  have seq : Sequence F K 8 8 d d b n (1 / 2) C :=
    ((hg.enlarge (show k ≤ K by unfold K; omega)).comp (hl.enlarge (by unfold K; omega))).relax
      (by decide) (le_max_right _ _) decrease le_rfl
  let H := max (Reduction.fee H₀ (1 / 2) C) (4 ^ (n * (K + 2) + K + 2))
  let recipe : Recipe F := ⟨b, n, e, H, 2 * C, fun j hj =>
    (step.iterate (by decide) (by unfold e; positivity) j hj).relax
      (Nat.pow_le_pow_left (le_max_left _ _) j) le_rfl le_rfl⟩
  exact ⟨recipe, K, d, by unfold K; omega, le_max_left _ _, le_max_right _ _, seq.iterate step.loss⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Checking headroom at each phase boundary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Assembly Packing

variable {F : Type} {x y : Wire} {S : Setup F x y} {T : Template F}
  {L : Limits} {P : Budget} {u d i k b v : ℕ}

theorem Enough.pos (H : Enough S L) : 0 < L.A := lt_of_lt_of_le (by positivity) H.basic

namespace Inside

variable (D : Inside S L T P u d i) (H : Enough S L) (h : i ≤ L.steps)
include D h

theorem hosts : T.scheme.m ≤ L.host :=
  D.upper.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)

theorem seats : T.scheme.m + T.scheme.h ≤ L.seats S.h := by
  have ht := D.upper
  rw [mul_add] at ht
  have hh := D.height
  have hi := Nat.mul_le_mul_right L.K h
  unfold Limits.seats
  omega

theorem tags : P.tag ≤ L.maxTag :=
  D.tag.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)

include H

theorem loads : P.load ≤ L.K ^ L.steps * L.start.load :=
  D.load.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right H.positive h))

theorem base : Phase.base S L.r P ≤ L.A := by
  have := D.loads H h
  have := H.basic
  unfold Phase.base
  omega

theorem rate : Phase.rate S T L.r P ≤ 3 * L.A ^ L.K := by
  have ha := (D.base H h).trans (Nat.le_self_pow H.positive.ne' L.A)
  have hs := D.spans
  have ht := (Nat.clog_mono_right 2 (Nat.add_le_add_left D.bits 1)).trans H.logarithm
  unfold Phase.rate
  omega

theorem short : Phase.short S T L.r P ≤ L.small := by
  have := D.rate H h
  have := D.tags h
  have := D.bits
  have := D.counters
  unfold Phase.short Limits.small
  omega

omit h
theorem speed (hn : i + 1 ≤ L.steps) (k : ℕ) (hk : k ≤ L.K) :
    k * P.reach ≤ L.K ^ L.steps * L.start.reach := calc
  _ ≤ L.K * (L.K ^ i * L.start.reach) := Nat.mul_le_mul hk D.origins
  _ = L.K ^ (i + 1) * L.start.reach := by rw [pow_succ', mul_assoc]
  _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right H.positive hn)

theorem charge (hn : i + 1 ≤ L.steps) (hσ : 0 ≤ L.σ) (hk : 2 ≤ L.K) :
    P.mass + 2 * P.width ≤ S.cap := by
  let Z := S.fringe.Z + L.σ
  let A := L.start.mass + L.start.width + Z
  have hZ : 0 ≤ Z := add_nonneg S.fringe.total_nonneg hσ
  have hp : P.mass + P.width + Z ≤ (L.K ^ i : ℕ) * A := D.potential
  have ha : 0 ≤ A := by
    have ht : (0 : ℝ) < (L.K ^ i : ℕ) := Nat.cast_pos.mpr (pow_pos H.positive _)
    exact nonneg_of_mul_nonneg_right ((add_nonneg (add_nonneg D.mass D.width) hZ).trans hp) ht
  calc
    _ ≤ (L.K : ℝ) * (P.mass + P.width + Z) := by
      have hK : (2 : ℝ) ≤ L.K := by exact_mod_cast hk
      nlinarith only [mul_le_mul_of_nonneg_right hK (add_nonneg (add_nonneg D.mass D.width) hZ), D.mass, hZ]
    _ ≤ (L.K : ℝ) * ((L.K ^ i : ℕ) * A) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = (L.K ^ (i + 1) : ℕ) * A := by rw [pow_succ', Nat.cast_mul, mul_assoc]
    _ ≤ (L.K ^ L.steps : ℕ) * A :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.pow_le_pow_right H.positive hn)) ha
    _ ≤ _ := H.history

theorem input (hσ : 0 ≤ L.σ) (hn : i + 1 ≤ L.steps) (hk : k ≤ L.K) (hK : 2 ≤ L.K) (hpos : 0 < k)
    (hu : u = b * v) (hv : 0 < v) (hd : S.z ∣ v) (hU : u ∣ S.U) (hU' : u ≤ S.U) :
    Phase.Input S T P L.w L.r b u v d k L.σ := by
  have hi : i ≤ L.steps := by omega
  refine ⟨H.trivalent, H.zpos, hv, hd, hu, hU, hU', D.capacity, ?_, by have := D.height; omega,
    hk.trans H.room, hpos, D.degree, D.core, D.single, H.names, D.lower, ?_, ?_, ?_, D.reach, D.width, D.mass,
    D.charge H hn hσ hK, ?_⟩
  · have ht := (Nat.mul_le_mul_right L.r hn).trans H.height
    have hh := D.height
    rw [Nat.succ_mul] at ht
    omega
  · exact (Nat.add_le_add (D.hosts hi) (Nat.mul_le_mul_right _ hk)).trans H.upper
  · have hs : 0 < L.small := by unfold Limits.small; have := H.pos; positivity
    exact ((Nat.pow_le_pow_left (D.short H hi) k).trans (Nat.pow_le_pow_right hs hk)).trans H.labels
  · exact (Nat.mul_le_mul_left 3 (D.speed H hn k hk)).trans H.origins
  · refine le_trans ?_ H.slack
    have hh := Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.mul_le_mul_right S.z (D.loads H hi)))
      (Nat.pow_le_pow_right (by decide : 0 < 2) (D.seats hi))
    exact_mod_cast hh

end Inside
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Growth estimates for a single encoded phase -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T : Template F}
  {L : Limits} {P : Budget} {u d d' i k b v Δ Δ' : ℕ} {ρ C : ℝ}

private theorem exponent {a b i j : ℕ} (h : a ≤ b) (hb : 0 < b) (hk : i ≤ j) : a ^ i ≤ b ^ j :=
  (Nat.pow_le_pow_left h _).trans (Nat.pow_le_pow_right hb hk)

theorem Completion.one (D : Inside S L T P u d i) (H : Enough S L) (hσ : 0 ≤ L.σ)
    (hn : i + 1 ≤ L.steps) (hk : 0 < k) (hr : k ≤ L.K) (hv : v ≤ u)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hl : 4 + ρ + C ≤ L.K)
    (q : Phase.Output S T P L.w L.r u v Δ Δ' d' k ρ C L.σ) :
    Nonempty (Completion S L T P u v Δ Δ' d' i 1 ρ C) := by
  have hi : i ≤ L.steps := by omega
  have hA := H.pos
  have hB := exponent (D.base H hi) hA hr
  have he : (Phase.rate S T L.r P) ^ k ≤ L.extra := exponent (D.rate H hi) (by positivity) hr
  have hs : (Phase.short S T L.r P) ^ k ≤ L.small ^ L.K :=
    exponent (D.short H hi) (by unfold Limits.small; positivity) hr
  have hz : 0 ≤ S.fringe.Z + L.σ := add_nonneg S.fringe.total_nonneg hσ
  let Q := Phase.after S T L.r P k ρ C L.σ
  have bound (a c : ℕ) (hb : a ≤ L.K ^ i * c) : k * a ≤ L.K ^ (i + 1) * c := by
    rw [pow_succ', mul_assoc]
    exact Nat.mul_le_mul hr hb
  have hp : Inside S L q.next Q v d' (i + 1) := by
    refine ⟨?_, D.lower.trans q.lower, ?_, q.degree, q.core, q.single,
      q.spans.trans hB, q.counters.trans hB, ?_, ?_, ?_, bound _ _ D.load,
      Nat.mul_pos hk D.reach, bound _ _ D.origins, ?_, ?_, ?_⟩
    · have := D.height
      have := q.height
      rw [Nat.succ_mul]
      omega
    · have := D.upper
      have := q.upper
      rw [Nat.succ_mul]
      omega
    · exact q.bits.trans (Nat.mul_le_mul (Nat.add_le_add_left (D.tags hi) 1) he)
    · change P.tag + _ ≤ _
      rw [Nat.succ_mul, ← Nat.add_assoc]
      exact Nat.add_le_add D.tag he
    · exact (hv.trans D.capacity).trans
        (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hk))
    · exact add_nonneg (mul_nonneg hρ D.width) (mul_nonneg hC hz)
    · exact add_nonneg D.mass (mul_nonneg (by norm_num) D.width)
    · let Z := S.fringe.Z + L.σ
      change 0 ≤ Z at hz
      change (P.mass + 2 * P.width) + (ρ * P.width + C * Z) + Z ≤ _
      calc
        _ ≤ (4 + ρ + C) * (P.mass + P.width + Z) := by
          nlinarith only [D.mass, D.width, hz, mul_nonneg hρ D.mass, mul_nonneg hC D.mass,
            mul_nonneg hρ hz, mul_nonneg hC D.width]
        _ ≤ (L.K : ℝ) * ((L.K ^ i : ℕ) * (L.start.mass + L.start.width + Z)) :=
          mul_le_mul hl D.potential (add_nonneg (add_nonneg D.mass D.width) hz) (Nat.cast_nonneg _)
        _ = _ := by rw [pow_succ', Nat.cast_mul, mul_assoc]
  refine ⟨⟨q.next, Q, hp, le_rfl, q.labels, by simpa using q.few.trans hs,
    fun t ht => (q.small t ht).trans hs, q.scale, q.size, ?_, q.transfer⟩⟩
  rw [one_mul]
  refine q.cost.trans (Nat.add_le_add (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (D.hosts hi)) ?_)
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (D.seats hi)) hs))
  exact exponent (Nat.add_le_add_left (D.short H hi) _) (by omega) hr

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Composition of an encoded sequence with uniform budgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T : Template F}
  {L : Limits} {P : Budget} {u v w d d' d'' i k b n n' Δ Δ' Δ'' : ℕ} {ρ ρ' C C' : ℝ}

private theorem weaken {X : Assembly.Snapshot.{1} F S.input S.output}
    {A B : Snapshot.Data S T u → Prop} (h : ∀ i, A i → B i) {G : Set (Table F)}
    (ht : Transforms F k G X (Snapshot.restrict A) n) :
    Transforms F k G X (Snapshot.restrict B) n := by
  obtain ⟨f, hf, he⟩ := ht
  refine ⟨f, hf, fun s => ?_⟩
  obtain ⟨I, _, q, c, hw, hc⟩ := he s
  exact ⟨I, inferInstance, fun j => ⟨(q j).val, h _ (q j).property⟩, c, hw, hc⟩

private theorem Completion.relax (p : Completion S L T P u v Δ Δ' d' i n ρ C)
    (hd : d' ≤ d'') (hg : Δ' ≤ Δ'') (hρ : ρ ≤ ρ') (hc : C ≤ C')
    (hx : 0 ≤ P.width) (hs : 0 ≤ L.σ) :
    Nonempty (Completion S L T P u v Δ Δ'' d'' i n ρ' C') := by
  have hi : Inside S L p.next p.budget v d'' (i + n) :=
    { p.inside with degree := p.inside.degree.trans hd }
  have hZ := add_nonneg S.fringe.total_nonneg hs
  refine ⟨⟨p.next, p.budget, hi, p.width.trans (by gcongr), p.labels, p.few, p.small,
     p.scale, p.size, p.cost, ?_⟩⟩
  refine weaken ?_ p.transfer
  intro t ht
  exact { ht with bounded := ht.bounded.mono hg (by unfold degreeBound; omega) le_rfl }

private theorem Completion.chain (p : Completion S L T P u v Δ Δ' d' i n ρ C)
    (q : Completion S L p.next p.budget v w Δ' Δ'' d'' (i + n) n' ρ' C') (hp : 0 ≤ ρ') :
    Nonempty (Completion S L T P u w Δ Δ'' d'' i (n + n') (ρ' * ρ) (ρ' * C + C')) := by
  let A := p.labels ∪ q.labels
  let j := max p.scale q.scale
  have hi := q.inside
  rw [Nat.add_assoc] at hi
  refine ⟨⟨q.next, q.budget, hi, ?_, A, ?_, ?_, j, p.size + q.size, ?_, ?_⟩⟩
  · linarith only [q.width, mul_le_mul_of_nonneg_left p.width hp]
  · rw [add_mul]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add p.few q.few)
  · intro k hk
    exact (Finset.mem_union.mp hk).elim (p.small k) (q.small k)
  · rw [add_mul]
    exact Nat.add_le_add p.cost q.cost
  · have g := p.transfer.widen (v := j) (L' := Allowed F L.w ∪ ↑A)
      (le_max_left _ _) (fun _ h => h.imp_right (Finset.mem_union_left _))
    have g' := q.transfer.widen (v := j) (L' := Allowed F L.w ∪ ↑A)
      (le_max_right _ _) (fun _ h => h.imp_right (Finset.mem_union_right _))
    exact g.comp g'

private theorem Sequence.positive (q : Sequence F k Δ Δ' d d' b n ρ C) :
    0 < b ∧ 0 ≤ ρ := by
  induction q with
  | one _ hb _ _ hr _ _ => exact ⟨hb, hr⟩
  | comp _ _ ih ih' => exact ⟨Nat.mul_pos ih.1 ih'.1, mul_nonneg ih'.2 ih.2⟩
  | relax _ _ _ hr _ ih => exact ⟨ih.1, ih.2.trans hr⟩

theorem Sequence.run (q : Sequence F L.K Δ Δ' d d' b n ρ C)
    (H : Enough S L) (hσ : 0 ≤ L.σ) (t : Inside S L T P u d i) (hn : i + n ≤ L.steps)
    (hu : u = b * v) (hv : 0 < v) (hdiv : S.z ∣ v) (hU : u ∣ S.U) (hU' : u ≤ S.U) :
    Nonempty (Completion S L T P u v Δ Δ' d' i n ρ C) := by
  induction q generalizing T P u v i with
  | one q hb hp hr hρ hc hl =>
    have hk : 2 ≤ L.K := by exact_mod_cast (show (2 : ℝ) ≤ L.K by linarith)
    have h := t.input H hσ hn hr hk hp hu hv hdiv hU hU'
    obtain ⟨r⟩ := q _ _ _ _ _ _ _ _ h
    exact Completion.one t H hσ hn hp hr (by rw [hu]; exact Nat.le_mul_of_pos_left _ hb) hρ hc hl r
  | @comp Δ Δ' Δ'' d d' d'' b b' n n' ρ ρ' C C' p q ih ih' =>
    have hu' : u = b * (b' * v) := by rw [hu, mul_assoc]
    have hm : 0 < b' * v := Nat.mul_pos q.positive.1 hv
    have hmid : b' * v ≤ u := by rw [hu']; exact Nat.le_mul_of_pos_left _ p.positive.1
    have hd : b' * v ∣ u := by rw [hu']; exact dvd_mul_left _ _
    obtain ⟨a⟩ := ih t (by omega) hu' hm (hdiv.mul_left b') hU hU'
    obtain ⟨f⟩ := ih' a.inside (by omega) rfl hv hdiv (hd.trans hU) (hmid.trans hU')
    exact a.chain f q.positive.2
  | relax p hd hw hr hc ih =>
    obtain ⟨f⟩ := ih t hn hu hv hdiv hU hU'
    exact f.relax hw hd hr hc t.width hσ

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Unconditional realization of a wire-saving batch phase -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Beat Phase Phase.Case

theorem subroundRule (F : Type) [Field F] : SubroundRule F := by
  intro P Δ hd d
  apply rule_of_bounds P Δ d hd
  · exact (((prepareWidth_bound P d).add (markWidth_bound P d)).add
      (issueWidth_bound P Δ d)).add ((short_const 2).mul (next_bits P Δ d))
  · have h₁ := (((input_bound P d).scale 100).add (prepareCost_bound P d)).add (headedCost_bound P Δ d)
    exact (((h₁.add (secondCost_bound P Δ d)).add ((candidate_bound P d).scale 4)).add (sweepCost_bound P Δ d))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
