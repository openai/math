import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Passage
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Log
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
import OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Mates
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep

/-!
# Keeping the dependence on prior labels linear

The base of the polynomial part of the restored label size uses
only the logarithm of the inherited selectors. Its exponent is
independent of the coefficient allowed for linear growth.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) {F : Type} [Field F] {x y : Wire}

structure FrameBound (Q : Layer F x y) (D : Template F) (payload K : ℕ) : Prop where
  ports : 2 ^ D.scheme.e ≤ v.box K
  height : payload ≤ v.box K
  labels : D.scheme.ℓ + D.count ≤ K * (Q.template.scheme.ℓ + Q.template.count) + v.box K

theorem pow_le_box (t : ℕ) : 2 ^ t ≤ v.box t :=
  Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (by omega))

theorem box_sum {a b c : ℕ} (h : a ≤ v.box c) (h' : b ≤ v.box c) :
    a + b ≤ v.box (c + 1) := by
  rw [box_add]
  exact (Nat.add_le_add h h').trans (by rw [← Nat.mul_two]; exact Nat.mul_le_mul_left _ (v.pow_le_box 1))

theorem log_box {a k : ℕ} (ha : a ≤ v.box k) (hk : k ≤ 2 ^ v.j) :
    Nat.clog 2 (1 + a) ≤ v.box 2 := by
  have hn : Nat.clog 2 (1 + a) ≤ k * (v.j + 1) + 1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [pow_succ]
    have := Nat.two_pow_pos (k * (v.j + 1))
    unfold box at ha
    omega
  have hh := Nat.mul_le_mul hk (show v.j + 1 ≤ 2 ^ v.j from Nat.lt_two_pow_self)
  refine hn.trans ((Nat.add_le_add_right hh 1).trans ?_)
  rw [box, show 2 * (v.j + 1) = (v.j + v.j) + 2 by omega, ← pow_add, pow_add _ _ 2]
  have := Nat.two_pow_pos (v.j + v.j)
  omega

theorem log_width {i z : ℕ} (hi : i ≤ v.j) (hz : z ≤ v.width i) :
    Nat.clog 2 (1 + z) ≤ 1 + v.stack + p.growth * v.j := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [width_eq] at hz
  have hk : 2 ^ (v.stack + p.growth * i) ≤ (2 : ℕ) ^ (v.stack + p.growth * v.j) := by gcongr
  rw [add_assoc, pow_add, pow_one]
  have ht := Nat.two_pow_pos (v.stack + p.growth * v.j)
  omega

namespace FrameBound
variable {v} {s : Plan} {m i E z payload K n B C : ℕ}
  {Q : Layer F x y} {D : Template F} (f : v.FrameBound Q D payload K)
  (cur : v.Current s n m i E Q) (hi : i ≤ v.j)

include f cur hi

theorem bits : D.scheme.ℓ + D.count ≤ v.box (K + 2 * E + 1) := by
  refine f.labels.trans (v.box_sum ?_ (v.box_mono (Nat.le_add_right ..)))
  rw [v.box_add, two_mul]
  exact Nat.mul_le_mul (v.le_box _) (cur.bits hi)

variable (h : v.Fits n B C) (hh : D.scheme.h ≤ v.blocks) (hz : z ≤ v.width i)
  (hk : K + 2 * E + 1 ≤ 2 ^ v.j)
include h hh hz hk

theorem base_le : BoundaryScale.base D z payload v.group ≤ v.box (K + p.groupRate + 5) := by
  have hl := v.log_width hi hz
  have hd := v.log_box (f.bits cur hi) hk
  let N := v.box (K + p.groupRate + 2)
  have hN : 2 ^ v.group ≤ N := v.box_mono (by omega)
  have hK : v.box K ≤ N := v.box_mono (by omega)
  have hd' : v.box 2 ≤ N := v.box_mono (by omega)
  have hv : 4 * (100 + v.stack + p.growth * v.j + v.blocks + v.height) ≤ N := h.four_span.trans hN
  have h' : BoundaryScale.base D z payload v.group ≤ N * 8 := by
    have := f.ports.trans hK
    have := f.height.trans hK
    unfold BoundaryScale.base
    rw [add_assoc 1 D.scheme.ℓ]
    omega
  rw [show K + p.groupRate + 5 = (K + p.groupRate + 2) + 3 by omega, v.box_add]
  exact h'.trans (Nat.mul_le_mul_left _ (v.pow_le_box 3))

theorem metadata_le : BoundaryScale.metadata D z payload v.group ≤ v.box (K + 2 * E + p.groupRate + 6) := by
  have hb := f.base_le cur hi h hh hz hk
  have hl := f.bits cur hi
  rw [BoundaryScale.metadata, add_assoc, show K + 2 * E + p.groupRate + 6 = (K + 2 * E + p.groupRate + 5) + 1 by omega]
  exact v.box_sum (hb.trans (v.box_mono (by omega))) (hl.trans (v.box_mono (by omega)))

end FrameBound
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Uniform applicability of a contraction and restoration phase -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {D : Template F} {Q : Layer F x y}
  {n m i B C E J K H d z payload : ℕ} {price : Prices F}

/-- First choose the overhead from the constant address costs, then
the coefficient of linear label growth, then the smallness exponent. -/
structure Admissible (p : Design δ) (s : Plan) (J K H E C : ℕ) : Prop where
  steps : p.steps = s.n + 1
  growth : p.growth = s.p
  gain : p.gain = s.v
  input : s.K * 2 ^ J ≤ p.overhead
  output : 2 ^ (J + H) ≤ p.overhead
  margin : K ≤ E
  factor : H * (K + 1) + 1 ≤ E
  additive : (K + p.groupRate + 5) * H ≤ E
  exponent : (K + 2 * E + p.groupRate + 6) * H ≤ C

namespace Current
variable (cur : v.Current s n m i E Q) (f : v.Passage Q D J)
  (data : v.FrameBound Q D payload K) (ok : Admissible p s J K H E C)
  (h : v.Fits n B C) (hi : i < v.j) (hk : K + 2 * E + 1 ≤ 2 ^ v.j)
include cur f data ok h hi hk

theorem requirements (hs : s.Fits) (unit : 0 < s.b) (overhead : 0 < s.K) (hm : n ≤ m) (hm' : m ≤ n ^ 2)
    (hz : 0 < z) (hsmall : (s.b * z) * s.D ^ s.c ≤ v.width i) (hbig : v.width i ≤ z * s.M)
    (hd : D.scheme.d ≤ d) (hslot : D.scheme.k = 0)
    (field : Nat.card F ≤ (Nat.clog 2 n) ^ B) (space : 16 * Nat.clog 2 n ≤ price.w) :
    Requirements D s (v.width i) (v.budget m i) z payload price v.group d H := by
  have axes : D.scheme.m + D.scheme.h ≤ Q.template.scheme.m + Q.template.scheme.h + J := by
    have := f.height
    have := f.upper
    omega
  have seats := cur.expand ok.input axes
  have addr := h.address hm' hi.le ((Nat.le_mul_of_pos_left _ overhead).trans seats)
  have small : s.K ≤ p.overhead := (Nat.le_mul_of_pos_right _ (by positivity)).trans ok.input
  have size : D.scheme.h ≤ v.blocks := by have := cur.height_le; have := f.height; omega
  have lower : z ≤ v.width i :=
    ((Nat.le_mul_of_pos_left _ unit).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by have := s.two hs; omega) _))).trans hsmall
  have hmeta := data.metadata_le cur hi.le h size lower hk
  refine ⟨h.one_le_budget hm hi.le, hz, hsmall, hbig, ?_,
    (small.trans v.overhead_le_group).trans Nat.lt_two_pow_self.le, ?_, hd, hslot, h.alphabet field, ?_, by omega⟩
  · have hh := cur.enough hi
    rw [ok.steps, add_mul, one_mul, ← f.height] at hh
    exact Nat.le_of_add_le_add_right hh
  · simpa only [Nat.cast_mul, mul_right_comm] using Levels.slack hi.le seats
  · refine (Nat.pow_le_pow_left hmeta H).trans ?_
    rw [← v.box_mul]
    exact ((v.box_mono ok.exponent).trans h.small).trans (cur.address.trans f.lower)

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Preservation of the round invariant through concentration and restoration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly Contraction

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan}
  {F : Type} [Field F] {x y : Wire} {D : Template F} {Q : Layer F x y}
  {n m i B C E J K H d z payload : ℕ} {price : Prices F}

namespace Current
variable (cur : v.Current s n m i E Q) (f : v.Passage Q D J) (data : v.FrameBound Q D payload K)
  (ok : Admissible p s J K H E C) (h : v.Fits n B C) (hi : i < v.j)
  (hk : K + 2 * E + 1 ≤ 2 ^ v.j) (hz : z ≤ v.width i)
  (result : Restored (x := x) (y := y) D s (v.width i) (v.budget m i) z payload price v.group H)

include cur f data ok h hi hk hz

private theorem restored_labels :
    result.next.template.scheme.ℓ + result.next.template.count ≤ E ^ (i + 1) * v.box E := by
  let a := E ^ i * v.box E
  have hE : 0 < E := by have := ok.factor; omega
  have hp : v.box E ≤ a := Nat.le_mul_of_pos_left _ (pow_pos hE _)
  have hf : D.scheme.h ≤ v.blocks := by have := f.height; have := cur.height_le; omega
  have hbase := data.base_le cur hi.le h hf hz hk
  have hb : BoundaryScale.base D z payload v.group ^ H ≤ a := by
    refine (Nat.pow_le_pow_left hbase H).trans ?_
    rw [← v.box_mul]
    exact (v.box_mono ok.additive).trans hp
  have hmeta : D.scheme.ℓ + D.count ≤ K * a + a :=
    data.labels.trans (Nat.add_le_add (Nat.mul_le_mul_left _ cur.labels) ((v.box_mono ok.margin).trans hp))
  calc
    _ ≤ H * (D.scheme.ℓ + D.count) + BoundaryScale.base D z payload v.group ^ H := result.labels
    _ ≤ H * (K * a + a) + a := Nat.add_le_add (Nat.mul_le_mul_left _ hmeta) hb
    _ = (H * (K + 1) + 1) * a := by ring
    _ ≤ E * a := Nat.mul_le_mul_right _ ok.factor
    _ = _ := by unfold a; rw [pow_succ]; ring

theorem advance : v.Current s n m (i + 1) E result.next where
  ready := by
    simpa only [budget, width, Design.width_succ, Design.budget_succ, ok.growth, ok.gain] using result.ready
  loopless := result.loopless
  address := (cur.address.trans f.lower).trans result.lower
  blocks := by
    have ht : p.steps * (i + 1) * v.group = p.steps * i * v.group + s.n * v.group + v.group := by rw [ok.steps]; ring
    have := cur.blocks
    have := f.height
    have := result.blocks
    omega
  seats := by
    have hw : result.next.template.scheme.m + result.next.template.scheme.h ≤
        Q.template.scheme.m + Q.template.scheme.h + (J + H) := by
      have := f.height
      have := f.upper
      have := result.seats
      omega
    simpa only [one_mul] using cur.expand (c := 1) (by rw [one_mul]; exact ok.output) hw
  ports := result.ports
  degree := result.degree
  volume := result.volume
  height := by
    have ht : Nat.clog 2 (v.width i) ≤ 1 + v.stack + p.growth * v.j :=
      (Nat.clog_mono_right _ (Nat.le_add_left _ 1)).trans (v.log_width hi.le le_rfl)
    have := cur.height_le
    have := f.height
    have := result.blocks
    have := result.height
    unfold span
    omega
  labels := cur.restored_labels f data ok h hi hk hz result

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Choosing a common round design and its label exponent -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
variable {δ : ℝ}

theorem Plan.choose_design (s : Plan) (J K H E₀ C₀ : ℕ) (hD : 8 ≤ s.D)
    (hv : 0 < s.v) (hp : 0 < s.p) (ratio : (s.p : ℝ) ≤ s.v * (1 + δ / 3)) :
    ∃ (p : Design δ) (E C : ℕ), Levels.Admissible p s J K H E C ∧ p.D = s.D ∧
      p.floor = s.floor ∧ E₀ ≤ E ∧ C₀ ≤ C ∧ s.D ≤ p.overhead := by
  have hm : 1 ≤ (s.M : ℝ) := by
    exact_mod_cast (show 1 ≤ s.M by unfold Plan.M; exact Nat.one_le_pow _ _ (by omega))
  have hden : 1 ≤ (s.M : ℝ) * (2 : ℝ) ^ s.p :=
    one_le_mul_of_one_le_of_one_le hm (one_le_pow₀ (by norm_num))
  let p : Design δ :=
    { D := s.D, steps := s.n + 1, gain := s.v, growth := s.p
      overhead := max s.D (max (s.K * 2 ^ J) (2 ^ (J + H))), floor := s.floor
      large := hD, steps_pos := by omega, gain_pos := hv, growth_pos := hp
      overhead_large := (show 2 ≤ s.D by omega).trans (le_max_left _ _), ratio := ratio
      floor_pos := by unfold Plan.floor; positivity
      floor_le := (one_div_le_one_div_of_le (by norm_num) hden).trans (by norm_num) }
  let E := max (max E₀ K) (max (H * (K + 1) + 1) ((K + p.groupRate + 5) * H))
  let C := max C₀ ((K + 2 * E + p.groupRate + 6) * H)
  refine ⟨p, E, C, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, le_max_right _ _⟩, rfl, rfl, ?_, le_max_left _ _, le_max_left _ _⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  all_goals unfold E; omega

theorem Design.small_exponent (p : Design δ) {C q : ℕ} (hq : 2 * C + 1 ≤ q)
    {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 1 / 2) (h : (p.groupRate + p.groupRate * q + 1 : ℕ) * a < β) :
    4 * a * (p.groupRate + C : ℕ) ≤ 1 := by
  have hg : 1 ≤ p.groupRate := by unfold Design.groupRate; have := p.overhead_large; omega
  have hn : 2 * (p.groupRate + C) ≤ p.groupRate + p.groupRate * q + 1 := by
    nlinarith only [Nat.mul_le_mul_left p.groupRate hq, Nat.mul_le_mul_right C hg]
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn : (_ : ℝ) ≤ _) ha.le
  push_cast at hh h ⊢
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Simultaneous cutoff for the chosen stage parameters -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels

open Filter

variable {δ : ℝ} {p : Design δ}

theorem Admissible.enlarge {s : Plan} {J K H E C D : ℕ}
    (h : Admissible p s J K H E C) (hd : C ≤ D) :
    Admissible p s J K H E D :=
  ⟨h.steps, h.growth, h.gain, h.input, h.output, h.margin, h.factor, h.additive, h.exponent.trans hd⟩

theorem funded_levels (p : Design δ) (M B C T₀ extra margin : ℕ)
    {a b ξ : ℝ} (hδ : δ ≤ 1) (ha : 0 < a) (ha' : a ≤ 1)
    (hb : 0 < b) (hb' : b ≤ 1) (hξ : 0 < ξ)
    (small : 4 * a * (p.groupRate + C : ℕ) ≤ 1) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ (Nat.clog 2 n : ℝ) ∧ 1 ≤ Real.log (Nat.clog 2 n) ∧
      ∃ v : Levels p M, v.Suits n T₀ a b ξ ∧ v.Fits n B C ∧
        margin ≤ 2 ^ v.j ∧ ((v.span + extra : ℕ) : ℝ) ≤ J * (Real.log (Nat.clog 2 n)) ^ 2 := by
  obtain ⟨J, hJ, span⟩ := eventual_span_log p M extra ha ha'
  refine ⟨J, hJ, ?_⟩
  filter_upwards [Design.levels p hδ T₀ M ha ha' hb hb' hξ,
      eventually_fits p M B C ha small, eventually_rounds p M ha margin, span,
      Shaving.tendsto_height.eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp Shaving.tendsto_height).eventually_ge_atTop 1]
    with n ex fit big bound hh hl
  obtain ⟨v, ok⟩ := ex
  exact ⟨hh, hl, v, ok, fit v T₀ b ξ hb' ok,
    (big v T₀ b ξ ok).trans Nat.lt_two_pow_self.le, bound v T₀ b ξ hb' ok⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Resources for the grouped input to local concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) (s : Plan)

def precision (B : ℕ) := (B + 2) * v.span + s.d + s.p
def binBits := 2 ^ (Template.Presents.Plan.depth s.D s.floor + 5 + 2)
def binFactor :=
  let t := Template.Presents.Plan.depth s.D s.floor
  let c := Template.Sheet.slots s.D
  2 ^ t * (1 + c + 32 * (s.D ^ 10 + (c + t)))

variable {v s} {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {n m i E B C a R : ℕ}
  (cur : v.Current s n m i E Q) (fit : v.Fits n B C)

theorem Fits.precision (fit : v.Fits n B C) (hs : s.d + s.p ≤ 2 ^ v.j) : v.precision s B ≤ v.box 1 := by
  have h := (Nat.mul_le_mul_right v.span (show B + 2 ≤ B + 4 by omega)).trans fit.span
  unfold Levels.precision box
  rw [one_mul, pow_succ]
  omega

include cur in
theorem Current.precision : Q.height ≤ v.precision s B := by
  have hx : v.span ≤ (B + 2) * v.span := Nat.le_mul_of_pos_left _ (by omega)
  exact cur.height.trans (Nat.add_le_add_right (Nat.add_le_add_right hx _) _)

include fit in
theorem Fits.field {t : ℕ} (ht : t ≤ (Nat.clog 2 n) ^ B) : t ≤ 2 ^ (v.precision s B) := by
  have hx : v.height ≤ v.span := Nat.le_add_left ..
  refine (ht.trans (Nat.pow_le_pow_left fit.height _)).trans ?_
  rw [← pow_mul, mul_comm v.height]
  apply Nat.pow_le_pow_right (by decide)
  unfold Levels.precision
  have := Nat.mul_le_mul (show B ≤ B + 2 by omega) hx
  omega

theorem width_precision (hi : i ≤ v.j) : v.width i ≤ 2 ^ (v.precision s B) := by
  rw [v.width_eq]
  apply Nat.pow_le_pow_right (by decide)
  have hs : v.stack + p.growth * i ≤ v.span := by
    have := Nat.mul_le_mul_left p.growth hi
    unfold span
    omega
  unfold precision
  have := Nat.le_mul_of_pos_left v.span (show 0 < B + 2 by omega)
  omega

variable (b : Q.template.Binning a s.D (v.width i) R s.floor)

include cur in
theorem Current.binBits : 2 ^ b.target.e ≤ binBits s := by
  rw [b.shape.2.2.2.2]
  unfold Levels.binBits
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (Nat.add_le_add_left cur.ports _) _)

include cur in
theorem Current.binLabel : b.target.ℓ ≤ binFactor s * (Q.template.scheme.ℓ + 1) := by
  have hd := b.nav_bound (by rw [cur.degree]; decide)
  have hn := (Nat.le_add_right b.target.d 1).trans (Nat.lt_two_pow_self.le.trans hd)
  have he : (2 : ℕ) ^ Q.template.scheme.e ≤ 32 := Nat.pow_le_pow_right (by decide) cur.ports
  let c := Template.Sheet.slots s.D
  let t := b.depth
  let a := 32 * (s.D ^ 10 + (c + t))
  rw [b.fields]
  calc
    _ ≤ 2 ^ t * (c + (Q.template.scheme.ℓ + a)) := by unfold a; gcongr
    _ ≤ 2 ^ t * ((1 + c + a) * (Q.template.scheme.ℓ + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [add_mul, mul_add, one_mul, mul_one]
      omega
    _ = _ := by rw [← mul_assoc]; rfl

include cur fit in
theorem Current.binSpace (hi : i ≤ v.j) (hm : m ≤ n ^ 2) {J w : ℕ}
    (hk : J + s.d + s.p + 1 ≤ 2 ^ v.j) (hw : 16 * Nat.clog 2 n ≤ w) :
    b.target.m + Q.height + J ≤ w := by
  have hy := cur.long fit hi hm
  have hs := fit.four_span.trans fit.group
  have hd := hk.trans ((Nat.pow_le_pow_right (by decide) v.rounds_le_group).trans fit.group)
  have ht := cur.height
  rw [b.shape.1]
  omega

theorem Passage.fromBin {D : Template F} {J : ℕ} (ha : a + v.group = Q.template.scheme.h)
    (hh : D.scheme.h = a) (lo : b.target.m ≤ D.scheme.m) (up : D.scheme.m ≤ b.target.m + J) :
    v.Passage Q D (1 + J) := by
  rw [b.shape.1] at lo up
  exact ⟨by omega, by omega, by omega⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Absorbing the grouped table and the fresh sphere data -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} {v : Levels p M} {s : Plan} {F : Type} [Field F] {x y : Wire}
  {Q : Layer F x y} {D : Template F} {n m i E B C a R J : ℕ}
  (cur : v.Current s n m i E Q) (fit : v.Fits n B C)
  (b : Q.template.Binning a s.D (v.width i) R s.floor)

def frameRate (s : Plan) (J : ℕ) := J * (binFactor s + 2) + 1

include cur fit in
theorem Current.fromBin (hs : s.d + s.p ≤ 2 ^ v.j) (ports : 2 ^ D.scheme.e ≤ J)
    (labels : D.scheme.ℓ + D.count ≤ J * (b.target.ℓ + 1 + v.precision s B)) :
    v.FrameBound Q D Q.height (frameRate s J) := by
  let k := binFactor s
  let r := J * (k + 2)
  let l := Q.template.scheme.ℓ + Q.template.count
  have hr : frameRate s J = r + 1 := rfl
  have ht := fit.precision hs
  have hJ : J ≤ r := Nat.le_mul_of_pos_right _ (by omega)
  have h₁ : 1 ≤ v.box 1 := v.le_box _
  have front : b.target.ℓ + 1 + v.precision s B ≤ (k + 2) * (l + v.box 1) := calc
    _ ≤ k * (Q.template.scheme.ℓ + 1) + 1 + v.box 1 := by gcongr; exact cur.binLabel b
    _ ≤ k * (l + v.box 1) + v.box 1 + v.box 1 := by gcongr; exact Nat.le_add_right ..
    _ ≤ _ := by rw [add_mul, two_mul]; omega
  rw [hr]
  refine ⟨(ports.trans (hJ.trans (Nat.le_succ _))).trans (v.le_box _),
    (cur.precision.trans ht).trans (v.box_mono (by omega)), ?_⟩
  calc
    _ ≤ J * (b.target.ℓ + 1 + v.precision s B) := labels
    _ ≤ J * ((k + 2) * (l + v.box 1)) := Nat.mul_le_mul_left _ front
    _ = r * l + r * v.box 1 := by rw [← mul_assoc, mul_add]
    _ ≤ (r + 1) * l + v.box r * v.box 1 :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.mul_le_mul_right _ (v.le_box _))
    _ = _ := by rw [← box_add]

include cur in
theorem Current.terminal (hi : i = v.j) :
    Q.Ready s.D v.finalWidth (8 * v.finalBudget m) s.floor ∧
      Q.template.scheme.h = v.remaining ∧
      2 ^ Q.template.scheme.m * 2 ^ v.remaining ≤ p.overhead ^ v.j * v.allocation m ∧
      Q.template.scheme.ℓ + Q.template.count ≤ v.box (E + E) := by
  subst i
  have hh : Q.template.scheme.h = v.remaining := by
    simpa only [Nat.sub_self, mul_zero, zero_mul, add_zero] using cur.left le_rfl
  refine ⟨?_, hh, ?_, cur.bits le_rfl⟩
  · simpa only [budget_final, width_eq, finalWidth] using cur.ready
  · simpa only [hh, pow_add] using cur.seats

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Common exponents for startup, grouping, contractions and the terminal step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

theorem Plan.assembly_design {δ : ℝ} (s : Plan) (J G H L B : ℕ) (hD : 8 ≤ s.D)
    (hv : 0 < s.v) (hp : 0 < s.p) (ratio : (s.p : ℝ) ≤ s.v * (1 + δ / 3)) :
    ∃ (p : Design δ) (E C q : ℕ),
      Levels.Admissible p s (1 + J) (Levels.frameRate s J) H E C ∧
      p.D = s.D ∧ p.floor = s.floor ∧ s.D ≤ p.overhead ∧
      15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide) ≤ E ∧ E ≤ C ∧
      (5 + 2 * E + p.groupRate + 6) * G ≤ C ∧ (E + E) * (L + 1) ≤ C ∧
      2 * C + 1 ≤ q ∧ C ≤ q * p.groupRate ∧ E ≤ q * p.groupRate := by
  obtain ⟨p, E, K, ok, degree, floor, start, _, overhead⟩ :=
    s.choose_design (1 + J) (Levels.frameRate s J) H
      (15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide)) 0 hD hv hp ratio
  let C := max (max K E) (max ((5 + 2 * E + p.groupRate + 6) * G) ((E + E) * (L + 1)))
  have hK : K ≤ C := (le_max_left ..).trans (le_max_left ..)
  have hE : E ≤ C := (le_max_right ..).trans (le_max_left ..)
  let q := 2 * C + 1
  have positive : 0 < p.groupRate := by unfold Design.groupRate; have := p.overhead_large; omega
  have cover : C ≤ q * p.groupRate :=
    (show C ≤ q by unfold q; omega).trans (Nat.le_mul_of_pos_right _ positive)
  exact ⟨p, E, C, q, ok.enlarge hK, degree, floor, overhead, start, hE,
    (le_max_left ..).trans (le_max_right ..), (le_max_right ..).trans (le_max_right ..),
    le_rfl, cover, hE.trans cover⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # A common scale for the first two operations of a round -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

def groupCoefficient (s : Plan) (J : ℕ) :=
  1000000 + s.D + 2 ^ Template.Presents.Plan.depth s.D s.floor + 2 * binBits s + binFactor s + J

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M)

def groupPayload (s : Plan) (B J payload : ℕ) := groupCoefficient s J + v.precision s B + 2 * payload

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Charging the restart to the common stage budget -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.BoundaryScale

open Assembly

variable {F : Type} [Field F] {x y : Wire} {δ : ℝ} {p : Design δ}

theorem budget {M : ℕ} (v : Levels p M) (D : Template F) (price : Prices F)
    {n m C q K R z payload : ℕ} {τ σ J : ℝ}
    (hK : 0 < K) (hh : 2 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n))
    (hJ : 1 ≤ J) (hτ : 0 ≤ τ) (hτσ : (K : ℝ) * τ ≤ σ) (hσ : σ ≤ 1)
    (hw : (price.W : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ τ)
    (wide : (price.w + price.w ^ price.power : ℕ) ≤ (Nat.clog 2 n) ^ R)
    (reserve : (7 + max R 1) * K ≤ M)
    (shortBase : (metadata D z payload v.group) ^ K ≤ v.box C)
    (hmeta : v.box C ≤ Nat.clog 2 n) (enough : C ≤ q * p.groupRate)
    (payloadBase : ((100 + D.scheme.h + payload + D.scheme.e + Nat.clog 2 (1 + z) : ℕ) : ℝ)
      ≤ J * (Real.log (Nat.clog 2 n)) ^ 2)
    (remain : v.remaining ≤ D.scheme.h)
    (seats : 2 ^ (D.scheme.m + D.scheme.h) ≤ p.overhead ^ v.j * v.allocation m) :
    let h : ℝ := Nat.clog 2 n
    let S := (short D z payload v.group price) ^ K
    let W := (2 * J) ^ K * (Real.log h) ^ (2 * K) * h ^ σ
    S ≤ 2 ^ K * (Nat.clog 2 n) ^ 2 ∧
      (S : ℝ) ≤ (2 : ℝ) ^ K * h ^ σ * (2 : ℝ) ^ (q * v.group) ∧
      (cost (x := copies x v.batch) (y := copies y v.batch) D z payload v.group price K : ℝ)
        ≤ W * v.expense h m (wd x + wd y) q := by
  let h : ℝ := Nat.clog 2 n
  let L := Real.log h
  let W := (2 * J) ^ K * L ^ (2 * K) * h ^ σ
  let S₀ := metadata D z payload v.group
  let E₀ := 100 + D.scheme.h + payload + D.scheme.e + Nat.clog 2 (1 + z)
  let S := short D z payload v.group price
  let A := long D z payload v.group price
  let E := outer D z payload price
  have h₁ : 1 ≤ h := (by norm_num : (1 : ℝ) ≤ 2).trans hh
  have hσ₀ : 0 ≤ σ := (mul_nonneg (by positivity) hτ).trans hτσ
  have hτ₁ : τ ≤ 1 :=
    (le_mul_of_one_le_left hτ (Nat.one_le_cast.mpr hK)).trans (hτσ.trans hσ)
  have hW₀ : 0 ≤ W := by unfold W; positivity
  have hW₁ : 1 ≤ W := by
    unfold W
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hl))
      (Real.one_le_rpow h₁ hσ₀)
  have hS₀ : 1 ≤ S₀ := Nat.succ_le_of_lt (by unfold S₀ metadata base; positivity)
  have hE₀ : 1 ≤ E₀ := by unfold E₀; omega
  have powers : (S : ℝ) ^ K ≤ (2 : ℝ) ^ K * h ^ σ * (S₀ : ℝ) ^ K := calc
    _ = ((S₀ : ℝ) + (price.W : ℝ)) ^ K := by unfold S short; push_cast; rfl
    _ ≤ (2 * (S₀ : ℝ)) ^ K * h ^ σ := power_with_routing (by exact_mod_cast hS₀) (by positivity)
      h₁ hτ hw hτσ
    _ = _ := by rw [mul_pow]; ring
  have hS₁ : (S₀ : ℝ) ^ K ≤ h := by
    unfold h
    exact_mod_cast shortBase.trans hmeta
  have hsmall : (S : ℝ) ^ K ≤ (2 : ℝ) ^ K * h ^ 2 := calc
    _ ≤ (2 : ℝ) ^ K * h ^ σ * h := mul_le_mul_of_nonneg_left hS₁ (by positivity) |>.trans' powers
    _ ≤ (2 : ℝ) ^ K * h * h := by
      have hσh : h ^ σ ≤ h := (Real.rpow_le_rpow_of_exponent_le h₁ hσ).trans_eq (Real.rpow_one _)
      gcongr
    _ = _ := by ring
  have hshort : (S : ℝ) ^ K ≤ (2 : ℝ) ^ K * h ^ σ * (2 : ℝ) ^ (q * v.group) :=
    powers.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast shortBase.trans (v.box_le_group_power enough)) (by positivity))
  have hσW : (2 : ℝ) ^ K * h ^ σ ≤ W := by
    unfold W
    have hfront : (2 : ℝ) ^ K ≤ (2 * J) ^ K := pow_le_pow_left₀ (by positivity) (by linarith) _
    have hfact := le_mul_of_one_le_right (by positivity : 0 ≤ (2 * J) ^ K) (one_le_pow₀ (n := 2 * K) hl)
    exact mul_le_mul_of_nonneg_right (hfront.trans hfact) (by positivity)
  have hA : (A : ℝ) ^ K ≤ h ^ M := by
    let r := max R 1
    have hp : h ≤ h ^ r := by
      simpa only [pow_one] using (pow_le_pow_right₀ h₁ (Nat.le_max_right R 1))
    have hq : h ^ R ≤ h ^ r := pow_le_pow_right₀ h₁ (Nat.le_max_left ..)
    have hs : (S₀ : ℝ) ≤ h :=
      (by exact_mod_cast Nat.le_self_pow (Nat.ne_of_gt hK) S₀ : (S₀ : ℝ) ≤ (S₀ : ℝ) ^ K).trans hS₁
    have hw' : (price.W : ℝ) ≤ h := hw.trans
      ((Real.rpow_le_rpow_of_exponent_le h₁ hτ₁).trans_eq (Real.rpow_one _))
    have ww : (price.w : ℝ) + (price.w : ℝ) ^ price.power ≤ h ^ R := by unfold h; exact_mod_cast wide
    have hl : (A : ℝ) ≤ 100 + h ^ r + 2 * h := by
      have w' := ww.trans hq
      change ((100 + price.w + price.w ^ price.power + (S₀ + price.W) : ℕ) : ℝ) ≤ _
      push_cast
      linarith only [w', hs, hw']
    have hr : 1 ≤ h ^ r := one_le_pow₀ h₁
    have hlong : (A : ℝ) ≤ h ^ (7 + r) := calc
      _ ≤ 103 * h ^ r := by nlinarith only [hl, hp, hr]
      _ ≤ h ^ 7 * h ^ r := mul_le_mul_of_nonneg_right
        ((by norm_num : (103 : ℝ) ≤ 2 ^ 7).trans (pow_le_pow_left₀ (by norm_num) hh _)) (by positivity)
      _ = _ := (pow_add ..).symm
    exact ((pow_le_pow_left₀ (by positivity) hlong K).trans_eq (pow_mul ..).symm).trans
      (pow_le_pow_right₀ h₁ reserve)
  have hEnd : (E : ℝ) ^ K ≤ W := calc
    _ = ((E₀ : ℝ) + (price.W : ℝ)) ^ K := by unfold E E₀ outer; push_cast; ring
    _ ≤ (2 * (E₀ : ℝ)) ^ K * h ^ σ := power_with_routing (by exact_mod_cast hE₀) (by positivity)
      h₁ hτ hw hτσ
    _ ≤ (2 * (J * L ^ 2)) ^ K * h ^ σ := by gcongr
    _ = _ := by unfold W; rw [← mul_assoc, mul_pow, ← pow_mul]
  have payment : cost (x := copies x v.batch) (y := copies y v.batch) D z payload v.group price K ≤
      2 ^ D.scheme.m * A ^ K + 2 ^ (D.scheme.m + D.scheme.h) * S ^ K + v.batch * (wd x + wd y) * E ^ K := by
    unfold cost
    rw [wd_copies, wd_copies, ← Nat.mul_add]
  refine ⟨by unfold h S at hsmall; exact_mod_cast hsmall, by exact_mod_cast hshort, ?_⟩
  apply v.phase_expense (h:=h) (W:=W) (by positivity) hW₀ remain seats payment
  · push_cast
    exact hA.trans (le_mul_of_one_le_left (by positivity) hW₁)
  · push_cast
    exact hshort.trans (mul_le_mul_of_nonneg_right hσW (by positivity))
  · exact_mod_cast hEnd

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.BoundaryScale
end

/-! # Charging grouping and local concentration to the same phase budget -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
open Contraction

variable {F : Type} [Field F]
  {x y : Wire} {δ : ℝ} {p : Design δ} {M n m i E B C J K q T₀ R : ℕ}
  {v : Levels p M} {s : Plan} {Q : Layer F (copies x v.batch) (copies y v.batch)}
  {price : Prices F} {a b ξ τ σ J₀ : ℝ}

theorem paid_group (cur : v.Current s n m i E Q) (ready : v.Suits n T₀ a b ξ)
    (fit : v.Fits n B C) (hi : i ≤ v.j)
    (margin : groupCoefficient s J + s.d + s.p + 2 * E + 6 ≤ 2 ^ v.j)
    (hK : 0 < K) (exponent : (5 + 2 * E + p.groupRate + 6) * K ≤ C)
    (hh : 2 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n))
    (hτ : 0 ≤ τ) (hτσ : (K : ℝ) * τ ≤ σ) (hσ : σ ≤ 1)
    (hw : (price.W : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ τ)
    (wide : (price.w + price.w ^ price.power : ℕ) ≤ (Nat.clog 2 n) ^ R)
    (reserve : (7 + max R 1) * K ≤ M) (enough : C ≤ q * p.groupRate) (hq : (p.groupRate * q : ℕ) * a ≤ b)
    (hJ : 0 ≤ J₀)
    (logSpan : ((v.span + s.d + s.p + 1 : ℕ) : ℝ) ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2) :
    let H := v.groupPayload s B J Q.height
    let h : ℝ := Nat.clog 2 n
    let W := (2 * ((groupCoefficient s J + B + 128 : ℕ) : ℝ) * (J₀ + 1)) ^ K * (Real.log h) ^ (2 * K) * h ^ σ
    (BoundaryScale.short Q.template 1 H v.group price) ^ K ≤ 2 ^ K * (Nat.clog 2 n) ^ 2 ∧
      (((BoundaryScale.short Q.template 1 H v.group price) ^ K : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (K + 2 * p.groupRate * q) * h ^ σ * (p.D * (v.finalWidth : ℝ)) ∧
      (BoundaryScale.cost (x := copies x v.batch) (y := copies y v.batch)
        Q.template 1 H v.group price K : ℝ) ≤ W * v.expense h m (wd x + wd y) q := by
  intro H h W
  have remain : v.remaining ≤ Q.template.scheme.h := by rw [cur.left hi]; exact Nat.le_add_right ..
  have seats : 2 ^ (Q.template.scheme.m + Q.template.scheme.h) ≤ p.overhead ^ v.j * v.allocation m :=
    cur.seats.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by have := p.overhead_large; omega) hi))
  have hm : v.FrameBound Q Q.template H 5 := by
    refine ⟨(Nat.pow_le_pow_right (by decide) cur.ports).trans (v.pow_le_box 5), ?_, by omega⟩
    have small : groupCoefficient s J ≤ v.box 1 := by unfold box; rw [one_mul, pow_succ]; omega
    have prec := fit.precision (s := s) (by omega)
    have old := (cur.precision (B := B)).trans prec
    have double : 2 * Q.height ≤ v.box 2 := by rw [two_mul]; exact v.box_sum old old
    exact (v.box_sum (v.box_sum small prec) double).trans (v.box_mono (by decide))
  have hz : 1 ≤ v.width i := by rw [v.width_eq]; exact Nat.one_le_pow _ _ (by decide)
  have metaPow : (BoundaryScale.metadata Q.template 1 H v.group) ^ K ≤ v.box C := calc
    _ ≤ (v.box (5 + 2 * E + p.groupRate + 6)) ^ K :=
      Nat.pow_le_pow_left (hm.metadata_le cur hi fit cur.height_le hz (by omega)) _
    _ ≤ _ := by rw [← v.box_mul]; exact v.box_mono exponent
  let c := groupCoefficient s J + B + 128
  have c₁ : 1 ≤ (c : ℝ) := by exact_mod_cast (show 1 ≤ c by unfold c; omega)
  have hc : 1 ≤ (c : ℝ) * (J₀ + 1) := one_le_mul_of_one_le_of_one_le c₁ (by linarith)
  have size : 100 + Q.template.scheme.h + H + Q.template.scheme.e + Nat.clog 2 (1 + 1) ≤ c * (v.span + s.d + s.p + 1) := by
    have hp := cur.ports
    have hq := cur.height
    have hx : Q.template.scheme.h ≤ v.span := cur.height_le.trans (by unfold span; omega)
    have ha := Nat.mul_le_mul_left B (show v.span ≤ v.span + s.d + s.p + 1 by omega)
    have hb := Nat.le_mul_of_pos_right (groupCoefficient s J) (show 0 < v.span + s.d + s.p + 1 by omega)
    rw [show Nat.clog 2 (1 + 1) = 1 by decide]
    unfold H groupPayload Levels.precision c
    simp only [add_mul]
    omega
  have outer : ((100 + Q.template.scheme.h + H + Q.template.scheme.e + Nat.clog 2 (1 + 1) : ℕ) : ℝ) ≤
      ((c : ℝ) * (J₀ + 1)) * (Real.log (Nat.clog 2 n)) ^ 2 := calc
    _ ≤ (c : ℝ) * ((v.span + s.d + s.p + 1 : ℕ) : ℝ) := by exact_mod_cast size
    _ ≤ (c : ℝ) * ((J₀ + 1) * (Real.log (Nat.clog 2 n)) ^ 2) := mul_le_mul_of_nonneg_left
      (logSpan.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (by positivity)
    _ = _ := (mul_assoc ..).symm
  obtain ⟨few, gate, paid⟩ := BoundaryScale.budget (x:=x) (y:=y) v Q.template price hK hh hl hc hτ hτσ hσ
    hw wide reserve metaPow fit.small enough outer remain seats
  refine ⟨few, ?_, ?_⟩
  · calc
      _ ≤ _ := gate
      _ ≤ (2 : ℝ) ^ K * h ^ σ * ((2 : ℝ) ^ (2 * p.groupRate * q) * (v.finalWidth : ℝ)) :=
        mul_le_mul_of_nonneg_left (ready.group_power_le_width hq) (by positivity)
      _ = (2 : ℝ) ^ (K + 2 * p.groupRate * q) * h ^ σ * (v.finalWidth : ℝ) := by rw [pow_add]; ring
      _ ≤ _ := by
        have hd : (1 : ℝ) ≤ p.D := by exact_mod_cast (show 1 ≤ p.D by have := p.large; omega)
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hd) (by positivity)
  · simpa only [W, h, c, mul_assoc] using paid

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end

/-! # Exact restart and its quantitative guarantee at the chosen levels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current

open Assembly Contraction

variable {F k : Type} [Field F] [Fintype F] [Field k] [Algebra k F]
  {x y : Wire} {δ : ℝ} {p : Design δ} {M n m i E B C J K H d q T₀ z R : ℕ}
  {v : Levels p M} {s : Plan} {Q : Layer F (copies x v.batch) (copies y v.batch)}
  {D : Template F} {price : Prices F} {a b ξ τ σ J₀ : ℝ}

theorem paid_restart (cur : v.Current s n m i E Q) (ready : v.Suits n T₀ a b ξ)
    (fit : v.Fits n B C) (f : v.Passage Q D J) (data : v.FrameBound Q D Q.height K)
    (ok : Admissible p s J K H E C) (hi : i < v.j) (hk : K + 2 * E + 1 ≤ 2 ^ v.j)
    (hK : 0 < H) (overhead : 0 < s.K) (hz : z ≤ v.width i)
    (hs : Requirements D s (v.width i) (v.budget m i) z Q.height price v.group d H)
    (restart : Restarts k s d H)
    (hh : 2 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n))
    (hτ : 0 ≤ τ) (hτσ : (H : ℝ) * τ ≤ σ) (hσ : σ ≤ 1)
    (hw : (price.W : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ τ)
    (wide : (price.w + price.w ^ price.power : ℕ) ≤ (Nat.clog 2 n) ^ R)
    (reserve : (7 + max R 1) * H ≤ M) (enough : C ≤ q * p.groupRate) (hq : (p.groupRate * q : ℕ) * a ≤ b)
    (hJ : 0 ≤ J₀)
    (logSpan : ((v.span + s.d + s.p + 1 : ℕ) : ℝ) ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2) :
    let h : ℝ := Nat.clog 2 n
    let W := (2 * ((K + 2 : ℕ) : ℝ) * (J₀ + 1)) ^ H * (Real.log h) ^ (2 * H) * h ^ σ
    ∃ result : Restored (x := copies x v.batch) (y := copies y v.batch)
        D s (v.width i) (v.budget m i) z Q.height price v.group H,
      v.Current s n m (i + 1) E result.next ∧
      result.keys.card ≤ 2 ^ H * (Nat.clog 2 n) ^ 2 ∧
      (((BoundaryScale.short D z Q.height v.group price) ^ H : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (H + 2 * p.groupRate * q) * h ^ σ * (p.D * (v.finalWidth : ℝ)) ∧
      (BoundaryScale.cost (x := copies x v.batch) (y := copies y v.batch)
        D z Q.height v.group price H : ℝ) ≤ W * v.expense h m (wd x + wd y) q := by
  obtain ⟨result⟩ := restart F (x := copies x v.batch) (y := copies y v.batch)
    D (v.width i) (v.budget m i) z Q.height price v.group hs
  have hD : D.scheme.h ≤ v.blocks := by
    have := f.height
    have := cur.height_le
    omega
  have hremain : v.remaining ≤ D.scheme.h := by
    have hstep : v.group ≤ p.steps * (v.j - i) * v.group :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos p.steps_pos (Nat.sub_pos_of_lt hi))
    have left := cur.left hi.le
    have ht := f.height
    omega
  have axes : D.scheme.m + D.scheme.h ≤ Q.template.scheme.m + Q.template.scheme.h + J := by
    have := f.height
    have := f.upper
    omega
  have seats : 2 ^ (D.scheme.m + D.scheme.h) ≤ p.overhead ^ v.j * v.allocation m :=
    (Nat.le_mul_of_pos_left _ overhead).trans ((cur.expand ok.input axes).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by have := p.overhead_large; omega) hi)))
  have metaPow : (BoundaryScale.metadata D z Q.height v.group) ^ H ≤ v.box C := calc
    _ ≤ (v.box (K + 2 * E + p.groupRate + 6)) ^ H := Nat.pow_le_pow_left (data.metadata_le cur hi.le fit hD hz hk) _
    _ ≤ _ := by rw [← v.box_mul]; exact v.box_mono ok.exponent
  let c : ℝ := ((K + 2 : ℕ) : ℝ) * (J₀ + 1)
  have hc : 1 ≤ c := by
    have hc₁ : (1 : ℝ) ≤ (K + 2 : ℕ) := by exact_mod_cast (show 1 ≤ K + 2 by omega)
    unfold c
    exact one_le_mul_of_one_le_of_one_le hc₁ (by linarith)
  have hlog := v.log_width hi.le hz
  have hsmall : 100 + D.scheme.h + Nat.clog 2 (1 + z) ≤ v.span + 1 := by
    unfold span
    omega
  have hsp : v.j + 1 ≤ v.span := by
    have ht : v.j ≤ p.growth * v.j := Nat.le_mul_of_pos_left _ p.growth_pos
    unfold span
    omega
  have hd : D.scheme.e ≤ K * v.span := by
    apply le_trans _ (Nat.mul_le_mul_left K hsp)
    exact (Nat.pow_le_pow_iff_right (by decide)).mp data.ports
  have hsize : 100 + D.scheme.h + Q.height + D.scheme.e + Nat.clog 2 (1 + z) ≤
    (K + 2) * (v.span + s.d + s.p + 1) := calc
    _ ≤ (v.span + 1) + (v.span + s.d + s.p) + K * v.span := by
      have := cur.height
      omega
    _ ≤ (v.span + s.d + s.p + 1) + (v.span + s.d + s.p + 1) + K * (v.span + s.d + s.p + 1) :=
      Nat.add_le_add (Nat.add_le_add (by omega) (by omega))
        (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring
  have hExt : ((100 + D.scheme.h + Q.height + D.scheme.e + Nat.clog 2 (1 + z) : ℕ) : ℝ) ≤
      c * (Real.log (Nat.clog 2 n)) ^ 2 := calc
    _ ≤ ((K + 2 : ℕ) : ℝ) * ((v.span + s.d + s.p + 1 : ℕ) : ℝ) := by exact_mod_cast hsize
    _ ≤ ((K + 2 : ℕ) : ℝ) * ((J₀ + 1) * (Real.log (Nat.clog 2 n)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact logSpan.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ = _ := by unfold c; ring
  obtain ⟨few, gate, paid⟩ := BoundaryScale.budget (x:=x) (y:=y) v D price hK hh hl hc hτ hτσ hσ
    hw wide reserve metaPow fit.small enough hExt hremain seats
  refine ⟨result, cur.advance f data ok fit hi hk hz result, result.few.trans few, ?_, ?_⟩
  · calc
      _ ≤ _ := gate
      _ ≤ (2 : ℝ) ^ H * (Nat.clog 2 n : ℝ) ^ σ * ((2 : ℝ) ^ (2 * p.groupRate * q) * (v.finalWidth : ℝ)) :=
        mul_le_mul_of_nonneg_left (ready.group_power_le_width hq) (by positivity)
      _ = (2 : ℝ) ^ (H + 2 * p.groupRate * q) * (Nat.clog 2 n : ℝ) ^ σ * (v.finalWidth : ℝ) := by
        rw [pow_add]; ring
      _ ≤ _ := by
        have hd : (1 : ℝ) ≤ p.D := by exact_mod_cast (show 1 ≤ p.D by have := p.large; omega)
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hd) (by positivity)
  · simpa only [c, Nat.cast_add, Nat.cast_ofNat, mul_assoc] using paid

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Current
end

/-! # Terminal bank capacity at the last round -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) (s : Plan)
  {F : Type} [Field F] {x y : Wire}

def depth := s.d + (v.stack + p.growth * v.j)
def capacity (m : ℕ) (Q : Layer F x y) :=
  2 ^ Q.template.scheme.m + ⌊8 * v.finalBudget m / (s.floor * v.finalWidth)⌋₊*2 ^ (Q.template.scheme.e + v.depth s)

theorem depth_eq : 2 ^ v.depth s = s.D * v.finalWidth := pow_add ..

namespace Current
variable {v s} {Q : Layer F x y} {n m E : ℕ} (h : v.Current s n m v.j E Q)
local notation "S" => Q.template.scheme
include h

theorem fits_terminal (i : Q.State) :
    Assembly.Terminal.Fits S (Q.data i).1 (v.capacity s m Q) (v.depth s) ∧
    Assembly.Terminal.Neutral S (Q.data i).1 :=
  (h.terminal rfl).1.terminal (by unfold Plan.floor Plan.M Plan.D; positivity)
    (by unfold finalWidth; positivity) (v.depth_eq s).ge le_rfl i

theorem capacity_le :
    (v.capacity s m Q : ℝ) ≤ (2 : ℝ) ^ Q.template.scheme.m + (256 * s.D / s.floor) * v.finalBudget m := by
  have hf : 0 < s.floor := by unfold Plan.floor Plan.M Plan.D; positivity
  have hT : 0 < (v.finalWidth : ℝ) := by unfold finalWidth; positivity
  have hL : 0 ≤ v.finalBudget m := by unfold finalBudget; positivity
  have he : (2 : ℝ) ^ Q.template.scheme.e ≤ 32 := by
    exact_mod_cast (show (2 : ℕ) ^ Q.template.scheme.e ≤ 32 from Nat.pow_le_pow_right (by decide) h.ports)
  rw [capacity, pow_add, v.depth_eq]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  apply add_le_add_right
  calc
    _ ≤ (8 * v.finalBudget m / (s.floor * v.finalWidth)) * (32 * ((s.D : ℝ) * v.finalWidth)) := by
      gcongr
      exact Nat.floor_le (by positivity)
    _ = _ := by field_simp; ring

theorem terminal_height :
    max Q.height (Assembly.Terminal.height S (v.depth s)) ≤ v.span + s.d + s.p := by
  apply max_le h.height
  unfold Assembly.Terminal.height depth span
  have := h.ready.1
  have := h.ports
  have := h.height_le
  omega

theorem terminal_space {B C w : ℕ} (fit : v.Fits n B C) (hm : m ≤ n ^ 2)
    (hs : s.d + s.p ≤ 2 ^ v.j) (hw : 16 * Nat.clog 2 n ≤ w) :
    1 ≤ Q.template.scheme.m ∧ Q.template.scheme.m + (Q.template.scheme.d + 1) ≤ w ∧
      2 ^ (Q.template.scheme.d + 1) * ((max Q.height (Assembly.Terminal.height S (v.depth s)) + 1)*
        (2 ^ Q.template.scheme.m + 2 ^ Q.template.scheme.m)) < 2 ^ w := by
  let t := max Q.height (Assembly.Terminal.height S (v.depth s))
  have h₀ := h.long fit le_rfl hm
  have h₁ := fit.four_span.trans fit.group
  have h₂ := hs.trans ((Nat.pow_le_pow_right (by decide) v.rounds_le_group).trans fit.group)
  have hv : 100 ≤ v.span := by unfold span; omega
  have ht : t ≤ v.span + s.d + s.p := h.terminal_height
  have hd := h.degree
  have hm := h.address
  refine ⟨by omega, by omega, ?_⟩
  have key : Q.template.scheme.d + 1 + (t + (Q.template.scheme.m + 1)) < w := by omega
  refine lt_of_le_of_lt ?_ (Nat.pow_lt_pow_right (by decide : 1 < 2) key)
  rw [pow_add 2 (Q.template.scheme.d + 1), pow_add 2 t, pow_succ 2 Q.template.scheme.m, ← Nat.mul_two]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ Nat.lt_two_pow_self)

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end
