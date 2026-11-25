import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads
import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage
import OAI.LinearAlgebra.MatrixExponent.Packing.Beat

/-! # The dyadic banks and their child channels fit the sorting range -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly
variable {F : Type} [Field F] {x y : Wire} {T : Template F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r b u v z payload d B K H : ℕ} {σ : ℝ}

private theorem bank_size (m n h w : ℕ) (hm : 2 * n + h + 4 ≤ m) (hw : 2 * m ≤ w) :
    2 ^ (n + 1) * ((h + 1) * (2 ^ m + 2 ^ (m + (n + 1)))) < 2 ^ w := by
  have hx : 2 ^ m + 2 ^ (m + (n + 1)) ≤ 2 ^ (m + (n + 1) + 1) := by
    rw [pow_succ, Nat.mul_two]
    exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)) _
  calc
    _ ≤ 2 ^ (n + 1) * (2 ^ h * 2 ^ (m + (n + 1) + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul Nat.lt_two_pow_self hx)
    _ = 2 ^ ((n + 1) + (h + (m + (n + 1) + 1))) := by rw [← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

theorem fanout (h : Input A L P p r b u v z payload d B K H σ) :
    2 ^ (r + 1) * ((payload + 1) * (2 ^ T.scheme.m + 2 ^ (T.scheme.m + (r + 1)))) < 2 ^ p.w := by
  apply bank_size _ _ _ _ _ h.upper
  have hs : short A r z payload ≤ T.scheme.m :=
    (Nat.le_self_pow h.positive.ne' _).trans h.small
  have hj := h.group
  have ha := Nat.two_pow_pos A.k
  have hb := Nat.two_pow_pos A.e
  have hc := Nat.two_pow_pos T.scheme.e
  have hr : r < 2 ^ r := Nat.lt_two_pow_self
  unfold short base at hs
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Common bounds on the widths and counters in both phases -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r b u v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r b u v z payload d B K H σ)
  (q : (frame A L u z payload Δ C P).state)

include h in
theorem size_bound (j : q.val.q.core.post.toPresentation.BorderSpan) :
    q.val.q.core.post.toPresentation.borderWidth j ≤ B * z := by
  let s := q.val.q.core.post
  let t := q.val.G.units.place j.val.1
  have hu : (s.atBlock t).peer 0 j.val.2 = none := by
    have he := j.property.2
    rw [s.vertex_eq] at he
    exact Option.map_eq_none_iff.mp he
  have hh : s.toPresentation.borderWidth j = (s.atBlock t).width 0 j.val.2 := by
    rw [Scheme.Presentation.borderWidth, s.vertex_eq]
    rfl
  have hs : s.toPresentation.borderWidth j ≤ q.val.G.tetherLoad t := by
    rw [hh, ← s.exterior_volume]
    unfold Pattern.volume
    apply le_trans _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j.val.2))
    simp [hu]
  refine hs.trans ?_
  have hl := (q.val.G.core_le_load t.1 t.2).trans ((q.property.1.bounded.2.2 t.1 t.2).trans h.ceiling)
  have he : (q.val.G.tetherLoad t : ℝ) ≤ B * (z : ℝ) := (le_add_of_nonneg_right (by positivity)).trans hl
  exact_mod_cast he

def precision (z B g : ℕ) := Nat.clog 2 (B * g * B * z + 1)

variable (g : ℕ)

include h in
theorem count_bound {m : ℕ} (hb' : m ≤ B) :
    (m : ℝ) * (g * P.load) < 2 ^ (precision z B g) := by
  have hn : (B * g * B) * z < 2 ^ (precision z B g) := Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)
  have hm : (m : ℝ) ≤ B := Nat.cast_le.mpr hb'
  calc
    _ ≤ (B : ℝ) * ((g : ℝ) * (B * z)) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left h.ceiling (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans h.load)) (Nat.cast_nonneg _)
    _ = ((B * g * B) * z : ℕ) := by simp only [Nat.cast_mul, mul_assoc]
    _ < _ := by exact_mod_cast hn

variable {a z' : ℕ} (G : HostNet F q.val.L a z')

include h in
theorem valid_of_charge (hmass : G.mass ≤ q.val.L.cap) (bound : ∀ v i, G.load v i ≤ g * P.load) :
    (Template.Meter.bounded (precision z B g) (1 / (L.denom : ℝ)) (1 / (2 : ℝ) ^ L.discount)).Valid G := by
  have he := q.property.1
  have hscale : g * P.load < q.val.L.scale * (2 : ℝ) ^ (precision z B g) := by
    rw [he.scale, one_div_mul_eq_div, lt_div_iff₀ (Nat.cast_pos.mpr h.denom)]
    exact (mul_comm _ _).trans_lt (count_bound h g h.scale)
  have hrate : (2 : ℝ) ^ q.val.L.discount * (g * P.load) < 2 ^ (precision z B g) := by
    simpa only [he.discount, Nat.cast_pow, Nat.cast_ofNat] using count_bound h g h.discount
  have hm := Template.Meter.valid_of_charge (G) (precision z B g) _ hmass bound hscale hrate (by
      intro j
      obtain ⟨u, _, hu⟩ := he.charge j
      exact ⟨u, hu⟩)
  change (Template.Meter.bounded _ q.val.L.scale (1 / (2 : ℝ) ^ q.val.L.discount)).Valid G at hm
  rw [he.scale, he.discount] at hm
  exact hm

include h in
theorem charges (bound : ∀ v i, G.load v i ≤ g * P.load) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ t, δ ≤ q.val.L.scale * q.val.L.charge t) ∧
      ∀ v i, G.load v i ≤ (B * g * B : ℕ) * δ := by
  have hd : (0 : ℝ) < L.denom := Nat.cast_pos.mpr h.denom
  refine ⟨(z : ℝ) / L.denom, div_pos (Nat.cast_pos.mpr h.zpos) hd, ?_, ?_⟩
  · intro t
    obtain ⟨n, hn, hq⟩ := q.property.1.charge t
    rw [hq, q.property.1.scale, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hn) hd.le
  · intro v i
    refine ((bound v i).trans (mul_le_mul_of_nonneg_left h.ceiling (Nat.cast_nonneg _))).trans ?_
    rw [← mul_div_assoc, le_div_iff₀ hd, Nat.cast_mul, Nat.cast_mul]
    have hpos : 0 ≤ (g : ℝ) * (B * z) := by positivity
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h.scale) hpos).trans_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Parameters for uniform bounds during contractions with a fixed border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing
export BatchDescent.Phase (Poly)
namespace Poly
export MatrixExponent.BatchDescent.Phase.Poly (const of_le pow_sum)
end Poly

structure Case (k : Type) [Field k] (b d B : ℕ) where
  F : Type
  [field : Field F]
  [finite : Fintype F]
  [alg : Algebra k F]
  x : Wire
  y : Wire
  T : Template F
  A : Attachment T
  L : BorderLimit F x y
  P : Bound
  p : Prices F
  r : ℕ
  u : ℕ
  v : ℕ
  z : ℕ
  payload : ℕ
  K : ℕ
  H : ℕ
  σ : ℝ
  h : Input A L P p r b u v z payload d B K H σ

attribute [instance] Case.field Case.finite Case.alg

namespace Case
variable {k : Type} [Field k] {b d B : ℕ} (i : Case k b d B)
local notation "I" => Case k b d B

abbrev m := i.T.scheme.m
abbrev height := i.T.scheme.h
abbrev a := i.height - i.r
abbrev n := i.height - i.a
abbrev base := Contraction.base i.A i.r i.z i.payload
abbrev short := Contraction.short i.A i.r i.z i.payload
abbrev block := i.short + i.p.W
abbrev outer := 100 + i.payload + i.p.W
abbrev long := 100 + i.p.w + i.p.w ^ i.p.power + i.p.W + i.short

theorem n_eq : i.n = i.r := Nat.sub_sub_self i.h.group
theorem positive : 0 < i.v := i.h.zpos.trans_le i.h.vpos

private theorem nonneg : 0 ≤ 2 ^ i.r ∧ 0 ≤ 2 ^ i.A.k ∧ 0 ≤ 2 ^ i.A.e ∧ 0 ≤ 2 ^ i.T.scheme.e :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem base_two : 2 ≤ i.base := by unfold base Contraction.base; have := i.nonneg; omega
theorem base_short : i.base ≤ i.short := by unfold short Contraction.short base; omega
theorem short_block : i.short ≤ i.block := Nat.le_add_right ..
theorem outer_block : i.outer ≤ i.block := by
  unfold outer block short Contraction.short Contraction.base
  have := i.nonneg
  omega
theorem block_long : i.block ≤ i.long := by unfold block long; have := Nat.zero_le (i.p.w ^ i.p.power); omega
theorem short_two : 2 ≤ i.short := i.base_two.trans i.base_short
theorem block_two : 2 ≤ i.block := i.short_two.trans i.short_block
theorem outer_two : 2 ≤ i.outer := by unfold outer; omega
theorem long_two : 2 ≤ i.long := i.block_two.trans i.block_long

abbrev Base (f : I → ℕ) := Poly base f
abbrev Short (f : I → ℕ) := Poly short f
abbrev Block (f : I → ℕ) := Poly block f
abbrev Outer (f : I → ℕ) := Poly outer f
abbrev Long (f : I → ℕ) := Poly long f

variable {f : Case k b d B → ℕ}

theorem Base.short (h : Base f) : Short f := h.grow base_short
theorem Short.block (h : Short f) : Block f := h.grow short_block
theorem Outer.block (h : Outer f) : Block f := h.grow outer_block
theorem Block.long (h : Block f) : Long f := h.grow block_long
theorem Short.long (h : Short f) : Long f := h.block.long

theorem base_const (c : ℕ) : Base (fun _ : I => c) := Poly.const base_two c
theorem short_const (c : ℕ) : Short (fun _ : I => c) := Poly.const short_two c
theorem block_const (c : ℕ) : Block (fun _ : I => c) := Poly.const block_two c
theorem outer_const (c : ℕ) : Outer (fun _ : I => c) := Poly.const outer_two c
theorem long_const (c : ℕ) : Long (fun _ : I => c) := Poly.const long_two c

theorem blocks : Base (fun i : I => 2 ^ i.r) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem levels : Base (fun i : I => i.height) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base height; have := i.nonneg; omega)
theorem units : Base (fun i : I => Nat.clog 2 (1 + i.z)) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem stations : Base (fun i : I => 2 ^ i.A.k) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem ports : Base (fun i : I => 2 ^ i.A.e) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem spans : Base (fun i : I => 2 ^ i.T.scheme.e) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem lengths : Base (fun i : I => Nat.clog 2 (1 + i.T.scheme.ℓ + i.A.ℓ)) :=
  Poly.of_le base_two (fun i => by unfold base Contraction.base; have := i.nonneg; omega)
theorem counters : Short (fun i : I => i.T.count) :=
  Poly.of_le short_two (fun i => by unfold short Contraction.short; omega)
theorem bits : Short (fun i : I => i.T.scheme.ℓ) :=
  Poly.of_le short_two (fun i => by unfold short Contraction.short; omega)
theorem labels : Short (fun i : I => i.A.ℓ) :=
  Poly.of_le short_two (fun i => by unfold short Contraction.short; omega)
theorem price : Outer (fun i : I => i.p.W) := Poly.of_le outer_two (fun _ => Nat.le_add_left ..)
theorem loads : Outer (fun i : I => i.payload) := Poly.of_le outer_two (fun i => by unfold outer; omega)
theorem world : Long (fun i : I => i.p.w) :=
  Poly.of_le long_two (fun i => by unfold long; have := Nat.zero_le (i.p.w ^ i.p.power); omega)
theorem power : Long (fun i : I => i.p.w ^ i.p.power) := Poly.of_le long_two (fun i => by unfold long; omega)
theorem hosts : Long (fun i : I => i.m) := world.mono fun i => (Nat.le_mul_of_pos_left _ (by decide)).trans i.h.upper
theorem groups : Base (fun i : I => i.a) := levels.mono fun _ => Nat.sub_le ..
theorem tiles : Base (fun i : I => 2 ^ i.n) := by simpa only [n_eq] using (blocks : Base (fun i : I => _))
theorem slots : Base (fun i : I => 2 ^ i.T.scheme.d) :=
  (base_const (2 ^ d)).mono fun i => Nat.pow_le_pow_right (by decide) i.h.degree

end Case
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# Charges on host addresses and short block records

Multiplication by a short quantity is allowed in both terms of the
budget. Multiplication by the world size is confined to the first.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
variable {κ : Type} [Field κ] {b d B : ℕ}
local notation "I" => Case κ b d B

def Mixed (j f : I → ℕ) : Prop :=
  ∃ k : ℕ, ∀ i, f i ≤ 2 ^ (j i) * i.long ^ k + 2 ^ (j i + i.height) * i.block ^ k

abbrev Cost (f : I → ℕ) := Mixed m f
abbrev Row (f : I → ℕ) := Mixed (fun _ => 0) f

variable {j f g n : Case κ b d B → ℕ}

namespace Mixed

theorem mono (h : Mixed j f) (hg : ∀ i, g i ≤ f i) : Mixed j g :=
  let ⟨k, hk⟩ := h
  ⟨k, fun i => (hg i).trans (hk i)⟩

theorem add (h : Mixed j f) (h' : Mixed j g) : Mixed j (fun i => f i + g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'
  refine ⟨max l k + 1, fun i => (Nat.add_le_add (hl i) (hk i)).trans ?_⟩
  rw [add_add_add_comm, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.long_two ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.block_two ..))

theorem mul (h : Mixed j f) (h' : Block g) : Mixed j (fun i => f i * g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'.bound
  refine ⟨l + k, fun i => (Nat.mul_le_mul (hl i) (hk i)).trans ?_⟩
  simp only [add_mul, mul_assoc, pow_add]
  gcongr
  exact i.block_long

theorem left (h : Mixed j f) (h' : Block g) : Mixed j (fun i => g i * f i) :=
  (h.mul h').mono fun _ => le_of_eq (mul_comm ..)

theorem scale (h : Mixed j f) (k : ℕ) : Mixed j (fun i => k * f i) := h.left (block_const k)

theorem long (j : I → ℕ) (h : Long f) : Mixed j (fun i => 2 ^ (j i) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_right ..)⟩

theorem short (j : I → ℕ) (h : Block f) : Mixed j (fun i => 2 ^ (j i + i.height) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_left ..)⟩

end Mixed

theorem Long.row (h : Long f) : Row f := by
  simpa only [pow_zero, one_mul] using Mixed.long (fun _ => 0) h

theorem Block.blocks (h : Block f) : Row (fun i => 2 ^ i.height * f i) := by
  simpa only [zero_add] using Mixed.short (fun _ => 0) h

theorem Block.groups (h : Block f) : Row (fun i => 2 ^ i.a * f i) :=
  h.blocks.mono (fun i => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)))

theorem Row.hosts (h : Row f) : Cost (fun i => 2 ^ i.m * f i) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun i => ?_⟩
  simpa only [pow_zero, one_mul, zero_add, mul_add, ← mul_assoc, ← pow_add] using Nat.mul_le_mul_left (2 ^ i.m) (hk i)

theorem Row.expand (h : Row f) (h' : Block (fun i => 2 ^ n i)) :
    Cost (fun i => 2 ^ (i.m + n i) * f i) := by
  simpa only [pow_add, mul_assoc] using Row.hosts (h.left h')

theorem Row.cost (h : Row f) : Cost f :=
  h.hosts.mono fun _ => Nat.le_mul_of_pos_left _ (by positivity)

/-- Payload transfer can pay a separate charge per exterior bit. -/
def Total (f : I → ℕ) : Prop :=
  ∃ k : ℕ, ∀ i, f i ≤ size (x := i.x) (y := i.y) i.A i.p i.r i.z i.payload k

theorem Cost.total (h : Cost f) : Total f :=
  let ⟨k, hk⟩ := h
  ⟨k, fun i => (hk i).trans (Nat.le_add_right ..)⟩

theorem Outer.total (h : Outer f) : Total (fun i => (wd i.x + wd i.y) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_left ..)⟩

theorem Total.mono (h : Total f) (hg : ∀ i, g i ≤ f i) : Total g :=
  let ⟨k, hk⟩ := h
  ⟨k, fun i => (hg i).trans (hk i)⟩

theorem Total.add (h : Total f) (h' : Total g) : Total (fun i => f i + g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'
  refine ⟨max l k + 1, fun i => (Nat.add_le_add (hl i) (hk i)).trans ?_⟩
  have aux (s a : ℕ) (hs : 2 ≤ s) := Nat.mul_le_mul_left a (Poly.pow_sum hs l k)
  have h₁ := aux _ (2 ^ i.m) i.long_two
  have h₂ := aux _ (2 ^ (i.m + i.height)) i.block_two
  have h₃ := aux _ (wd i.x + wd i.y) i.outer_two
  simp only [mul_add] at h₁ h₂ h₃
  change (2 ^ i.m * i.long ^ l + 2 ^ (i.m + i.height) * i.block ^ l + (wd i.x + wd i.y) * i.outer ^ l) +
    (2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.height) * i.block ^ k + (wd i.x + wd i.y) * i.outer ^ k) ≤
    2 ^ i.m * i.long ^ _ + 2 ^ (i.m + i.height) * i.block ^ _ + (wd i.x + wd i.y) * i.outer ^ _
  omega

theorem Total.mul (h : Total f) (h' : Outer g) : Total (fun i => f i * g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'.bound
  refine ⟨l + k, fun i => (Nat.mul_le_mul (hl i) (hk i)).trans ?_⟩
  change (2 ^ i.m * i.long ^ l + 2 ^ (i.m + i.height) * i.block ^ l + (wd i.x + wd i.y) * i.outer ^ l) * i.outer ^ k ≤
    2 ^ i.m * i.long ^ (l + k) + 2 ^ (i.m + i.height) * i.block ^ (l + k) + (wd i.x + wd i.y) * i.outer ^ (l + k)
  rw [add_mul, add_mul]
  simp only [pow_add, mul_assoc]
  gcongr
  · exact i.outer_block.trans i.block_long
  · exact i.outer_block

theorem Total.left (h : Total f) (h' : Outer g) : Total (fun i => g i * f i) :=
  (h.mul h').mono fun _ => le_of_eq (mul_comm ..)

theorem Total.scale (h : Total f) (k : ℕ) : Total (fun i => k * f i) := h.left (outer_const k)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
end

/-! # Controlling widths after an expansion of hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
open Assembly Coloring
variable {κ : Type} [Field κ] {b d B : ℕ}
local notation "I" => Case κ b d B

structure Child (N : (i : I) → Template i.F) (δ : I → ℕ) : Prop where
  extent : ∀ i, (N i).scheme.h ≤ i.height
  allocation : ∀ i, (N i).scheme.m ≤ i.m + δ i
  growth : Short (fun i : I => 2 ^ δ i)
  single : ∀ i, (N i).scheme.k = 0
  spans : Short (fun i : I => 2 ^ (N i).scheme.e)
  neighbors : Short (fun i : I => 2 ^ (N i).scheme.d)
  bits : Short (fun i : I => (N i).scheme.ℓ)
  count : Short (fun i : I => (N i).count)

namespace Child

theorem parent : Child (fun i : I => i.T) (fun _ => 0) :=
  ⟨fun _ => le_rfl, fun _ => le_rfl, short_const 1, fun i : I => i.h.single,
    Case.spans.short, Case.slots.short, Case.bits, counters⟩

variable {N : (i : Case κ b d B) → Template i.F} {δ f : Case κ b d B → ℕ} (H : Child N δ)
include H

theorem layer (h : Block f) : Row (fun i : I => 2 ^ (N i).scheme.h * f i) :=
  h.blocks.mono (fun i : I => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (H.extent i)))

theorem cost (h : Row f) : Cost (fun i : I => 2 ^ (N i).scheme.m * f i) :=
  (h.expand H.growth.block).mono
    (fun i : I => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (H.allocation i)))

theorem address : Long (fun i : I => (N i).scheme.m) :=
  (hosts.add H.growth.long.of_exp).mono H.allocation

theorem format : Cost (fun i : I => (N i).format.width) := by
  have top := Long.row (((H.neighbors.long.mul (H.address.add (long_const 2))).add (long_const 2)))
  have body := H.layer (H.bits.block.add H.count.block)
  refine (H.cost (top.add body)).mono fun i : I => ?_
  rw [Template.width]

theorem scheme : Cost (fun i : I => (N i).scheme.format.width) := by
  refine H.format.mono fun i : I => ?_
  rw [Format.width_pair]
  exact Nat.le_add_right ..

variable {j v : Case κ b d B → ℕ} (hj : Short (fun i => 2 ^ j i)) (hv : Row v)

include hj hv

theorem expand : Cost (fun i : I => 2 ^ ((N i).scheme.m + j i) * v i) := by
  simpa only [pow_add, mul_assoc] using H.cost (hv.left hj.block)

theorem access : Cost (fun i : I => i.p.fee ((N i).scheme.m + j i) (v i)) := by
  have p : Block (fun i : I => 1000 * (1 + i.p.W)) := (block_const 1000).mul ((block_const 1).add price.block)
  have w : Row (fun i : I => v i + 1 + i.p.w ^ i.p.power) := (hv.add (long_const 1).row).add Case.power.row
  refine ((H.expand hj w).left p).mono fun i => ?_
  rw [Prices.fee, mul_assoc]

theorem gather : Cost (fun i : I =>
    gatherCost ((N i).scheme.m) (j i) (v i) (i.p.fee ((N i).scheme.m + j i) (v i))) := by
  have m := H.address
  have q := m.add hj.long.of_exp
  have hi := ((long_const 100).add ((q.add ((long_const 3).mul m)).add (long_const 1))).pow 200
  have w := ((Long.row q).add hv).add (long_const 1).row
  refine ((((H.access hj hv).scale 4).add ((H.expand hj (Long.row hi)).scale 4)).add
    ((H.expand hj w).scale 1100)).mono fun i => ?_
  rw [gatherCost, mul_assoc 1100]

theorem read : Cost (fun i : I =>
    Window.readCost ((N i).scheme.m) (j i) (v i) (i.p.fee ((N i).scheme.m + j i) (v i))) :=
  (H.gather hj hv).add ((H.cost (((H.address.row.add hv).left hj.block).add hv)).scale 1000)

end Child
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
end

/-! # Budgets for common headers and per-block fields -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
open Coloring Assembly

variable {κ : Type} [Field κ] {b d B : ℕ}
local notation "I" => Case κ b d B

namespace Width
variable {A E : Case κ b d B → Format} {t f g : Case κ b d B → ℕ}

theorem expMax (h : Poly t (fun i => 2 ^ f i)) (k : Poly t (fun i => 2 ^ g i)) :
    Poly t (fun i => 2 ^ max (f i) (g i)) := by
  refine (h.add k).mono fun i => ?_
  rcases le_total (f i) (g i) with h|h
  · rw [max_eq_right h]; exact Nat.le_add_left ..
  · rw [max_eq_left h]; exact Nat.le_add_right ..

theorem bit : Short (fun _ : I => Format.bit.width) := short_const _
theorem addr (h : Poly t f) : Poly t (fun i => (Format.addr (f i)).width) :=
  h.mono (fun _ => (Format.width_addr _).le)
theorem pair (h : Poly t (fun i => (A i).width)) (k : Poly t (fun i => (E i).width)) :
    Poly t (fun i => ((A i).pair (E i)).width) :=
  (h.add k).mono (fun _ => (Format.width_pair ..).le)
theorem vec (h : Poly t (fun i => 2 ^ f i)) (k : Poly t (fun i => (A i).width)) :
    Poly t (fun i => (Format.vec (f i) (A i)).width) :=
  (h.mul k).mono (fun _ => (Format.width_vec ..).le)
theorem pack {n : I → ℕ} (h : Mixed n (fun i => (A i).width)) (k : Mixed n (fun i => (E i).width)) :
    Mixed n (fun i => ((A i).pair (E i)).width) :=
  (h.add k).mono (fun _ => (Format.width_pair ..).le)
theorem many (h : Short (fun i => 2 ^ f i)) (k : Row (fun i => (A i).width)) :
    Row (fun i => (Format.vec (f i) (A i)).width) :=
  (k.left h.block).mono (fun _ => (Format.width_vec ..).le)
end Width

namespace Child
variable {N : (i : Case κ b d B) → Template i.F} {δ : Case κ b d B → ℕ}
  {A : Case κ b d B → Format} (h : Child N δ)
include h

theorem vector (a : Row (fun i => (A i).width)) :
    Cost (fun i => (Format.vec (N i).scheme.m (A i)).width) :=
  (h.cost a).mono (fun _ => (Format.width_vec ..).le)

theorem stack (a : Short (fun i => (A i).width)) :
    Row (fun i => (Format.vec (N i).scheme.h (A i)).width) :=
  (h.layer a.block).mono (fun _ => (Format.width_vec ..).le)

theorem bank (a : Row (fun i => (A i).width)) :
    Cost (fun i => (Fmt.bank (N i).scheme.m (N i).scheme.d (A i)).width) :=
  h.vector (Width.pack (Long.row (Width.vec h.neighbors.long (Width.addr h.address))) a)

theorem attached {Z : (i : I) → Attachment (N i)} (a : Short (fun i => (Z i).ℓ)) :
    Cost (fun i => (Z i).format.width) :=
  Width.pack h.format (h.vector (h.stack (Width.addr a)))

end Child
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case
end

/-!
# Uniform sorting prices over extensions of the ground field

Choose the exponent of the width threshold before the extension
field is chosen. Mapping a permutation tensor to the extension
preserves its cost and all its zero-one entries.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
open Filter

variable {F : Type} [Field F]

def extend (p : Prices F) (K : Type) [Field K] [Algebra F K] : Prices K where
  w := p.w
  power := p.power
  W := p.W
  tag j v hj hw hv := by
    obtain ⟨m, hm, ht⟩ := p.tag j v hj hw hv
    exact ⟨m, hm, Assembly.tag_map ht⟩

private theorem pad (h A : ℕ) (hh : 16 ≤ h) :
    16 * h + (16 * h) ^ A ≤ h ^ (2 * (A + 1) + 1) := by
  have ha : 16 * h ≤ h ^ 2 := by rw [pow_two]; gcongr
  have hb : h ^ 2 ≤ h ^ (2 * (A + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hc : (16 * h) ^ A ≤ h ^ (2 * (A + 1)) := calc
    _ ≤ (h ^ 2) ^ A := Nat.pow_le_pow_left ha _
    _ ≤ _ := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ h ^ (2 * (A + 1)) + h ^ (2 * (A + 1)) := Nat.add_le_add (ha.trans hb) hc
    _ ≤ _ := by rw [pow_succ, ← mul_two]; gcongr; omega

theorem eventual (wide : Radix.WideTag F) {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : ℕ, ∀ᶠ n : ℕ in atTop,
      let h := Nat.clog 2 n
      ∀ (K : Type) [Field K] [Algebra F K], ∃ p : Prices K,
        p.w = 16 * h ∧ p.w + p.w ^ p.power ≤ h ^ R ∧ (p.W : ℝ) ≤ (h : ℝ) ^ τ := by
  obtain ⟨A, C, hC, h⟩ := Assembly.wide_cost wide (half_pos hτ)
  refine ⟨2 * (A + 1) + 1, ?_⟩
  have grows := (tendsto_rpow_atTop (half_pos hτ)).comp Shaving.tendsto_height
  filter_upwards [Shaving.tendsto_height.eventually_ge_atTop 16,
    grows.eventually_ge_atTop (C * (16 : ℝ) ^ (τ / 2) + 1)] with n hn hg
  intro t K _ _
  let p : Prices F := ⟨16 * t, A, ⌈C * ((16 * t : ℕ) : ℝ) ^ (τ / 2)⌉₊, h (16 * t)⟩
  have ht : 16 ≤ t := by exact_mod_cast hn
  refine ⟨p.extend K, rfl, pad t A ht, ?_⟩
  have hn' : 1 ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  calc
    _ ≤ C * ((16 * t : ℕ) : ℝ) ^ (τ / 2) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ (C * (16 : ℝ) ^ (τ / 2) + 1) * (t : ℝ) ^ (τ / 2) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (by positivity),
        add_mul, one_mul, mul_assoc]
      exact add_le_add_right (Real.one_le_rpow hn' (half_pos hτ).le) _
    _ ≤ (t : ℝ) ^ (τ / 2) * (t : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_right hg (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity), add_halves]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
end

/-! # The two elementary operations on an attached core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Packing

def SubroundRule (k : Type) [Field k] : Prop :=
  ∀ (P : Gadget k) Δ, 3 ≤ Δ → ∃ K, 0 < K ∧ Phase k Δ (Δ ^ degreePower) P.b degreePower K P.ratio 1

def ResetRule (k : Type) [Field k] : Prop :=
  ∀ (y w Δ : ℕ) (R : Rotor k (2 ^ y) w) (c : ℝ), 0 < w → 3 ≤ Δ → 4 * coreBins Δ ≤ 2 ^ y →
    1 ≤ c → (Fintype.card R.E : ℝ) ≤ c * (2 : ℝ) ^ y * w →
    ∃ K, 0 < K ∧ Phase k Δ 3 1 (900 + 2 ^ y + 1) K (2 * resetWidth c w) (2 * resetWidth c w)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Interface to a fixed number of reductions on an attached core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction

open Assembly
variable {F : Type} [Field F] {x y : Wire} {T Y : Template F}

structure Growth (A : Attachment T) (A' : Attachment Y) (r z payload n K H : ℕ) : Prop where
  height : Y.scheme.h + n * r = T.scheme.h
  lower : T.scheme.m ≤ Y.scheme.m
  upper : Y.scheme.m ≤ T.scheme.m + n * r + K
  degree : Y.scheme.d ≤ H
  full : Y.full = true
  single : Y.scheme.k = 0
  spans : 2 ^ Y.scheme.e ≤ H
  stations : A'.k ≤ A.k + n * r + K
  outer : 2 ^ A'.e ≤ 2 ^ A.e + H
  counters : Y.count ≤ (base A r z payload) ^ H
  labels : Y.scheme.ℓ + A'.ℓ ≤ H * (T.scheme.ℓ + A.ℓ) + (base A r z payload) ^ H

variable (A : Attachment T) (L : BorderLimit F x y)

def limit (P : Bound) (K : ℕ) (ρ c σ : ℝ) : Bound :=
  {after L P K ρ c σ with mass := P.mass + 2 * K * (P.width + (L.total + σ))}

structure Start (P : Bound) (p : Prices F) (r b u v z payload d B n K H : ℕ) (σ : ℝ) : Prop
    extends Input A L P p r b u v z payload d B K H σ where
  nonneg : 0 ≤ σ
  height : n * r ≤ T.scheme.h
  space : 2 * (T.scheme.m + n * r + K) ≤ p.w
  reserve : P.mass + 2 * K * (P.width + (L.total + σ)) ≤ L.cap

structure Stop (P : Bound) (p : Prices F) (r u v z payload Δ Δ' C C' n K H : ℕ)
    (ρ c σ : ℝ) where
  next : Template F
  pack : Attachment next
  growth : Growth A pack r z payload n K H
  keys : Finset (Table F)
  few : keys.card ≤ (short A r z payload) ^ H
  transfer : Transforms F ((short A r z payload) ^ H) keys
    (frame A L u z payload Δ C P) (frame pack L v z payload Δ' C' (limit L P K ρ c σ))
    (size (x := x) (y := y) A p r z payload H)

structure Block (k : Type) [Field k] (Δ Δ' b n e K : ℕ) (ρ c : ℝ) : Prop where
  unit : 0 < b
  steps : 0 < n
  overhead : 0 < K
  degree : ∀ C, Δ ≤ C → Δ' ≤ C ^ e
  factor : 0 ≤ ρ
  loss : 0 ≤ c
  run : ∀ C d B, Δ ≤ C → ∃ H, 0 < H ∧ ∀ (F : Type) [Field F] [Fintype F] [Algebra k F]
    {x y : Wire} {T : Template F} (A : Attachment T) (L : BorderLimit F x y)
    (P : Bound) (p : Prices F) (r u v z payload : ℕ) (σ : ℝ),
    Start A L P p r b u v z payload d B n K H σ →
    Nonempty (Stop A L P p r u v z payload Δ Δ' C (C ^ e) n K H ρ c σ)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

section
/-! # Growth of the control parameters in one contraction -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Growth
open Assembly

def rate (n K H : ℕ) := n + K + 2 * H + 100

variable {F : Type} {T Y : Template F} {A : Attachment T} {A' : Attachment Y}
  {r z payload n K H : ℕ} (g : Growth A A' r z payload n K H)

private theorem height_le_pow {X : ℕ} (h : 2 ≤ X) (k : ℕ) : k ≤ X ^ k :=
  (Nat.lt_two_pow_self (n := k)).le.trans (Nat.pow_le_pow_left h _)

include g in
private theorem base_bound :
    base A' r z payload ≤ 8 * (base A r z payload) ^ (n + K + H + 1) := by
  let X := base A r z payload
  let C := X ^ (n + K + H + 1)
  have hx : X = 100 + 2 ^ r + T.scheme.h + Nat.clog 2 (1 + z) + 2 ^ A.k + 2 ^ A.e +
      2 ^ T.scheme.e + payload + Nat.clog 2 (1 + T.scheme.ℓ + A.ℓ) := rfl
  have := Nat.two_pow_pos r
  have := Nat.two_pow_pos A.k
  have := Nat.two_pow_pos A.e
  have := Nat.two_pow_pos T.scheme.e
  have h2 : 2 ≤ X := by omega
  have hX : X ≤ C := Nat.le_pow (by omega)
  have hc : X ^ H ≤ C := Nat.pow_le_pow_right (by omega) (by omega)
  have hH := (height_le_pow h2 H).trans hc
  have hl : 1 + Y.scheme.ℓ + A'.ℓ ≤ (1 + T.scheme.ℓ + A.ℓ) * (C + 1) := by
    have h := g.labels
    change _ ≤ _ + X ^ H at h
    have ht := Nat.mul_le_mul_right (T.scheme.ℓ + A.ℓ) hH
    nlinarith only [h, ht, hc]
  have hlog : Nat.clog 2 (1 + Y.scheme.ℓ + A'.ℓ) ≤ X + C := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    apply hl.trans
    apply Nat.mul_le_mul
    · exact (Nat.le_pow_clog (by decide : 1 < 2) _).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact Nat.lt_two_pow_self
  have hs : 2 ^ A'.k ≤ C := calc
    _ ≤ 2 ^ (A.k + n * r + K) := Nat.pow_le_pow_right (by decide) g.stations
    _ = 2 ^ A.k * (2 ^ r) ^ n * 2 ^ K := by rw [pow_add, pow_add, mul_comm n, pow_mul]
    _ ≤ X * X ^ n * X ^ K := by gcongr <;> omega
    _ ≤ _ := by rw [← pow_succ', ← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have := g.height
  have := g.outer
  have := g.spans
  change base A' r z payload ≤ 8 * C
  unfold base
  omega

include g in
theorem base_le : base A' r z payload ≤ (base A r z payload) ^ (rate n K H) := by
  let X := base A r z payload
  have hx : 100 ≤ X := by unfold X base; grind
  apply g.base_bound.trans
  calc
    _ ≤ X * X ^ (n + K + H + 1) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := by rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by unfold rate; omega)

include g in
theorem short_le : short A' r z payload ≤ (short A r z payload) ^ (rate n K H) := by
  let X := short A r z payload
  let C := X ^ (n + K + H + 1)
  have hx : 100 ≤ X := by unfold X short base; grind
  have hB : base A r z payload ≤ X := by unfold X short; omega
  have hL : T.scheme.ℓ + A.ℓ ≤ X := by unfold X short; omega
  have hc : X ^ H ≤ C := Nat.pow_le_pow_right (by omega) (by omega)
  have hp := (Nat.pow_le_pow_left hB H).trans hc
  have hH := (height_le_pow (by omega : 2 ≤ X) H).trans hc
  have ht : base A' r z payload ≤ 8 * C :=
    g.base_bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _))
  have hl := g.labels.trans (Nat.add_le_add (Nat.mul_le_mul hH hL) hp)
  have hcnt := g.counters.trans hp
  calc
    _ ≤ 10 * C + C * X := by unfold short; omega
    _ ≤ C * X ^ 2 := by
      rw [mul_comm 10, ← mul_add]
      exact Nat.mul_le_mul_left _ (by nlinarith only [hx])
    _ ≤ _ := by unfold C; rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by unfold rate; omega)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Growth
end

/-!
# Composing quantitative bounds for attached contractions

Growth of the host count is controlled by the number of block
coordinates consumed in the phase. For local work the bound stays
polynomial in the short records without the global address length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Growth
open Assembly

variable {F : Type} {x y : Wire} {T Y Z : Template F}
  {A : Attachment T} {A' : Attachment Y} {A'' : Attachment Z}
  {r z payload n K H n' K' H' : ℕ}

def join (n K H J : ℕ) := rate n K H * (J + 1) + J + H + 2

theorem add_le (n K H J : ℕ) : H + J ≤ join n K H J := by unfold join; omega

private theorem absorb {X u v k : ℕ} (h : 2 ≤ X) (hu : u < k) (hv : v < k) :
    X ^ u + X ^ v ≤ X ^ k := by
  have hp : 0 < X := by omega
  calc
    _ ≤ X ^ (k - 1) + X ^ (k - 1) := Nat.add_le_add
      (Nat.pow_le_pow_right hp (by omega)) (Nat.pow_le_pow_right hp (by omega))
    _ = X ^ (k - 1) * 2 := by omega
    _ ≤ X ^ (k - 1) * X := Nat.mul_le_mul_left _ h
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]

private theorem first (n K H J : ℕ) : H < join n K H J := by unfold join; omega

private theorem second (n K H J : ℕ) :
    rate n K H + (rate n K H + 1) * J < join n K H J := by
  simp only [join, add_mul, mul_add, mul_one, one_mul]
  omega

private theorem raised {X k : ℕ} (h : 2 ≤ X) : k ≤ X ^ k :=
  Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h k)

private theorem base_room (A : Attachment T) (r z payload : ℕ) :
    2 ≤ base A r z payload ∧ 2 ^ r ≤ base A r z payload := by
  unfold base
  have hk := Nat.two_pow_pos A.k
  have hr := Nat.two_pow_pos r
  have he := Nat.two_pow_pos A.e
  have hd := Nat.two_pow_pos T.scheme.e
  omega

private theorem short_room (A : Attachment T) (r z payload : ℕ) :
    2 ≤ short A r z payload ∧ 2 ^ r ≤ short A r z payload := by
  have := base_room A r z payload
  unfold short
  omega

theorem keys (g : Growth A A' r z payload n K H) (J : ℕ) :
    (short A r z payload) ^ H + (short A' r z payload) ^ J ≤ (short A r z payload) ^ (join n K H J) := by
  refine (Nat.add_le_add_left (Nat.pow_le_pow_left g.short_le J) _).trans ?_
  rw [← pow_mul]
  apply absorb (short_room A r z payload).1 (first ..)
  unfold join
  rw [mul_add]
  omega

theorem comp (g : Growth A A' r z payload n K H) (g' : Growth A' A'' r z payload n' K' H') :
    Growth A A'' r z payload (n + n') (K + K') (join n K H H') := by
  let X := base A r z payload
  let j := join n K H H'
  let p := rate n K H
  have hp : 2 ≤ X := (base_room A r z payload).1
  have ht : H + H' < j := by unfold j join; omega
  have hu : p * H' < j := by unfold j join p; rw [mul_add]; omega
  have hv : H' * H ≤ j := by
    have : H ≤ p := by unfold p rate; omega
    exact (Nat.mul_le_mul_left H' this).trans ((mul_comm H' p).trans_le hu.le)
  have hm : (base A' r z payload) ^ H' ≤ X ^ (p * H') := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left g.base_le H'
  refine ⟨?_, g.lower.trans g'.lower, ?_, g'.degree.trans (by omega), g'.full, g'.single,
    g'.spans.trans (by omega), ?_, ?_, g'.counters.trans
      (hm.trans (Nat.pow_le_pow_right (by omega) hu.le)), ?_⟩
  · have := g.height; have := g'.height; rw [add_mul]; omega
  · have := g.upper; have := g'.upper; rw [add_mul]; omega
  · have := g.stations; have := g'.stations; rw [add_mul]; omega
  · have := g.outer; have := g'.outer; omega
  · calc
      _ ≤ H' * (H * (T.scheme.ℓ + A.ℓ) + X ^ H) + X ^ (p * H') :=
        g'.labels.trans (Nat.add_le_add (Nat.mul_le_mul_left _ g.labels) hm)
      _ = (H' * H) * (T.scheme.ℓ + A.ℓ) + (H' * X ^ H + X ^ (p * H')) := by ring
      _ ≤ j * (T.scheme.ℓ + A.ℓ) + (X ^ (H + H') + X ^ (p * H')) := by
        rw [pow_add, mul_comm (X ^ H)]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hv)
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (raised hp)) _)
      _ ≤ _ := Nat.add_le_add_left (absorb hp ht hu) _

private theorem sum_pow {X C j : ℕ} (hX : 2 ≤ X) (hj : 0 < j) :
    X ^ j + C ≤ (X + C) ^ (j + 1) :=
  (Nat.add_le_add (Nat.pow_le_pow_left (by omega) _) (show C ≤ (X + C) ^ 1 by simp)).trans
    (absorb (by omega) (by omega) (by omega))

private theorem site_count {a b X : ℕ} (h : b ≤ a + n * r + K) (hX : 2 ≤ X) (hr : 2 ^ r ≤ X) :
    2 ^ b ≤ 2 ^ a * X ^ (rate n K H) := by
  calc
    _ ≤ 2 ^ (a + n * r + K) := Nat.pow_le_pow_right (by decide) h
    _ = 2 ^ a * ((2 ^ r) ^ n * 2 ^ K) := by rw [pow_add, pow_add, mul_comm n, pow_mul, mul_assoc]
    _ ≤ 2 ^ a * (X ^ n * X ^ K) := by gcongr
    _ ≤ _ := by rw [← pow_add]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by unfold rate; omega))

private theorem pair_cost (g : Growth A A' r z payload n K H) (C J : ℕ) {a b : ℕ}
    (hab : b ≤ a + n * r + K) :
    2 ^ a * (short A r z payload + C) ^ H + 2 ^ b * (short A' r z payload + C) ^ J ≤
      2 ^ a * (short A r z payload + C) ^ (join n K H J) := by
  let X := short A r z payload + C
  let p := rate n K H
  obtain ⟨hh, ht⟩ := short_room A r z payload
  have hu : 2 ≤ X := by omega
  have hb : 2 ^ b ≤ 2 ^ a * X ^ p := site_count hab hu (by omega)
  have hs : short A' r z payload + C ≤ X ^ (p + 1) :=
    (Nat.add_le_add_right g.short_le _).trans (sum_pow hh (by unfold rate; omega))
  calc
    _ ≤ 2 ^ a * X ^ H + (2 ^ a * X ^ p) * (X ^ (p + 1)) ^ J :=
      Nat.add_le_add_left (Nat.mul_le_mul hb (Nat.pow_le_pow_left hs J)) _
    _ = 2 ^ a * (X ^ H + X ^ (p + (p + 1) * J)) := by rw [mul_add, pow_add X p ((p + 1) * J), pow_mul, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (absorb hu (first ..) (second ..))

theorem cost [Field F] (g : Growth A A' r z payload n K H) (J : ℕ) (p : Prices F) :
    size (x := x) (y := y) A p r z payload H + size (x := x) (y := y) A' p r z payload J ≤
      size (x := x) (y := y) A p r z payload (join n K H J) := by
  let C := 100 + p.w + p.w ^ p.power + p.W
  let X := 100 + payload + p.W
  have ha := pair_cost g C J g.upper
  have hb := pair_cost g p.W J (a := T.scheme.m + T.scheme.h) (b := Y.scheme.m + Y.scheme.h)
    (by have := g.height; have := g.upper; omega)
  have ht := absorb (show 2 ≤ X by omega) (first n K H J) (show J < join n K H J by unfold join; omega)
  have hc := Nat.mul_le_mul_left (wd x + wd y) ht
  rw [mul_add] at hc
  rw [add_comm (short A r z payload) C, add_comm (short A' r z payload) C] at ha
  dsimp only [X, C] at hc ha
  dsimp only [size]
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Growth
end
