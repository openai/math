import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Raw.Local
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.One

/-!
# Quantitative contract for one encoded contraction or reset

A phase reduces block height by exactly `r`. Its constants are
independent of the number of hosts and blocks. Only the charge on
long addresses can involve a polynomial of the global width `w`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Packing

structure Budget where
  load : ℕ
  tag : ℕ
  reach : ℕ
  width : ℝ
  mass : ℝ

variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T : Template F} {u : ℕ}

/-- Choose an artificially large full degree so noncore marks cannot
propagate. Only the small core graph needs to be stored. -/
def degreeBound (S : Setup F x y) (T : Template F) (Δ : ℕ) := Δ + 2 ^ S.h + 2 ^ T.scheme.m

structure Ready (Δ : ℕ) (P : Budget) (s : Snapshot.Data S T u) : Prop where
  live : Nonempty s.G.V
  neutral : s.Neutral
  tagged : s.Tagged P.tag
  bounded : s.G.Bounded Δ (degreeBound S T Δ) (P.load * S.z)
  tracks : S.first.Tracks s.G P.reach
  width : (s.G.X : ℝ) ≤ P.width
  mass : (s.G.mass : ℝ) ≤ P.mass

abbrev frame (S : Setup F x y) (T : Template F) (u Δ : ℕ) (P : Budget) :=
  Snapshot.restrict (Ready (S := S) (T := T) (u := u) Δ P)

namespace Phase

def base (S : Setup F x y) (r : ℕ) (P : Budget) :=
  100 + 2 ^ r + S.h + Nat.clog 2 (1 + S.U) + 2 ^ S.discount + P.load + S.d

def rate (S : Setup F x y) (T : Template F) (r : ℕ) (P : Budget) :=
  base S r P + 2 ^ T.scheme.e + Nat.clog 2 (1 + T.scheme.ℓ)

def short (S : Setup F x y) (T : Template F) (r : ℕ) (P : Budget) :=
  rate S T r P + T.count + T.scheme.ℓ + P.tag

def after (S : Setup F x y) (T : Template F) (r : ℕ) (P : Budget) (K : ℕ) (ρ C σ : ℝ) : Budget :=
  ⟨K * P.load, P.tag + (rate S T r P) ^ K, K * P.reach,
    ρ * P.width + C * (S.fringe.Z + σ), P.mass + 2 * P.width⟩

/-- Preconditions shared by all encoded inputs at a phase boundary. -/
structure Input (S : Setup F x y) (T : Template F) (P : Budget) (w r b u v d K : ℕ)
    (σ : ℝ) : Prop where
  trivalent : S.G.Trivalent
  zpos : 0 < S.z
  vpos : 0 < v
  divides : S.z ∣ v
  units : u = b * v
  initial : u ∣ S.U
  ceiling : u ≤ S.U
  load : u ≤ P.load * S.z
  group : r ≤ T.scheme.h
  height : T.scheme.h ≤ S.h
  room : K ≤ 2 ^ r
  positive : 0 < K
  degree : T.scheme.d ≤ d
  core : T.full = false
  single : T.scheme.k = 0
  names : S.e ≤ 3 * w
  lower : w ≤ T.scheme.m
  upper : T.scheme.m + K * (S.h + 1) ≤ 2 * w
  small : (short S T r P) ^ K ≤ w / 4
  origins : 3 * (K * P.reach) ≤ S.d
  reach : 0 < P.reach
  width : 0 ≤ P.width
  mass : 0 ≤ P.mass
  history : P.mass + 2 * P.width ≤ S.cap
  slack : K * (P.load * S.z : ℕ) * (2 ^ (T.scheme.m + T.scheme.h) : ℕ) ≤ σ * (2 : ℝ) ^ r

structure Output (S : Setup F x y) (T : Template F) (P : Budget) (w r u v Δ Δ' d' K : ℕ)
    (ρ C σ : ℝ) where
  next : Template F
  height : next.scheme.h + r = T.scheme.h
  lower : T.scheme.m ≤ next.scheme.m
  upper : next.scheme.m ≤ T.scheme.m + r + K
  degree : next.scheme.d ≤ d'
  core : next.full = false
  single : next.scheme.k = 0
  spans : 2 ^ next.scheme.e ≤ (base S r P) ^ K
  counters : next.count ≤ (base S r P) ^ K
  bits : next.scheme.ℓ ≤ (1 + P.tag) * (rate S T r P) ^ K
  labels : Finset (Table F)
  few : labels.card ≤ (short S T r P) ^ K
  small : ∀ k ∈ labels, Processor.arity k ≤ (short S T r P) ^ K
  scale : ℕ
  size : ℕ
  cost : size ≤ 2 ^ T.scheme.m * (100 + w + short S T r P) ^ K +
    2 ^ (T.scheme.m + T.scheme.h) * (short S T r P) ^ K
  transfer : Transforms F scale (Allowed F w ∪ (labels : Set (Table F)))
    (frame S T u Δ P) (frame S next v Δ' (after S T r P K ρ C σ)) size

end Phase

def Phase (F : Type) [Field F] (Δ Δ' d d' b K : ℕ) (ρ C : ℝ) : Prop :=
  ∀ {x y : Wire} (S : Setup F x y) (T : Template F) (P : Budget)
    (w r u v : ℕ) (σ : ℝ), Phase.Input S T P w r b u v d K σ →
    Nonempty (Phase.Output S T P w r u v Δ Δ' d' K ρ C σ)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # A common domain for bounds uniform in the host and block counts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase
open Assembly Packing

structure Case (F : Type) [Field F] (b d : ℕ) where
  x : Wire
  y : Wire
  S : Setup F x y
  T : Template F
  R : Budget
  w : ℕ
  r : ℕ
  u : ℕ
  v : ℕ
  K : ℕ
  σ : ℝ
  h : Input S T R w r b u v d K σ

namespace Case
variable {F : Type} [Field F] {b d : ℕ} (i : Case F b d)

abbrev m := i.T.scheme.m
abbrev height := i.T.scheme.h
abbrev a := i.height - i.r
abbrev n := i.height - i.a
abbrev base := Phase.base i.S i.r i.R
abbrev rate := Phase.rate i.S i.T i.r i.R
abbrev short := Phase.short i.S i.T i.r i.R
abbrev long := 100 + i.w + i.short

theorem n_eq : i.n = i.r := Nat.sub_sub_self i.h.group

private theorem nonneg (i : Case F b d) : 0 ≤ 2 ^ i.r ∧ 0 ≤ 2 ^ i.S.discount ∧ 0 ≤ 2 ^ i.T.scheme.e :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem base_two : 2 ≤ i.base := by unfold base Phase.base; have := nonneg i; omega
theorem base_rate : i.base ≤ i.rate := by unfold rate Phase.rate base; have := nonneg i; omega
theorem rate_short : i.rate ≤ i.short := by unfold short Phase.short rate; omega
theorem short_long : i.short ≤ i.long := Nat.le_add_left ..
theorem rate_two : 2 ≤ i.rate := i.base_two.trans i.base_rate
theorem short_two : 2 ≤ i.short := i.rate_two.trans i.rate_short
theorem long_two : 2 ≤ i.long := i.short_two.trans i.short_long

abbrev Base (f : Case F b d → ℕ) := Poly base f
abbrev Rate (f : Case F b d → ℕ) := Poly rate f
abbrev Short (f : Case F b d → ℕ) := Poly short f
abbrev Long (f : Case F b d → ℕ) := Poly long f

variable {f : Case F b d → ℕ}
theorem Base.rate (h : Base f) : Rate f := h.grow base_rate
theorem Rate.short (h : Rate f) : Short f := h.grow rate_short
theorem Short.long (h : Short f) : Long f := h.grow short_long

local notation "I" => Case F b d

theorem base_const (c : ℕ) : Base (fun _ : I => c) := Poly.const base_two c
theorem rate_const (c : ℕ) : Rate (fun _ : I => c) := Poly.const rate_two c
theorem short_const (c : ℕ) : Short (fun _ : I => c) := Poly.const short_two c
theorem long_const (c : ℕ) : Long (fun _ : I => c) := Poly.const long_two c

theorem blocks : Base (fun i : I => 2 ^ i.r) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem levels : Base (fun i : I => i.S.h) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem units : Base (fun i : I => Nat.clog 2 (1 + i.S.U)) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem discount : Base (fun i : I => 2 ^ i.S.discount) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem load : Base (fun i : I => i.R.load) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem lanes : Base (fun i : I => i.S.d) :=
  Poly.of_le base_two (fun i => by unfold base Phase.base; have := nonneg i; omega)
theorem spans : Rate (fun i : I => 2 ^ i.T.scheme.e) :=
  Poly.of_le rate_two (fun i => by unfold rate Phase.rate; have := nonneg i; omega)
theorem lengths : Rate (fun i : I => Nat.clog 2 (1 + i.T.scheme.ℓ)) :=
  Poly.of_le rate_two (fun i => by unfold rate Phase.rate; have := nonneg i; omega)
theorem counters : Short (fun i : I => i.T.count) :=
  Poly.of_le short_two (fun i => by unfold short Phase.short; omega)
theorem bits : Short (fun i : I => i.T.scheme.ℓ) :=
  Poly.of_le short_two (fun i => by unfold short Phase.short; omega)
theorem tags : Short (fun i : I => i.R.tag) :=
  Poly.of_le short_two (fun i => by unfold short Phase.short; omega)
theorem world : Long (fun i : I => i.w) :=
  Poly.of_le long_two (fun i => by unfold long; omega)
theorem hosts : Long (fun i : I => i.m) :=
  ((long_const 2).mul world).mono (fun i => (Nat.le_add_right ..).trans i.h.upper)
theorem groups : Base (fun i : I => i.a) :=
  levels.mono fun i => (Nat.sub_le ..).trans i.h.height
theorem tiles : Base (fun i : I => 2 ^ i.n) := by simpa only [n_eq] using (blocks : Base (fun i : I => _))
theorem slots : Base (fun i : I => 2 ^ i.T.scheme.d) :=
  (base_const (2 ^ d)).mono fun i => Nat.pow_le_pow_right (by decide) i.h.degree

end Case
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase
end

/-!
# Charges on host addresses and short block records

Multiplication by a short quantity is allowed in both terms of the
budget. Multiplication by the world size is confined to the first.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
variable {F : Type} [Field F] {b d : ℕ}
local notation "I" => Case F b d

def Mixed (j f : I → ℕ) : Prop :=
  ∃ k : ℕ, ∀ i, f i ≤ 2 ^ (j i) * i.long ^ k + 2 ^ (j i + i.height) * i.short ^ k

abbrev Cost (f : I → ℕ) := Mixed m f
abbrev Row (f : I → ℕ) := Mixed (fun _ => 0) f

variable {j f g n : Case F b d → ℕ}

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
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.short_two ..))

theorem mul (h : Mixed j f) (h' : Short g) : Mixed j (fun i => f i * g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'.bound
  refine ⟨l + k, fun i => (Nat.mul_le_mul (hl i) (hk i)).trans ?_⟩
  simp only [add_mul, mul_assoc, pow_add]
  gcongr
  exact i.short_long

theorem left (h : Mixed j f) (h' : Short g) : Mixed j (fun i => g i * f i) :=
  (h.mul h').mono fun _ => le_of_eq (mul_comm ..)

theorem scale (h : Mixed j f) (k : ℕ) : Mixed j (fun i => k * f i) := h.left (short_const k)

theorem long (j : I → ℕ) (h : Long f) : Mixed j (fun i => 2 ^ (j i) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_right ..)⟩

theorem short (j : I → ℕ) (h : Short f) : Mixed j (fun i => 2 ^ (j i + i.height) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_left ..)⟩

end Mixed

theorem Long.row (h : Long f) : Row f := by
  simpa only [pow_zero, one_mul] using Mixed.long (fun _ => 0) h

theorem Short.blocks (h : Short f) : Row (fun i => 2 ^ i.height * f i) := by
  simpa only [zero_add] using Mixed.short (fun _ => 0) h

theorem Short.groups (h : Short f) : Row (fun i => 2 ^ i.a * f i) :=
  h.blocks.mono (fun i => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)))

theorem Row.hosts (h : Row f) : Cost (fun i => 2 ^ i.m * f i) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun i => ?_⟩
  simpa only [pow_zero, one_mul, zero_add, mul_add, ← mul_assoc, ← pow_add] using Nat.mul_le_mul_left (2 ^ i.m) (hk i)

theorem Row.expand (h : Row f) (h' : Short (fun i => 2 ^ n i)) :
    Cost (fun i => 2 ^ (i.m + n i) * f i) := by
  simpa only [pow_add, mul_assoc] using Row.hosts (h.left h')

theorem Row.cost (h : Row f) : Cost f :=
  h.hosts.mono fun _ => Nat.le_mul_of_pos_left _ (by positivity)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
end

/-! # Polynomial cost of the new table controls after a host reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
open Coloring Assembly History

variable {F : Type} [Field F] [Fintype F] {b d : ℕ}
local notation "I" => Case F b d

theorem reset_overhead {e : I → ℕ} (he : Rate (fun i => 2 ^ (e i))) :
    Rate (fun i => Reset.overhead i.T.scheme (e i)) := by
  have hl : Rate (fun i : I => Dense.used i.T.scheme.ℓ) := by
    simpa only [Dense.used, Nat.add_comm] using (lengths : Rate (fun i : I => _))
  have hk : Rate (fun i : I => 1 + i.T.scheme.k) :=
    (rate_const 1).mono fun i => by rw [i.h.single, Nat.add_zero]
  have hy := he.of_exp.add (rate_const 1)
  have ht := (((he.add he).add (rate_const 1)).pow 3).mul (rate_const 8)
  have hc := ht.mul (rate_const (Nat.clog 2 (Fintype.card F)))
  have hh := (hy.add (he.mul (hk.add (spans.mul hy)))).add hc
  refine (hh.add (he.mul hl)).mono fun i => ?_
  simp only [Reset.overhead, Reset.shapeWidth, Reset.tripleCost, Reset.Addr, B, Fintype.card_sum, Fintype.card_fin]
  rfl

theorem reset_added {n e k : I → ℕ} (hn : Rate n) (he : Rate (fun i => 2 ^ (e i))) (hk : Rate k) :
    Rate (fun i => (Post.headerFmt (n i) (e i) (k i)).width + Reset.overhead i.T.scheme (e i)) := by
  have one := (rate_const 1 : Rate (fun _ : I => _))
  refine ((one.add (he.mul (hk.add (one.add (one.add (hn.add he.of_exp)))))).add
    (reset_overhead he)).mono fun i => ?_
  simp only [Post.headerFmt, Post.field, Format.width_pair, Format.width_vec, Format.width_addr]
  rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
end

/-! # Controlling widths after an expansion of hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
open Assembly Coloring
variable {F : Type} [Field F] {b d : ℕ}
local notation "I" => Case F b d

structure Child (N : I → Template F) (δ : I → ℕ) : Prop where
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
    Case.spans.short, Case.slots.rate.short, Case.bits, counters⟩

theorem names : Long (fun i : I => i.S.e) :=
  ((long_const 3).mul world).mono (fun i : I => i.h.names)

variable {N : Case F b d → Template F} {δ f : Case F b d → ℕ} (H : Child N δ)
include H

theorem layer (h : Short f) : Row (fun i : I => 2 ^ (N i).scheme.h * f i) :=
  h.blocks.mono (fun i : I => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (H.extent i)))

theorem cost (h : Row f) : Cost (fun i : I => 2 ^ (N i).scheme.m * f i) :=
  (h.expand H.growth).mono
    (fun i : I => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (H.allocation i)))

theorem address : Long (fun i : I => (N i).scheme.m) :=
  (hosts.add H.growth.long.of_exp).mono H.allocation

theorem format : Cost (fun i : I => (N i).format.width) := by
  have top := Long.row (((H.neighbors.long.mul (H.address.add (long_const 2))).add (long_const 2)))
  have body := H.layer (H.bits.add H.count)
  refine (H.cost (top.add body)).mono fun i : I => ?_
  rw [Template.width]

theorem scheme : Cost (fun i : I => (N i).scheme.format.width) := by
  refine H.format.mono fun i : I => ?_
  rw [Format.width_pair]
  exact Nat.le_add_right ..

theorem row : Row (fun i : I => (Trail.rowFormat (N i).scheme i.S.h i.S.d i.S.e).width) := by
  have body := H.layer (H.spans.mul (lanes.rate.short.add levels.rate.short))
  have head : Row (fun i : I => i.S.d * i.S.e) := Long.row ((lanes.rate.short.long.mul names))
  refine (body.add head).mono fun i : I => ?_
  rw [Trail.width_row, H.single, add_zero, pow_add, mul_assoc]

theorem trail : Cost (fun i : I => (Trail.format (N i).scheme i.S.h i.S.d i.S.e).width) := by
  refine (H.cost H.row).mono fun i : I => ?_
  rw [Trail.width_format]

theorem full : Cost (fun i : I => (i.S.format (N i)).width) := by
  refine (H.format.add H.trail).mono fun i : I => ?_
  rw [Format.width_pair]

theorem sweep : Cost (fun i : I => Snapshot.sweepCost i.S (N i)) := by
  have tags := H.layer (((short_const 1).add H.bits).add H.bits)
  have address := Long.row (((long_const 4).mul (H.neighbors.long.mul H.address)))
  have aux : Cost (fun i : I => (Format.vec (N i).scheme.m (N i).header).width) := by
    refine H.format.mono fun i : I => ?_
    rw [Format.width_pair]
    exact Nat.le_add_left ..
  refine (((H.cost (address.add tags)).add (aux.scale 4)).add (H.trail.scale 4)).mono fun i : I => ?_
  rw [Snapshot.sweepCost, updateCost, Format.width_addr]

end Child
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case
end

/-! # The cost of retaining exterior labels after an expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case.Child
open Assembly Coloring
variable {F : Type} [Field F] {b d : ℕ}
local notation "I" => Case F b d
variable {N : Case F b d → Template F} {δ k : Case F b d → ℕ} (H : Child N δ)
  (hk : Short (fun i => 2 ^ k i))

private theorem old_height : Short (fun i : I => i.height) :=
  levels.rate.short.mono (fun i : I => i.h.height)

include H hk

theorem receipts :
    Cost (fun i : I => (Trail.receipts i.T.scheme (N i).scheme (k i) i.S.h i.S.d i.S.e).width) := by
  refine (H.cost (parent.row.left hk)).mono fun i : I => ?_
  rw [Format.width_vec, Format.width_vec]

theorem controls : Cost (fun i : I => (Trail.controls i.T.scheme (N i).scheme (k i)).width) := by
  have len := (((short_const 1).add hk.of_exp).add old_height).add parent.spans.of_exp
  refine (H.cost (H.layer (H.spans.mul len))).mono fun i : I => ?_
  rw [Trail.width_controls, H.single, i.h.single, add_zero, add_zero, pow_add, mul_assoc, mul_assoc]

private theorem execution : Cost (fun i : I => Trail.cost i.T.scheme (N i).scheme (k i) i.S.h i.S.d i.S.d i.S.e) := by
  let w := fun i : I => Trail.addressWidth i.T.scheme (N i).scheme (k i)
  let a := fun i : I => 1 + k i + i.T.scheme.e + (N i).scheme.e
  have wa (i : I) : w i ≤ i.height + a i := by
    unfold w Trail.addressWidth a
    rw [H.single, i.h.single]
    have := H.extent i
    unfold Case.height at *
    omega
  have ha : Short (fun i : I => 2 ^ a i) :=
    (((short_const (2 ^ 1)).exp_add hk).exp_add parent.spans).exp_add H.spans
  have hw : Short w := (old_height.add ha.of_exp).mono wa
  have hw' : Row (fun i : I => 2 ^ w i) := by
    refine ha.blocks.mono fun i : I => ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (wa i)
  have lane := (lanes (F := F) (b := b) (d := d)).rate.short
  have hs := (((((short_const 100).add hw).add (hk.mul (lane.add (short_const 1)))).add
    levels.rate.short).add lane).add lane
  exact H.cost ((hw'.mul (hs.pow 10)).add (Long.row (((Short.long hs).add names).pow 104)))

theorem carry {A : I → Format} (h : Cost (fun i : I => (A i).width)) :
    Cost (fun i : I => Trail.carryCost i.T.scheme (N i).scheme (k i)
      i.S.h i.S.d i.S.d i.S.e (A i) (N i).format) := by
  have feed := (H.receipts hk).add (H.controls hk)
  refine (((h.scale 20).add ((H.format.add feed).scale 16)).add ((execution H hk).scale 4)).mono fun i : I => ?_
  rw [Trail.carryCost, show (Trail.feed _ _ _ _ _ _).width = _ from Format.width_pair ..]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case.Child
end

/-! # Gathering neighboring records without duplicating long addresses per block -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case.Child
open Assembly Coloring
variable {F : Type} [Field F] {b d : ℕ}
local notation "I" => Case F b d

theorem current : Cost (fun i : I => (Trail.source i.T.scheme i.S.h i.S.d i.S.e).width) := by
  refine (parent.scheme.add parent.trail).mono fun i : I => ?_
  rw [Format.width_pair]

private theorem bank : Cost (fun i : I => (Trail.bank i.T.scheme i.S.h i.S.d i.S.e).width) := by
  have h : Long (fun i : I => 2 ^ i.T.scheme.d * i.m) := parent.neighbors.long.mul hosts
  refine (Row.hosts (h.row.add parent.row)).mono fun i : I => ?_
  rw [Format.width_vec, Format.width_pair, Format.width_vec, Format.width_addr]

theorem fan : Short (fun i : I => 2 ^ (i.T.scheme.d + 1)) :=
  parent.neighbors.exp_add (short_const (2 ^ 1))

theorem gather {N : I → Template F} {δ c : I → ℕ} (H : Child N δ)
    (h : Cost (fun i : I => gatherCost i.m i.T.scheme.d (Trail.rowFormat i.T.scheme i.S.h i.S.d i.S.e).width (c i))) :
    Cost (fun i : I => Trail.gatherBound i.T.scheme (N i).scheme i.S.h i.S.d i.S.e
      (Trail.rowFormat i.T.scheme i.S.h i.S.d i.S.e).width (c i)) := by
  have extra := ((current.add bank).add (parent.receipts parent.neighbors)).add (H.receipts fan)
  exact h.add (extra.scale 64)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.Case.Child
end
