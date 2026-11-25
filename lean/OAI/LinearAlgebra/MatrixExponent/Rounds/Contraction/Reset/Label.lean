import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.ShortNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Attachment.WriteNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Correspondence
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames

/-! # Record and payload widths after reattachment -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
open Coloring Assembly Width BatchDescent

variable {κ : Type} [Field κ] {b d B : ℕ} {N : (i : Case κ b d B) → Template i.F}
  {δ j p : Case κ b d B → ℕ} (h : Child N δ) (hj : Short (fun i => 2 ^ j i)) (hp : Short (fun i => 2 ^ p i))
local notation "I" => Case κ b d B

include h in
theorem payload : Total (fun i : I => (Attachment.payload i.x i.y i.payload (N i).scheme.m).width) := by
  have u := (h.cost (long_const 1).row).total
  have v : Total (fun i : I => (wd i.x + wd i.y) * 1) := (outer_const 1).total
  refine (((u.add v).scale 2).left (loads.add (outer_const 1))).mono fun i => ?_
  simpa only [mul_one, Attachment.payload, Attachment.volume, add_assoc] using Fmt.width_payload (N i).scheme.m
    (Attachment.volume i.x i.y (N i).scheme.m) i.payload

include h hj in
theorem transport : Short (fun i : I => (i.A.transport (N i) (j i)).ℓ) := by
  have t : Short (fun i : I => 2 ^ (i.A.spanBits (N i))) := expMax ports.short h.spans
  have member : Short (fun i : I => i.A.member.width) := pair bit (pair (addr labels) (addr stations.short.of_exp))
  have target := pair (addr h.neighbors.of_exp) (pair (addr hj.of_exp) (addr t.of_exp))
  exact pair (addr h.bits) (vec hj (pair member (vec t (pair bit (pair bit target)))))

include h hj in
theorem shrink (c : ℕ) : Short (fun i : I => (i.A.shrink (N i) (j i) c).ℓ) := by
  have t : Short (fun i : I => 2 ^ (i.A.spanBits (N i))) := expMax ports.short h.spans
  have endpt := (((short_const 2).add h.neighbors.of_exp).add hj.of_exp).add t.of_exp
  have extra := hj.mul (((short_const 1).add stations.short.of_exp).add (t.mul endpt))
  refine ((h.bits.add ((short_const c).mul labels)).add extra).mono fun i => ?_
  exact (i.A.short_width (N i) (j i) c).le

include h hj in
theorem shrinkWidth (c : ℕ) : Short (fun i : I => i.A.shrinkWidth (N i) (j i) c) :=
  (h.transport hj).add (h.shrink hj c)

include h hj in
theorem shrinkCost (c : ℕ) : Total (fun i : I => i.A.shrinkCost (N i) (j i) c i.x i.y i.payload) := by
  have labels := h.cost (h.layer ((block_const 1).add (h.shrinkWidth hj c).block))
  exact (Cost.total ((h.format.scale 4).add labels)).add (h.payload.scale 4)

include h hj hp in
theorem orders : Short (fun i : I => (i.A.orders (N i) (j i) (p i)).width) := by
  have a : Short (fun i : I => i.T.scheme.k) := (short_const 0).mono fun i => (i.h.single).le
  have p₁ := pair bit (pair (addr hp.of_exp) (pair (addr levels.short) (pair (addr a) (addr Case.spans.short.of_exp))))
  have p₂ : Short (fun i : I => i.A.pointer.width) := pair bit (pair (addr levels.short) (addr stations.short.of_exp))
  exact pair (vec h.spans p₁) (vec hj p₂)

include h hj hp in
theorem requests : Cost (fun i : I => (i.A.Requests (N i) (j i) (p i)).width) :=
  pack (parent.attached labels) (pack h.format (h.vector (h.stack (pair bit (h.orders hj hp)))))

include h hj hp in
theorem sweepCost : Cost (fun i : I => i.A.sweepCost (N i) (j i) (p i)) := by
  have tags := h.layer (((block_const 1).add h.bits.block).add h.bits.block)
  have graph := Long.row ((long_const 4).mul (h.neighbors.long.mul h.address))
  have aux : Cost (fun i : I => (Format.vec (N i).scheme.m (N i).header).width) := by
    refine h.format.mono fun i => ?_
    rw [Format.width_pair]
    exact Nat.le_add_left ..
  have orders := h.vector (h.stack (pair bit (h.orders hj hp)))
  have src : Cost (fun i : I => i.A.format.width) := parent.attached labels
  refine ((src.scale 4).add (((h.cost (graph.add tags)).add (aux.scale 4)).add (orders.scale 4))).mono fun i => ?_
  rw [Attachment.sweepCost, updateCost, Format.width_addr]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
end

/-! # Transporting a ready border across an exact change of core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing Assembly.Attachment
open scoped Classical

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {x y : Wire}
  {k m u v z Δ C Δ' C' : ℕ} {L : BorderLimit F x y} {P P' : Bound}
  (X : A.Data x y u) (q : A.Query Y k m) (G : HostNet F X.L Y.scheme.h v)
  (old : A.Encloses q.old X.G X.Z) (fresh : Y.Encodes q.fresh G) (slot : X.T → Coloring.B k)
  (h : q.R.Moves old fresh slot) (ok : Relocation.WriteActive fresh q.active)
  (move : q.M.Agrees old.core.post.toPresentation fresh.post.toPresentation) (full : Y.full = true)

theorem moved_ready (hx : Ready A L z Δ C P X) (live : Nonempty G.V)
    (simple : Δ' ≤ 3 → ∀ e, G.src e ≠ G.dst e)
    (low : ∀ j, v ≤ fresh.post.toPresentation.borderWidth j)
    (stay : X.G.Preserves G) (hb : G.Bounded Δ' C' P'.load)
    (hw : (G.X : ℝ) ≤ P'.width) (hm : (G.mass : ℝ) ≤ P'.mass) :
    Ready (A.transport Y.sweep k) L z Δ' C' P' (q.apply h ok move full) where
  neutral := G.diagram.sweep_neutral
  live := live
  simple := simple
  span := q.floor h ok move full low
  parallel j := (hx.parallel j).trans (stay.parallelBits _ j)
  scale := hx.scale
  discount := hx.discount
  cap := hx.cap
  total := hx.total
  charge := hx.charge
  test := hx.test
  bounded := hb
  width := hw
  mass := hm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Control parameters for a reset with attached border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly
open scoped Classical

export BatchDescent.Restore (gain tolerance Slice)

variable {F : Type} {x y : Wire}

def indices (T : Template F) (Δ z B : ℕ) :=
  4 * (Template.Encodes.margin Δ) ^ 2 + 4 + T.scheme.h + Nat.clog 2 (1 + B ^ 3 * z)

def e (t B : ℕ) := Nat.clog 2 (gain t * B)
def copies (t B : ℕ) := B * gain t * B
def c (t z B : ℕ) := Nat.clog 2 (copies t B * z + 1)

abbrev meter (L : BorderLimit F x y) (t z B : ℕ) :=
  Template.Meter.bounded (c t z B) (1 / (L.denom : ℝ)) (1 / (2 : ℝ) ^ L.discount)

abbrev cap [Fintype F] (T : Template F) (t B : ℕ) :=
  History.Reset.overhead T.scheme (e t B) + T.scheme.ℓ * copies t B
abbrev book [Fintype F] (T : Template F) (u t z B : ℕ) :=
  History.Reset.Book.make T.scheme u (e t B) (cap T t B) T.order (Finset.range (B * z + 1))

variable [Field F] [Fintype F] {Y w : ℕ} (R : Rotor F Y w)
  (T : Template F) (L : BorderLimit F x y) (u t z Δ C B r : ℕ)

abbrev raw := T.reset R Δ C (T.scheme.h - r) (book T u t z B) (meter L t z B)
abbrev next := (raw R T L u t z Δ C B r).sweep

def slots {T : Template F} (A : Attachment T) (r : ℕ) := T.scheme.h - (T.scheme.h - r) + A.k

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-!
# Uniform widths over a changing working field

The base bounds the logarithm of the alphabet and the precision of
the physical counters. Only the cost of retaining old labels is
linear in the full input label length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Coloring Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B

abbrev child (i : I) := raw (R.extend i.F) i.T i.L i.u t i.z Δ C B i.r
abbrev shift (i : I) := History.Reset.Child.extra R Δ i.n
abbrev keyBits (i : I) := Nat.clog 2 (i.height + 1)
abbrev depth (i : I) := i.n + 8

theorem child_factor : Base (fun i : I => 2 ^ shift R Δ d B i) :=
  tiles.exp_add (base_const (2 ^ Nat.clog 2 (resetPositions R Δ)))

def degree (C Y : ℕ) := Nat.clog 2 (4 + terminalWidth C Y)

theorem child_degree (i : I) : (child R Δ C t d B i).scheme.d = degree C Y := by
  change History.Reset.Child.width C Y i.T.full = _
  rw [i.h.full]
  rfl

private theorem clog_mul (n z : ℕ) : Nat.clog 2 (n * z + 4) ≤ n + 4 + Nat.clog 2 (1 + z) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  calc
    _ ≤ (n + 4) * (1 + z) := by simp only [mul_add, add_mul, mul_one]; omega
    _ ≤ _ := Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.le_pow_clog (by decide) _)

theorem meter_bound : Base (fun i : I => (meter i.L t i.z B).count) := by
  have h : Base (fun i : I => c t i.z B) :=
    ((base_const (copies t B + 4)).add units).mono fun i =>
      (Nat.clog_mono_right _ (by omega : copies t B * i.z + 1 ≤ copies t B * i.z + 4)).trans (clog_mul ..)
  exact (base_const 3).mul h

theorem palette_bound : Base (fun i : I => (book i.T i.u t i.z B).d) := by
  refine ((base_const (B + 4)).add units).mono fun i => ?_
  simp only [book, History.Reset.Book.make, History.Reset.Book.lenBits, Finset.card_range]
  exact clog_mul B i.z

theorem overhead_bound : Base (fun i : I => History.Reset.overhead i.T.scheme (e t B)) := by
  have hl : Base (fun i : I => History.Dense.used i.T.scheme.ℓ) := by
    refine lengths.mono fun i => ?_
    exact Nat.clog_mono_right _ (by omega)
  have hk : Base (fun i : I => 1 + i.T.scheme.k) :=
    (base_const 1).mono fun i => by rw [i.h.single, Nat.add_zero]
  have hs : Base (fun i : I => Nat.clog 2 (Fintype.card i.F)) := by
    refine blocks.mono fun i => ?_
    rw [← Nat.card_eq_fintype_card]
    exact i.h.alphabet
  have he : Base (fun _ : I => 2 ^ (e t B)) := base_const _
  have hy := he.of_exp.add (base_const 1)
  have ht := (((he.add he).add (base_const 1)).pow 3).mul (base_const 8)
  have hh := (hy.add (he.mul (hk.add (spans.mul hy)))).add (ht.mul hs)
  refine (hh.add (he.mul hl)).mono fun i => ?_
  simp only [History.Reset.overhead, History.Reset.shapeWidth, History.Reset.tripleCost,
    History.Reset.Addr, Coloring.B, Fintype.card_sum, Fintype.card_fin]
  rfl

def added (i : I) := (History.Post.headerFmt (child R Δ C t d B i).scheme.d (e t B)
  (book i.T i.u t i.z B).d).width + History.Reset.overhead i.T.scheme (e t B)

theorem added_bound : Base (added R Δ C t d B) := by
  have one := (base_const 1 : Base (fun _ : I => _))
  have he : Base (fun _ : I => 2 ^ (e t B)) := base_const _
  have hd : Base (fun i : I => (child R Δ C t d B i).scheme.d) :=
    (base_const (degree C Y)).mono fun i => (child_degree R Δ C t d B i).le
  have hdr := one.add (he.mul ((palette_bound (F := F) t d B).add (one.add (one.add (hd.add he.of_exp)))))
  refine (hdr.add (overhead_bound t d B)).mono fun i => ?_
  simp only [added, History.Post.headerFmt, History.Post.field, Format.width_pair, Format.width_vec, Format.width_addr]
  rfl

theorem label_eq (i : I) :
    (child R Δ C t d B i).scheme.ℓ = added R Δ C t d B i + i.T.scheme.ℓ * copies t B := by
  change (History.Post.record _ _ _ (.addr _)).width = _
  simp only [added, book, History.Reset.Book.make, cap, History.Post.record, History.Post.headerFmt,
    Format.width_pair, Format.width_addr, add_assoc]

theorem bits_bound : Short (fun i : I => (child R Δ C t d B i).scheme.ℓ) :=
  ((added_bound R Δ C t d B).short.add (Case.bits.mul (short_const (copies t B)))).mono
    (fun i => (label_eq R Δ C t d B i).le)

theorem child_bound : Case.Child (child R Δ C t d B) (shift R Δ d B) := by
  refine ⟨fun _ => Nat.sub_le .., fun _ => le_rfl, (child_factor R Δ d B).short, fun _ => rfl,
    short_const (2 ^ e t B), ?_, bits_bound R Δ C t d B, (meter_bound t d B).short⟩
  exact (short_const (2 ^ degree C Y)).mono fun i => (congrArg (2^·) (child_degree R Δ C t d B i)).le

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-!
# Precision for a reset with two kinds of charge

The exterior and the incidence history have different denominators.
Their product clears both denominators, uniformly over all states.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C : ℕ} {σ : ℝ}

def denominator (L : BorderLimit F x y) := L.denom * 2 ^ L.discount

omit [Field F] in
theorem limits (T : Template F) (Δ z B : ℕ) :
    let b := indices T Δ z B
    4 * (Template.Encodes.margin Δ) ^ 2 < 2 ^ b ∧ 6 * 2 ^ T.scheme.h < 2 ^ b ∧ B ^ 3 * z < 2 ^ b := by
  dsimp only
  unfold indices
  constructor
  · exact (by omega : _ ≤ 4 * (Template.Encodes.margin Δ) ^ 2 + 4 + T.scheme.h+
      Nat.clog 2 (1 + B ^ 3 * z)).trans_lt Nat.lt_two_pow_self
  constructor
  · calc
      _ < 2 ^ 3 * 2 ^ T.scheme.h := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
      _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (Nat.lt_add_one _).trans_le (by
      rw [add_comm (B ^ 3 * z)]
      exact (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)))

variable (h : Input A L P p r 1 u u z payload d B K H σ)
    (q : (frame A L u z payload Δ C P).state)

include h in
theorem integer (v : q.val.G.V) (i : Cell T.scheme.h) :
    ∃ n : Coloring.B (indices T Δ z B), q.val.G.load v i * denominator L = n.val := by
  let G := q.val.G
  let c := (v, i)
  have Hq := q.property.1
  have hm : G.mass ≤ q.val.L.cap := by
    rw [Hq.cap]
    exact Nat.cast_le.mp (Hq.mass.trans (le_trans (le_add_of_nonneg_right
      (mul_nonneg (by norm_num) h.width)) h.history))
  choose f _ hf using Hq.charge
  let park := ∑ j, if G.park j = c then f j else 0
  have hp : push G.park q.val.L.charge c = (park : ℝ) := by
    simp only [park, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, push, hf]
  let n := (G.tetherLoad c + Packing.degree G.pair c * u) * denominator L + park * 2 ^ L.discount + G.past c * L.denom
  have he : G.load v i * denominator L = (n : ℝ) := by
    rw [HostNet.load, hp, HostNet.rate, ite_eq_left hm, Hq.scale, Hq.discount]
    simp only [n, c, denominator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpos : (L.denom : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.denom.ne'
    field_simp
  have hn : n ≤ B ^ 3 * z := by
    have hd : denominator L ≤ B * B := Nat.mul_le_mul h.scale h.discount
    apply (Nat.cast_le (α := ℝ)).mp
    rw [← he]
    calc
      _ ≤ ((B : ℝ) * z) * (B * B : ℕ) := mul_le_mul ((Hq.bounded.2.2 v i).trans h.ceiling)
        (Nat.cast_le.mpr hd) (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  exact ⟨⟨n, hn.trans_lt (limits T Δ z B).2.2⟩, he⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Electing a reset at the current physical load bound -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ : ℝ}
    (h : Input A L P p r 1 u u z payload d B K H σ) (s : Slice Δ Y w t)
    (hC : Δ ≤ C) (hk : 2 ^ t ≤ K) (q : (frame A L u z payload Δ C P).state)
local notation "a" => (T.scheme.h - r)
local notation "W" => ((2 : ℝ) ^ t * P.load)
local notation "g" => Template.Encodes.margin Δ

include h in
private theorem positive : 0 < P.load :=
  (Nat.cast_pos.mpr (h.zpos.trans_le h.vpos)).trans_le h.load

include h in
private theorem normalized (x : ℝ) (hb : x ≤ P.load) : x / W ≤ 1 / (2 : ℝ) ^ t := by
  have := positive h
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm x]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

include h in
theorem unit (_s : Slice Δ Y w t) : (u : ℝ) / W ≤ 1 / (2 : ℝ) ^ t := normalized h u h.load

include h hk in
theorem slack : W * (Fintype.card q.val.G.V * 2 ^ a : ℕ) ≤ σ := by
  have hv : Fintype.card q.val.G.V ≤ 2 ^ T.scheme.m := by
    simpa using Fintype.card_le_of_injective _ q.val.q.core.post.host.injective
  have := positive h
  apply le_of_mul_le_mul_right _ (show (0 : ℝ) < 2 ^ r by positivity)
  apply le_trans _ h.slack
  push_cast
  rw [mul_assoc, mul_assoc (Fintype.card q.val.G.V : ℝ), ← pow_add, Nat.sub_add_cancel h.group, pow_add]
  gcongr
  · exact_mod_cast hk
  · exact_mod_cast hv

include h hC s hk in
theorem ok : Template.Encodes.Fits (G := q.val.G) a t Δ C g (denominator L)
    (Nat.clog 2 (T.scheme.h + 1)) (indices T Δ z B) W (tolerance Δ Y) where
  corePos := by have := s.core; omega
  full := hC
  late hf := by rw [h.full] at hf; cases hf
  gap := by
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk.trans h.room)
    have := h.group
    omega
  depth := Nat.le_pow_clog (by decide : 1 < 2) _
  integer := integer h q
  denominator := Nat.mul_pos h.denom (Nat.two_pow_pos _)
  width := h.zpos.trans_le h.vpos
  margin := by unfold Template.Encodes.margin; have := s.core; positivity
  widthLimit := (limits T Δ z B).1
  weightLimit := (limits T Δ z B).2.1
  capacity := mul_pos (by positivity) (positive h)
  bound v i := normalized h _ (q.property.1.bounded.2.2 v i)
  cdeg := q.property.1.bounded.1
  ndeg := q.property.1.bounded.2.1
  small := s.small

abbrev poll := q.val.q.core.elected (ok h s hC hk q) s.enough s.space (unit h s)
abbrev board := History.Reset.electedBoard q.val.q.core (ok h s hC hk q) s.enough s.space (unit h s)

theorem fits (R : Rotor F Y w) {c : ℝ} (hc : 1 ≤ c) (cost : (Fintype.card R.E : ℝ) ≤ c * Y * w) :
    (poll h s hC hk q).Fits R c where
  upper := hC
  full := q.property.1.bounded.2.1
  nonneg := zero_le_one.trans hc
  cost := cost
  small := by
    change (Detour.steps (terminalWidth Δ Y) : ℝ) * tolerance Δ Y ≤ 1
    unfold tolerance
    rw [mul_one_div, div_le_one (by positivity)]
    exact le_add_of_nonneg_right zero_le_one

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Linear propagation of label lengths under an attached reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Coloring Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "Z" => child R Δ C t d B

abbrev swept (i : I) := (Z i).sweep
abbrev seats (i : I) := slots i.A i.r
abbrev target (i : I) := i.A.shrink (swept R Δ C t d B i) (seats d B i) (copies t B)

theorem swept_bound : Case.Child (swept R Δ C t d B) (shift R Δ d B) := by
  obtain ⟨ha, hm, hg, hk, he, hd, hb, hc⟩ := child_bound R Δ C t d B
  exact ⟨ha, hm, hg, hk, he, hd, hb, hc⟩

theorem seats_bound : Base (fun i : I => 2 ^ seats d B i) := tiles.exp_add stations

private def overhead (i : I) :=
  2 * added R Δ C t d B i + 2 ^ seats d B i *
    (1 + i.A.k + 2 ^ (i.A.spanBits (Z i)) * (2 + (Z i).scheme.d + seats d B i + i.A.spanBits (Z i)))

private theorem overhead_base : Base (overhead R Δ C t d B) := by
  have spans : Base (fun i : I => 2 ^ i.A.spanBits (Z i)) :=
    Width.expMax ports (base_const (2 ^ e t B))
  have slots := seats_bound (F := F) d B
  have hd : Base (fun i : I => (Z i).scheme.d) :=
    (base_const (degree C Y)).mono fun i => (child_degree R Δ C t d B i).le
  have len := (((base_const 2).add hd).add slots.of_exp).add spans.of_exp
  exact ((base_const 2).mul (added_bound R Δ C t d B)).add
    (slots.mul (((base_const 1).add stations.of_exp).add (spans.mul len)))

theorem labels_bound : ∃ J, ∀ i : I,
    (Z i).scheme.ℓ + (target R Δ C t d B i).ℓ ≤ J * (i.T.scheme.ℓ + i.A.ℓ) + i.base ^ J := by
  obtain ⟨k, hk⟩ := (overhead_base R Δ C t d B).bound
  let J := max (2 * copies t B) k
  refine ⟨J, fun i => ?_⟩
  have hg : (target R Δ C t d B i).ℓ = (Z i).scheme.ℓ + copies t B * i.A.ℓ+
      2 ^ seats d B i * (1 + i.A.k + 2 ^ (i.A.spanBits (Z i)) * (2 + (Z i).scheme.d + seats d B i + i.A.spanBits (Z i))) :=
    i.A.short_width _ _ _
  calc
    _ = (2 * copies t B * i.T.scheme.ℓ + copies t B * i.A.ℓ) + overhead R Δ C t d B i := by
      rw [hg, label_eq]
      unfold overhead
      ring
    _ ≤ J * (i.T.scheme.ℓ + i.A.ℓ) + i.base ^ J := by
      have he := i.base_two
      have hc : 2 * copies t B ≤ J := le_max_left _ _
      rw [mul_add]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hc) (Nat.mul_le_mul_right _ (by omega)))
        ((hk i).trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Comparing old and new host names without storing them at every block -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
open Coloring Assembly Width Attachment

variable {κ : Type} [Field κ] {b d B : ℕ} {N : (i : Case κ b d B) → Template i.F}
  {δ j p : Case κ b d B → ℕ} (h : Child N δ) (hj : Short (fun i => 2 ^ j i)) (hp : Short (fun i => 2 ^ p i))
local notation "I" => Case κ b d B

include h hj in
theorem depth : Short (fun i : I => 2 ^ (Attachment.depth (N i) (j i))) :=
  (expMax h.spans hj).exp_add (short_const (2 ^ 1))

include h hp in
private theorem aliases : Short (fun i : I => (Alias.Output i.T.scheme.d (N i).scheme.d (p i)).width) :=
  vec hp (vec Case.slots.short (vec h.neighbors (vec hp bit)))

def incoming (i : I) := 2 ^ i.T.scheme.d * i.m + 2 ^ i.height * i.A.ℓ

def packet (N : (i : I) → Template i.F) (j p : I → ℕ) (i : I) :=
  Inspect.Packet i.m i.T.scheme.d (p i) (N i).scheme.h (i.A.bundle (N i) (j i) (p i))

include h hj hp

private theorem ticket_bound : Short (fun i : I => (i.A.ticket (N i) (j i) (p i)).width) :=
  pair (addr h.bits) (pair bit (h.orders hj hp))

theorem bundle_bound : Short (fun i : I => (i.A.bundle (N i) (j i) (p i)).width) :=
  pair (h.ticket_bound hj hp) (vec (h.depth hj) (addr labels))

theorem review : Short (fun i : I => (i.A.Review (N i) (j i) (p i)).width) :=
  pair (h.aliases hp) (pair (h.bundle_bound hj hp) (vec h.neighbors (h.bundle_bound hj hp)))

theorem rebuildWidth : Short (fun i : I => i.A.rebuildWidth (N i) (j i) (p i)) :=
  (h.review hj hp).add (h.transport hj)

theorem packet_bound : Row (fun i : I => (packet N j p i).width) := by
  have host : Row (fun i : I => (Format.addr i.m).width) := Long.row (addr hosts)
  exact pack (many hp host) (pack (many hp (many Case.slots.short host)) (h.stack (h.bundle_bound hj hp)))

theorem inputs : Cost (fun i : I => (i.A.Inputs (N i) (j i) (p i)).width) := by
  have ask := vec (h.depth hj) (pair (addr hp.of_exp) (addr levels.short))
  have fresh := h.bank (h.stack (pair (h.ticket_bound hj hp) ask))
  exact pack (parent.bank (parent.stack (addr labels))) fresh

private theorem receive_bound : Cost (fun i : I => Receive.cost i.m i.T.scheme.d i.height i.A.ℓ
    (N i).scheme.m (N i).scheme.d (N i).scheme.h (p i) (Attachment.depth (N i) (j i))
    (i.A.ticket (N i) (j i) (p i)) (incoming i) (i.p.fee (i.m + i.T.scheme.d) (incoming i))) := by
  have hd : Short (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.short
  have hw : Row (fun i : I => incoming i) := (Long.row (hd.long.mul hosts)).add labels.block.blocks
  have send := parent.gather hd hw
  have rx := h.bank (h.packet_bound hj hp)
  have work := ((((block_const 100).add levels.short.block).add hp.block).add (h.depth hj).block).add labels.block
  have tail := h.cost ((labels.block.blocks.left hp.block).add (Block.blocks (work.pow 100)))
  exact send.add (((((h.inputs hj hp).add rx).add (hw.expand hd.block)).add tail).scale 500)

private theorem inspect_bound : Cost (fun i : I => Inspect.cost i.m i.T.scheme.d (N i).scheme.m
    (N i).scheme.d (p i) (N i).scheme.h (i.A.bundle (N i) (j i) (p i)) (packet N j p i).width
    (i.p.fee ((N i).scheme.m + (N i).scheme.d) (packet N j p i).width)) := by
  have hd : Short (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.short
  have cv : Row (fun i : I => (Format.addr i.m).width) := Long.row (addr hosts)
  have hw := h.packet_bound hj hp
  have pre := (h.gather h.neighbors hw).add ((h.bank hw).scale 56)
  have rx := h.vector (many h.neighbors hw)
  have query := h.vector (pack (many hp (many hd cv)) (many h.neighbors (many hp cv)))
  have result := h.vector (h.aliases hp).long.row
  have out := h.vector (h.stack (h.review hj hp))
  have work := ((((long_const 100).add hosts).add hd.long).add h.neighbors.long).add hp.long
  exact ((((pre.add (rx.scale 32)).add (query.scale 8)).add (result.scale 4)).add (out.scale 8)).add
    ((h.cost (Long.row (work.pow 100))).scale 4)

theorem rebuildCost : Cost (fun i : I => i.A.rebuildCost (N i) (j i) (p i)
    (incoming i) (i.p.fee (i.m + i.T.scheme.d) (incoming i)) (packet N j p i).width
    (i.p.fee ((N i).scheme.m + (N i).scheme.d) (packet N j p i).width)) := by
  have req := h.requests hj hp
  have query := (req.add ((h.inputs hj hp).scale 34)).scale 4
  have run := (query.add (h.receive_bound hj hp)).add (h.inspect_bound hj hp)
  have print := h.cost (h.layer ((block_const 1).add (h.rebuildWidth hj hp).block))
  exact (((req.scale 24).add (h.format.scale 8)).add run).add print

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Case.Child
end

/-! # Physical and label bounds after a reset with a retained border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    (h : Input A L P p r 1 u u z payload d B K H σ) (s : Slice Δ Y w t)
    (hC : Δ ≤ C) (hk : 2 ^ t ≤ K) (q : (frame A L u z payload Δ C P).state)
local notation "a" => (T.scheme.h - r)
local notation "W" => ((2 : ℝ) ^ t * P.load)
local notation "U" => poll h s hC hk q

include h in
theorem charged : History.Reset.Charged q.val.q.core.post T.order z T.scheme.ℓ := by
  intro j hj
  refine Nat.mul_le_mul (History.Dense.used_le.mpr (Fin.isLt _)) ?_
  let G := q.val.G
  change z ≤ G.past j + G.tetherLoad j + Packing.degree G.pair j * u
  change 0 < G.tetherLoad j + Packing.degree G.pair j * u at hj
  by_cases hd : 0 < Packing.degree G.pair j
  · have ht := h.vpos.trans (Nat.le_mul_of_pos_left u hd)
    omega
  have ht : 0 < G.tetherLoad j := by rw [show Packing.degree G.pair j = 0 by omega, zero_mul, add_zero] at hj; exact hj
  have witness : ∃ i, G.far i = j := by
    let _ : DecidableEq (G.V × Cell T.scheme.h) := Classical.typeDecidableEq _
    unfold HostNet.tetherLoad exterior at ht
    rcases Nat.add_pos_iff_pos_or_pos.mp ht with hx|hy
    · obtain ⟨i, hi⟩ := (Fintype.card_pos_iff.mp hx).some
      exact ⟨.inl i, hi⟩
    · obtain ⟨i, hi⟩ := (Fintype.card_pos_iff.mp hy).some
      exact ⟨.inr i, hi⟩
  obtain ⟨i, rfl⟩ := witness
  have hb := (q.property.1.parallel i).trans (G.parallel_le_tether i)
  omega

theorem gain_eq : 89 * W = gain t * P.load := by
  simp only [gain, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

include h in
theorem gain_le : 89 * W ≤ (gain t * B : ℕ) * (z : ℝ) := by
  rw [gain_eq, Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h.ceiling (by positivity)

variable [NeZero Y] [NeZero w] (R : Rotor F Y w) (hc : 1 ≤ κ)
    (cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w)
local notation "hf" => fits h s hC hk q R hc cost
local notation "Q" => History.Reset.Setup.result U R hf
local notation "G" => History.Reset.Setup.graph U R hf

theorem estimates :
    (∀ x y, (G).diagram.eval x y = q.val.G.diagram.eval x y) ∧
    (G).Bounded 3 (3 + terminalWidth C Y) (gain t * P.load) ∧
    ((G).X : ℝ) ≤ 2 * resetWidth κ w * P.width + 2 * resetWidth κ w * (L.total + σ) ∧
    q.val.G.Preserves G ∧ ((G).mass : ℝ) ≤ P.mass + 2 * P.width := by
  obtain ⟨eval, _, bounds, width, preserve, mass, _⟩ := (U).bounds R hf (slack h hk q)
  refine ⟨eval, ?_, ?_, preserve, ?_⟩
  · rw [← gain_eq]; exact bounds
  · have hσ : 0 ≤ σ := by
      have hp : 0 ≤ P.load := (Nat.cast_nonneg _).trans h.load
      exact nonneg_of_mul_nonneg_left (le_trans (by positivity) h.slack) (by positivity)
    have hr : 0 ≤ resetWidth κ w := by unfold resetWidth; positivity
    refine width.trans ?_
    calc
      _ ≤ resetWidth κ w * (2 * σ + 2 * P.width + 2 * L.total) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (add_le_add (by linarith only [hσ]) (mul_le_mul_of_nonneg_left q.property.1.width (by norm_num)))
          (mul_le_mul_of_nonneg_left q.property.1.total (by norm_num))) hr
      _ = _ := by ring
  · rw [mass, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact add_le_add q.property.1.mass (mul_le_mul_of_nonneg_left q.property.1.width (by norm_num))

theorem mass : (G).mass ≤ q.val.L.cap := by
  rw [q.property.1.cap]
  exact Nat.cast_le.mp ((estimates h s hC hk q R hc cost).2.2.2.2.trans h.history)

theorem room (v : Cell a × (Q).vertex) :
    Fintype.card (History.Reset.Visible q.val.q.core.post Q v) ≤ 2 ^ (e t B) :=
  (History.Reset.seats_fit q.val.q.core.post Q v h.zpos h.vpos q.property.1.span (gain_le h)).2.2.trans
    (Nat.le_pow_clog (by decide) _)

theorem valid : (meter L t z B).Valid G :=
  valid_of_charge h q (gain t) G (mass h s hC hk q R hc cost)
    (estimates h s hC hk q R hc cost).2.1.2.2

variable [Fintype F]
local notation "b" => book T u t z B
local notation "N" => raw R T L u t z Δ C B r

theorem ready (S : History.Reset.Allocation q.val.q.core.post Q (N).scheme)
    (nav : Coloring.B (N).scheme.m → Coloring.B (N).scheme.d → Coloring.B (N).scheme.m)
    (hop : ∀ (i : (Q).Survivors) j,
      let host := History.Reset.Allocation.endHost (q := Q)
      nav (S.host (host i j)) (S.index (host i j) (host i (!j))) = S.host (host i (!j))) :
    (b).Ready S nav := by
  have hd : 2 ^ q.val.L.discount * (gain t * B) ≤ copies t B := by
    rw [q.property.1.discount, copies, mul_assoc]
    exact Nat.mul_le_mul_right _ h.discount
  apply (b).ready S nav _ hop ((U).result_simple R hf) q.property.1.neutral
    (charged h q) h.zpos h.vpos q.property.1.span (mass h s hC hk q R hc cost) (gain_le h)
    (Nat.le_pow_clog (by decide) _) (Nat.add_le_add_left (Nat.mul_le_mul_left _ hd) _)
  intro j
  exact History.Reset.Book.represent T.scheme u (e t B) (cap T t B) T.order (Finset.range (B * z + 1))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (size_bound h q j)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end
