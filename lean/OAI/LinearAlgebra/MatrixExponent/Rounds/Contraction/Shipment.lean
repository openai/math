import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.ShortNet
import OAI.LinearAlgebra.MatrixExponent.Packing.Beat

/-! # Relaxing the degree and resource allowances after a contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction

open Assembly
variable {F k : Type} [Field F] [Field k] {x y : Wire} {T Y : Template F}
  {A : Attachment T} {A' : Attachment Y} {L : BorderLimit F x y}
  {r b u v z payload d B n e K K' H H' Δ Δ' Δ'' C C' : ℕ}
  {ρ c ρ' c' σ : ℝ} {P P' : Bound} {p : Prices F}

theorem relax_frame {X : Snapshot.{1} F x y} {G : Set (Table F)}
    (f : Transforms F H G X (frame A L u z payload Δ C P) n)
    (hd : Δ ≤ Δ') (hc : C ≤ C') (hb : P.load ≤ P'.load)
    (hw : P.width ≤ P'.width) (hm : P.mass ≤ P'.mass) :
    Transforms F H G X (frame A L u z payload Δ' C' P') n := by
  obtain ⟨q, hq, he⟩ := f
  refine ⟨q, hq, fun s => ?_⟩
  obtain ⟨I, _, a, l, ha, hl⟩ := he s
  have h (i : I) : Ready A L z Δ' C' P' (a i).val :=
    { (a i).property.1 with
      simple := fun h => (a i).property.1.simple (hd.trans h)
      bounded := (a i).property.1.bounded.mono hd hc hb
      width := (a i).property.1.width.trans hw
      mass := (a i).property.1.mass.trans hm }
  exact ⟨I, inferInstance, fun i => ⟨(a i).val, h i, (a i).property.2⟩, l, ha, hl⟩

omit [Field F] in
theorem Growth.overhead (g : Growth A A' r z payload n K H) (hk : K ≤ K') :
    Growth A A' r z payload n K' H :=
  { g with upper := g.upper.trans (Nat.add_le_add_left hk _)
           stations := g.stations.trans (Nat.add_le_add_left hk _) }

theorem Phase.block (q : Phase k Δ Δ' b e K ρ c) (hu : 0 < b) (hk : 0 < K)
    (hd : ∀ C, Δ ≤ C → Δ' ≤ C ^ e) (hf : 0 ≤ ρ) (hl : 0 ≤ c) :
    Block k Δ Δ' b 1 e K ρ c := by
  refine ⟨hu, by decide, hk, hd, hf, hl, fun C d B hC => ?_⟩
  obtain ⟨H, hH, run⟩ := q C d B hC
  refine ⟨H, hH, ?_⟩
  intro F _ _ _ x y T A L P p r u v z payload σ h
  obtain ⟨s⟩ := run F A L P p r u v z payload σ h.toInput
  have g : Growth A s.pack r z payload 1 K H :=
    ⟨by simpa only [one_mul] using s.height, s.lower, by simpa only [one_mul] using s.upper,
      s.degree, s.full, s.single, s.spans, by simpa only [one_mul] using s.stations, s.outer, s.counters, s.labels⟩
  refine ⟨⟨s.next, s.pack, g, s.keys, s.few, relax_frame s.transfer le_rfl le_rfl le_rfl le_rfl ?_⟩⟩
  have hx := h.width
  have hs := add_nonneg h.total h.nonneg
  change P.mass + 2 * P.width ≤ P.mass + 2 * K * (P.width + (L.total + σ))
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hk
  nlinarith only [mul_nonneg (sub_nonneg.mpr hK) hx, mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hs]

theorem Start.shrink (h : Start A L P p r b u v z payload d B n K H σ) (hk : K' ≤ K)
    (hh : 0 < H') (hH : H' ≤ H) : Start A L P p r b u v z payload d B n K' H' σ := by
  have hw := h.width
  have hZ := add_nonneg h.total h.nonneg
  have hB := (Nat.cast_nonneg u).trans h.load
  have hs : 0 < short A r z payload := by unfold short base; positivity
  refine { h with
    room := hk.trans h.room
    positive := hh
    small := (Nat.pow_le_pow_right hs hH).trans h.small
    space := (by have := h.space; omega)
    slack := le_trans ?_ h.slack
    reserve := le_trans ?_ h.reserve } <;> gcongr

theorem Block.relax (q : Block k Δ Δ' b n e K ρ c) (hk : K ≤ K') (hρ : ρ ≤ ρ') (hc : c ≤ c') :
    Block k Δ Δ' b n e K' ρ' c' := by
  refine ⟨q.unit, q.steps, q.overhead.trans_le hk, q.degree, q.factor.trans hρ, q.loss.trans hc, fun C d B hC => ?_⟩
  obtain ⟨H, hH, run⟩ := q.run C d B hC
  refine ⟨H, hH, ?_⟩
  intro F _ _ _ x y T A L P p r u v z payload σ h
  obtain ⟨s⟩ := run F A L P p r u v z payload σ (h.shrink hk hH le_rfl)
  have hw := h.width
  have hZ := add_nonneg h.total h.nonneg
  have hb := (Nat.cast_nonneg u).trans h.load
  refine ⟨⟨s.next, s.pack, s.growth.overhead hk, s.keys, s.few,
    relax_frame s.transfer le_rfl le_rfl ?_ ?_ ?_⟩⟩ <;> dsimp only [limit, after] <;> gcongr

theorem Block.degree_mono (q : Block k Δ Δ' b n e K ρ c) (hd : Δ' ≤ Δ'')
    (hf : ∀ C, Δ ≤ C → Δ'' ≤ C ^ e) : Block k Δ Δ'' b n e K ρ c := by
  refine ⟨q.unit, q.steps, q.overhead, hf, q.factor, q.loss, fun C d B hC => ?_⟩
  obtain ⟨H, hH, run⟩ := q.run C d B hC
  refine ⟨H, hH, ?_⟩
  intro F _ _ _ x y T A L P p r u v z payload σ h
  obtain ⟨s⟩ := run F A L P p r u v z payload σ h
  exact ⟨⟨s.next, s.pack, s.growth, s.keys, s.few, relax_frame s.transfer hd le_rfl le_rfl le_rfl le_rfl⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Physical costs of two consecutive blocks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Block

open Assembly
variable {F : Type} {x y : Wire} {T Y : Template F}
  {A : Attachment T} {A' : Attachment Y} {L : BorderLimit F x y}
  {r z payload n K J H : ℕ} {ρ c τ b σ : ℝ} {P : Bound}

/-- The host address can grow by `K` extra bits. Only the charge
for the *first* block is exponentiated. -/
def fee (K : ℕ) (ρ c : ℝ) := K + K * 2 ^ K + ⌈ρ + c + 1⌉₊ + 1

theorem add_fee (hj : 0 < J) : K + J ≤ fee K ρ c * J := calc
  _ ≤ K * J + J := Nat.add_le_add_right (Nat.le_mul_of_pos_right K hj) J
  _ = (K + 1) * J := by ring
  _ ≤ _ := Nat.mul_le_mul_right _ (by unfold fee; omega)

private theorem load_fee : J * K ≤ fee K ρ c * J := by
  rw [mul_comm J]
  exact Nat.mul_le_mul_right _ (by unfold fee; omega)

theorem chain_load (hl : 0 ≤ P.load) :
    (limit L (limit L P K ρ c σ) J τ b σ).load ≤
      (limit L P (fee K ρ c * J) (τ * ρ) (τ * c + b) σ).load := by
  dsimp only [limit, after]
  rw [← mul_assoc, ← Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr load_fee) hl

theorem chain_width :
    (limit L (limit L P K ρ c σ) J τ b σ).width =
      (limit L P (fee K ρ c * J) (τ * ρ) (τ * c + b) σ).width := by
  dsimp only [limit, after]
  ring

theorem chain_mass (hj : 0 < J) (hw : 0 ≤ P.width) (ht : 0 ≤ L.total + σ) (hr : 0 ≤ ρ) (hc : 0 ≤ c) :
    (limit L (limit L P K ρ c σ) J τ b σ).mass ≤
      (limit L P (fee K ρ c * J) (τ * ρ) (τ * c + b) σ).mass := by
  let a := ⌈ρ + c + 1⌉₊
  have hs : ρ * P.width + c * (L.total + σ) + (L.total + σ) ≤ a * (P.width + (L.total + σ)) := calc
    _ ≤ (ρ + c + 1) * (P.width + (L.total + σ)) := by nlinarith only [mul_nonneg hr ht, mul_nonneg hc hw, hw]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (add_nonneg hw ht)
  have hf : K + J * a ≤ fee K ρ c * J := calc
    _ ≤ K * J + J * a := Nat.add_le_add_right (Nat.le_mul_of_pos_right K hj) _
    _ = (K + a) * J := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by unfold fee a; omega)
  dsimp only [limit, after]
  calc
    _ ≤ (P.mass + 2 * K * (P.width + (L.total + σ))) + 2 * J * ((a : ℝ) * (P.width + (L.total + σ))) := by gcongr
    _ = P.mass + 2 * (K + J * a : ℕ) * (P.width + (L.total + σ)) := by push_cast; ring
    _ ≤ _ := by gcongr

theorem chain_seats (g : Growth A A' r z payload n K H) (hl : 0 ≤ P.load) :
    (J : ℝ) * (limit L P K ρ c σ).load * (2 ^ (Y.scheme.m + Y.scheme.h) : ℕ) ≤
      (fee K ρ c * J : ℕ) * P.load * (2 ^ (T.scheme.m + T.scheme.h) : ℕ) := by
  have h : 2 ^ (Y.scheme.m + Y.scheme.h) ≤ (2 ^ K : ℕ) * 2 ^ (T.scheme.m + T.scheme.h) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by have := g.upper; have := g.height; omega)
  have hf : K * 2 ^ K * J ≤ fee K ρ c * J := Nat.mul_le_mul_right _ (by unfold fee; omega)
  change (J : ℝ) * (K * P.load) * _ ≤ _
  calc
    _ ≤ (J : ℝ) * (K * P.load) * (2 ^ K * 2 ^ (T.scheme.m + T.scheme.h) : ℕ) := by gcongr
    _ = (K * 2 ^ K * J : ℕ) * P.load * (2 ^ (T.scheme.m + T.scheme.h) : ℕ) := by push_cast; ring
    _ ≤ _ := by gcongr

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Block
end

/-! # Reserving wire histories within the frozen-charge bound -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing

namespace Contraction

private def allowance (s : Plan) := 2 * s.K * (s.A * (1 + s.d) ^ 2 + s.A + 1)

def reserve (s : Plan) (L : ℝ) : ℕ := ⌈(allowance s : ℝ) * L⌉₊

/-- One extra unit in the coefficient covers rounding the cap when `1 ≤ L`. -/
def discount (s : Plan) := Nat.clog 2 ((allowance s + 1) * s.D)

variable {s : Plan} {L : ℝ}

theorem le_reserve (hs : s.Fits) (hL : 1 ≤ L) :
    2 * s.K * (s.A * (1 + (s.d : ℝ)) ^ 2 * L + (s.A / Real.sqrt s.D * L + L / s.D)) ≤ reserve s L := by
  have hd : (1 : ℝ) ≤ s.D := Nat.one_le_cast.mpr (le_trans (by decide) (s.two hs))
  calc
    _ ≤ 2 * s.K * (s.A * (1 + (s.d : ℝ)) ^ 2 * L + (s.A * L + L)) := by
      gcongr
      · exact div_le_self (Nat.cast_nonneg _) (Real.one_le_sqrt.mpr hd)
      · exact div_le_self (by linarith) hd
    _ = (allowance s : ℝ) * L := by unfold allowance; push_cast; ring
    _ ≤ _ := Nat.le_ceil _

theorem discount_bound (hs : s.Fits) (hL : 1 ≤ L) :
    s.C * (10000 * L) / Real.sqrt s.D + (reserve s L : ℝ) / (2 : ℝ) ^ (discount s) ≤
      s.A / Real.sqrt s.D * L := by
  have hd : (1 : ℝ) ≤ s.D := Nat.one_le_cast.mpr (le_trans (by decide) (s.two hs))
  have hcap : (reserve s L : ℝ) ≤ (allowance s + 1) * L := calc
    _ ≤ (allowance s : ℝ) * L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ _ := by linarith
  have hsize : ((allowance s : ℝ) + 1) * s.D ≤ (2 : ℝ) ^ (discount s) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ((allowance s + 1) * s.D)
  have small : (reserve s L : ℝ) / (2 : ℝ) ^ (discount s) ≤ L / Real.sqrt s.D := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ ((allowance s : ℝ) + 1) * L * s.D :=
        mul_le_mul hcap (Real.sqrt_le_self_iff.mpr (.inr hd)) (by positivity) (by positivity)
      _ = L * (((allowance s : ℝ) + 1) * s.D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize (by positivity)
  calc
    _ ≤ s.C * (10000 * L) / Real.sqrt s.D + L / Real.sqrt s.D := add_le_add_right small _
    _ = ((s.C : ℝ) * 10000 + 1) / Real.sqrt s.D * L := by ring
    _ ≤ _ := by gcongr; simp [Plan.A]; linarith

end Contraction

open scoped Classical

theorem Concentrated.reserve {F : Type} {x y : Wire} {h u : ℕ}
    {Q : LocalTerm F x y h u} {s : Plan} (hs : s.Fits) {L : ℝ} {T R g : ℕ}
    {P : Input F x y h s.D T R g (10000 * L)} (hq : Concentrated P Q s.C s.d 10)
    (hL : 1 ≤ L) (hT : 0 < T) (hu : 0 < u) :
    Fringe.Z { Q.fringe (s.two hs) with
      cap := Contraction.reserve s L, discount := Contraction.discount s } ≤ s.A / Real.sqrt s.D * L ∧
      ((Q.host (s.two hs) hu).X : ℝ) ≤ s.A * (1 + (s.d : ℝ)) ^ 2 * L := by
  refine ⟨?_, (hq.raw hs (by positivity) hT hu).2⟩
  refine le_trans ?_ (Contraction.discount_bound hs hL)
  apply add_le_add _ le_rfl
  exact (le_add_of_nonneg_right (Fringe.reserve_nonneg _)).trans (hq.frozen_mass (s.two hs) hT)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # From a concentrated term to a restorable attached core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing Finset

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
    (A : Attachment D) (s : Plan) (T : ℕ) (L : ℝ) (z payload : ℕ)

structure Protected {I : Type} [Fintype I] {a b : Wire}
    (G : Fringe a b I) (Z : Border F I x y a b) : Prop where
  cover : ∀ i, (wd (Z.table i).1 + wd (Z.table i).2.1 : ℕ) ≤ G.charge i
  square : (∑ i, G.charge i ^ 2) ≤ (s.A : ℝ) * L * T
  maximum : ∀ i, G.charge i ≤ (s.A : ℝ) * s.D * T
  fixed : ∀ i, G.charge i ≤ (s.C : ℝ) * s.D * T

abbrev fringe : BorderLimit F x y where
  denom := s.D ^ 4
  discount := discount s
  cap := reserve s L
  total := s.A / Real.sqrt s.D * L
  test _ _ _ _ G Z := Protected s T L G Z

abbrev origin : Bound := ⟨T / s.D, s.A * (1 + (s.d : ℝ)) ^ 2 * L, 0⟩

abbrev destination : Bound :=
  ⟨T, (s.ρ * s.A * (1 + (s.d : ℝ)) ^ 2 + s.loss * ((s.A + 1) / Real.sqrt s.D)) * L, reserve s L⟩

abbrev initial := frame (x := x) (y := y) A (fringe s T L) (s.b * z) z payload s.c (s.D ^ s.c) (origin s T L)
abbrev final := frame (x := x) (y := y) A (fringe s T L) z z payload 3 s.full (destination s T L)

variable {A s T L z payload}

theorem allocation (hs : s.Fits) (hz : 0 < z) (hunit : T ≤ z * s.M)
    (X : (final (x := x) (y := y) A s T L z payload).state) :
    Nonempty (X.val.G.Restore s.full s.slots s.slots) := by
  have h := X.property.1
  have hd : (1 : ℝ) ≤ s.D := by exact_mod_cast (show 1 ≤ s.D by have := s.two hs; omega)
  have hcap := s.slots_cover hs T z hunit
  have lower (i : X.val.T) : (z : ℝ) ≤ X.val.L.charge i := by
    obtain ⟨n, hn, he⟩ := h.charge i
    rw [he]
    exact Nat.cast_le.mpr hn
  have upper (i : X.val.T) : X.val.L.charge i ≤ (s.slots : ℝ) * z := calc
    _ ≤ (s.C : ℝ) * s.D * T := h.test.fixed i
    _ ≤ (s.D : ℝ) ^ 2 * T := by
      rw [pow_two]
      gcongr
      exact s.small.trans hs.degree
    _ ≤ (s.D : ℝ) ^ 4 * T := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd (by decide)) (Nat.cast_nonneg _)
    _ ≤ _ := hcap
  have ha : (T : ℝ) ≤ X.val.L.scale * (s.slots * (z : ℝ)) := by
    rw [h.scale, show (fringe (F := F) (x := x) (y := y) s T L).denom = s.D ^ 4 from rfl,
      Nat.cast_pow, one_div_mul_eq_div, le_div_iff₀ (by positivity), mul_comm (T : ℝ)]
    exact hcap
  exact X.val.G.restore s.full s.slots s.slots T z (Nat.cast_pos.mpr hz) h.bounded ha
    (fun i => ⟨lower i, upper i⟩) (fun i => Nat.cast_le.mpr (h.parallel i))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# Concentration bounds for a specified ordering of the core packets

The presentation fixes a packet order. Changing this order leaves the
initial charge, core width and parallel tether counts unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing
open scoped Classical

variable {F : Type} {x y : Wire} {h u : ℕ} {s : Plan} (hs : s.Fits)
    (L : ℝ) (Q : LocalTerm F x y h u)

abbrev frozen : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed :=
  { Q.fringe (s.two hs) with cap := reserve s L, discount := discount s }

variable (hu : 0 < u) (E : Packets Q.freeze.core u)

abbrev hosted := Q.frame.hostOf hu (frozen hs L Q) rfl E

local notation "G" => hosted hs L Q hu E
local notation "old" => Q.host (s.two hs) hu

theorem hosted_load (v : Q.V) (i : Cell h) : (G).load v i = (old).load v i := by
  have hae := HostNet.load_eq (G) (v, i)
  have hbe := HostNet.load_eq (old) (v, i)
  rw [show (G).past (v, i) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero] at hae
  rw [show (old).past (v, i) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero] at hbe
  exact hae.trans hbe.symm

theorem hosted_width : (G).X = (old).X := by
  have he := Fintype.card_congr ((G).units.bits.symm.trans (old).units.bits)
  simpa only [HostNet.X, Fintype.card_prod, Fintype.card_fin] using he

variable {L Q} {R T g : ℕ} {P : Rounds.Input F x y h s.D T R g (10000 * L)}
    (hc : Concentrated P Q s.C s.d 10)

include hc in
theorem protected_charge (hL : 0 ≤ L) : Protected s T L (frozen hs L Q) Q.freeze.border where
  cover i := Q.cover i.val
  square := hc.frozenSquare.trans (mul_le_mul_of_nonneg_right (by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right s.cost_le hL) (Nat.cast_nonneg T))
  maximum i := by
    refine (hc.frozenMax i).trans ?_
    gcongr
    unfold Plan.A
    omega
  fixed := hc.frozenMax

include hc in
theorem hosted_bounded : (G).Bounded s.c (s.D ^ s.c) (origin s T L).load := by
  have hd := s.two hs
  have t := (hc.bounded hd hu (s.small.trans hs.degree)).mono s.small
    (Nat.pow_le_pow_right (by omega) s.small) le_rfl
  exact ⟨t.1, t.2.1, fun v i => (hosted_load hs L Q hu E v i).le.trans (t.2.2 v i)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Admitting a posted term of the concentration expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
    {A : Attachment D} {s : Plan} {z : ℕ} (hs : s.Fits) (L : ℝ)
    (Q : LocalTerm F x y D.scheme.h (s.b * z)) (hu : 0 < s.b * z) (E : Packets Q.freeze.core (s.b * z))
    {rows : A.format.obj} (q : A.Encloses rows (hosted hs L Q hu E) Q.freeze.border)

abbrev incoming : Attachment.Data A x y (s.b * z) where
  T := Q.freeze.Fixed
  a := Q.freeze.x
  b := Q.freeze.y
  L := frozen hs L Q
  G := hosted hs L Q hu E
  Z := Q.freeze.border
  raw := rows
  q := q

variable {L Q hu E} {T R g : ℕ} {P : Rounds.Input F x y D.scheme.h s.D T R g (10000 * L)}
local notation "X" => incoming hs L Q hu E q

theorem incoming_ready (hc : Concentrated P Q s.C s.d 10) (hL : 1 ≤ L) (hT : 0 < T)
    (hv : Nonempty Q.V) (hn : (X).Neutral)
    (hspan : ∀ j, s.b * z ≤ q.core.post.toPresentation.borderWidth j)
    (hi : ∀ i : Q.freeze.Fixed, ∃ n : ℕ, Q.charge i.val = n) :
    Ready A (fringe s T L) z s.c (s.D ^ s.c) (origin s T L) X := by
  have hz : z ≤ s.b * z := Nat.le_mul_of_pos_left z (Nat.pos_of_mul_pos_right hu)
  have hr := hc.reserve hs hL hT hu
  refine ⟨hn, hv, (by intro h; unfold Plan.c at h; omega), hspan, ?_, ?_, rfl, rfl, hr.1, ?_,
    protected_charge hs hc (by positivity), hosted_bounded hs hu E hc, ?_, ?_⟩
  · intro i
    exact hz.trans (Q.parallel (s.two hs) hu i)
  · change 1 / (s.D : ℝ) ^ 4 = 1 / (s.D ^ 4 : ℕ)
    rw [Nat.cast_pow]
  · intro i
    obtain ⟨n, he⟩ := hi i
    refine ⟨n, hz.trans ?_, he⟩
    exact Nat.cast_le.mp ((Q.floor i.val).trans_eq he)
  · change ((hosted hs L Q hu E).X : ℝ) ≤ _
    rw [hosted_width]
    exact hr.2
  · change (↑(∑ _ : Q.V × Cell D.scheme.h, (0 : ℕ)) : ℝ) ≤ 0
    rw [Finset.sum_const_zero, Nat.cast_zero]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Running the core contractions at the scale of a complete round -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly

variable {F k : Type} [Field F] [Field k] {x y : Wire} {D : Template F}

/-- The output carries the same exterior records and frozen-charge bounds. -/
structure Result (A : Attachment D) (s : Plan) (T : ℕ) (L : ℝ) (z payload : ℕ)
    (p : Prices F) (r H : ℕ) where
  next : Template F
  pack : Attachment next
  growth : Growth A pack r z payload s.n s.K H
  keys : Finset (Table F)
  few : keys.card ≤ (short A r z payload) ^ H
  transfer : Transforms F ((short A r z payload) ^ H) keys (initial (x := x) (y := y) A s T L z payload)
    (final pack s T L z payload) (size (x := x) (y := y) A p r z payload H)

private def ceiling (s : Plan) := s.M + s.D ^ 4 + 2 ^ discount s

theorem reduce {s : Plan} (hs : s.Fits)
    (q : Block k s.c 3 s.b s.n s.e s.K s.ρ s.loss) (d : ℕ) :
    ∃ H, 0 < H ∧ ∀ (F : Type) [Field F] [Fintype F] [Algebra k F]
      {x y : Wire} {D : Template F} (A : Attachment D) (T : ℕ) (L : ℝ)
      (z payload : ℕ) (p : Prices F) (r : ℕ),
      1 ≤ L → 0 < z → (s.b * z) * s.D ^ s.c ≤ T → T ≤ z * s.M → s.n * r ≤ D.scheme.h → s.K ≤ 2 ^ r →
      (s.K : ℝ) * T * (2 ^ (D.scheme.m + D.scheme.h) : ℕ) ≤ L * (2 : ℝ) ^ r →
      D.scheme.d ≤ d → D.full = true → D.scheme.k = 0 →
      Nat.clog 2 (Nat.card F) ≤ 2 ^ r → 4 * D.scheme.h ≤ D.scheme.m →
      (short A r z payload) ^ H ≤ D.scheme.m → 2 * (D.scheme.m + s.n * r + s.K) ≤ p.w →
      Nonempty (Result (x := x) (y := y) A s T L z payload p r H) := by
  have hd : (1 : ℝ) ≤ s.D := by exact_mod_cast (show 1 ≤ s.D by have := s.two hs; omega)
  have hd₀ : (0 : ℝ) < s.D := zero_lt_one.trans_le hd
  have hdeg := Nat.le_self_pow (show s.c ≠ 0 by unfold Plan.c; omega) s.D
  obtain ⟨H, hH, run⟩ := q.run (s.D ^ s.c) d (ceiling s) (hs.degree.trans hdeg)
  refine ⟨H, hH, ?_⟩
  intro F _ _ _ x y D A T L z payload p r hL hz hunit hunit' hlen hroom slack hc hf hk hal hfour hsmall hspace
  let X : BorderLimit F x y := fringe s T L
  let P := origin s T L
  have hu : (s.b * z : ℕ) ≤ P.load := (le_div_iff₀ hd₀).mpr (by
    exact_mod_cast (Nat.mul_le_mul_left (s.b * z) hdeg).trans hunit)
  have hmax : P.load ≤ ceiling s * (z : ℝ) := calc
    _ ≤ (T : ℝ) := div_le_self (by positivity) hd
    _ ≤ (z : ℝ) * s.M := by exact_mod_cast hunit'
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (by unfold ceiling; have := Nat.zero_le (2 ^ discount s); omega)) (by positivity)
  have ht : 0 ≤ X.total := by unfold X fringe; positivity
  have hw : 0 ≤ P.width := by unfold P origin; positivity
  have hσ : 0 ≤ L / s.D := by positivity
  have hK : (1 : ℝ) ≤ s.K := by exact_mod_cast q.overhead
  have hres : P.mass + 2 * s.K * (P.width + (X.total + L / s.D)) ≤ X.cap := by
    simpa only [P, origin, zero_add, X, fringe] using le_reserve hs hL
  have hhist : P.mass + 2 * P.width ≤ X.cap := by
    refine le_trans ?_ hres
    nlinarith only [mul_nonneg (sub_nonneg.mpr hK) hw,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) s.K) (add_nonneg ht hσ)]
  have hsl : (s.K : ℝ) * P.load * (2 ^ (D.scheme.m + D.scheme.h) : ℕ) ≤ L / s.D * (2 : ℝ) ^ r := by
    change (s.K : ℝ) * (T / (s.D : ℝ)) * _ ≤ _
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right slack hd₀.le
  have pre : Start A X P p r s.b (s.b * z) z z payload d (ceiling s) s.n s.K H (L / s.D) :=
    ⟨⟨rfl, hz, le_rfl, hu, hmax, (by change 0 < s.D ^ 4; have := s.two hs; positivity),
      (Nat.le_add_left ..).trans (Nat.le_add_right ..), Nat.le_add_left .., ht,
      (Nat.le_mul_of_pos_left _ q.steps).trans hlen, hroom, hc, hf, hk, hH, hal, hfour,
      hsmall, (by omega), hw, le_rfl, hhist, hsl⟩, hσ, hlen, hspace, hres⟩
  obtain ⟨v⟩ := run F A X P p r (s.b * z) z z payload _ pre
  refine ⟨⟨v.next, v.pack, v.growth, v.keys, v.few, relax_frame v.transfer le_rfl (pow_mul ..).ge ?_ ?_ hres⟩⟩
  · change (s.K : ℝ) * (T / (s.D : ℝ)) ≤ T
    rw [← mul_div_assoc, div_le_iff₀ hd₀, mul_comm (T : ℝ)]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs.overhead) (by positivity)
  · have hh : L / (s.D : ℝ) ≤ L / Real.sqrt s.D :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (Real.sqrt_le_self_iff.mpr (.inr hd))
    calc
      _ ≤ s.ρ * P.width + s.loss * (X.total + L / Real.sqrt s.D) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh) q.loss)
      _ = _ := by dsimp only [P, origin, X, fringe, destination]; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# The cost of a transfer using wide tagged permutation

Pad the control width past the sorting threshold. The bound on
the number of contacts pays for the dyadic payload transfer as well.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
open Assembly Coloring

variable {F : Type} [Field F] (W : Prices F)

def transferCost (m V k m' V' k' p : ℕ) :=
  let q := max k k'
  500000 * ((102 + q) ^ 8 + W.W) * (q + 1) ^ 2 * (1 + (V + V') + 2 ^ p * (2 ^ m + 2 ^ m') * (W.w ^ W.power + W.w + 1))

def shipment (size m V k m' V' k' p l n : ℕ) :=
  let v := (Payload.Script.item l p n).width + W.w ^ W.power
  4 * size + (Payload.Script.cost m k m' k' p l v (W.W * (2 ^ m * v)) (W.W * (2 ^ m' * v)) +
    Payload.Script.commandCost m V k m' V' k' (2 ^ p) p l n) +
    W.transferCost m V k m' V' k' p

variable {I : Type*} {X Y : Format} {x : I → X.obj} {y : I → Y.obj} {weight : I → F}
  {u s : ℕ} {L : Set (Table F)} {m V k m' V' k' p l n : ℕ}
local notation "Ch" => PeerLayout.S m V k m' V' k' (2 ^ p)
local notation "Cmd" => Payload.Script m m' p l n

private theorem kernel (hu : 3 ≤ u) (ht : 2 ^ p * ((max k k' + 1) * (2 ^ m + 2 ^ m')) < 2 ^ W.w) :
    Kernel F u L ((Ch).control.pair (Fmt.payload m V k)) (Fmt.payload m' V' k')
      ((Ch).kernel F) (W.transferCost m V k m' V' k' p) := by
  have h := payload_kernel (K := F) (L := L) m V k m' V' k' (2 ^ p) hu ht W.tag
  simp only [payloadChannels] at h
  unfold PeerLayout.S PeerLayout.P transferCost
  exact h

theorem ship {cmd : I → (Cmd).obj} {f : I → (Fmt.payload m V k).obj} {g : I → (Fmt.payload m' V' k').obj}
    (hu : 3 ≤ u) (hm : 1 ≤ m) (hm' : 1 ≤ m') (ht : 2 ^ p * ((max k k' + 1) * (2 ^ m + 2 ^ m')) < 2 ^ W.w)
    (h : Computes F u L X (.pair Y Cmd) x (fun i => (y i, cmd i)) weight s)
    (ok : ∀ i b, (Ch).Carries (Payload.Script.decode le_rfl (cmd i)) (f i) b ↔ g i = b) :
    Computes F u L (.pair X (Fmt.payload m V k)) (.pair Y (Fmt.payload m' V' k'))
      (fun i => (x i, f i)) (fun i => (y i, g i)) weight (s + W.shipment Y.width m V k m' V' k' p l n) := by
  let v := (Payload.Script.item l p n).width + W.w ^ W.power
  have width : 2 ^ m + 2 ^ m' < 2 ^ W.w :=
    ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (Nat.le_mul_of_pos_left _ (by positivity))).trans_lt ht
  have a : m ≤ W.w := ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.le_add_right _ _).trans_lt width)).le
  have b : m' ≤ W.w := ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.le_add_left _ _).trans_lt width)).le
  obtain ⟨q, hq, h₁⟩ := W.tag m v hm a (Nat.le_add_left ..)
  obtain ⟨r, hr, h₂⟩ := W.tag m' v hm' b (Nat.le_add_left ..)
  have hh := h.shipped ok hu h₁ h₂ (Nat.le_add_right _ _) (W.kernel hu ht)
  refine hh.mono ?_
  have he : Payload.Script.cost m k m' k' p l v q r ≤
      Payload.Script.cost m k m' k' p l v (W.W * (2 ^ m * v)) (W.W * (2 ^ m' * v)) := by
    unfold Payload.Script.cost
    gcongr
  rw [add_assoc s]
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.add_le_add_right he _) _) _) _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
end

/-! # Compacting the frozen selectors after either elementary phase -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Packing Assembly
variable {F : Type} [Field F] {T Y : Template F} {A : Attachment T} {x y : Wire}
  {L : BorderLimit F x y} {k N u z payload Δ C : ℕ} {P : Bound}

theorem Ready.shrink {s : (A.transport Y k).Data x y u}
    (h : Ready (A.transport Y k) L z Δ C P s) (hs : A.Sparse Y k N s.raw) :
    Ready (A.shrink Y k N) L z Δ C P (s.shrink hs) where
  neutral := h.neutral
  live := h.live
  simple := h.simple
  span := by
    change ∀ j, u ≤ (s.q.shrink hs).core.post.toPresentation.borderWidth j
    rw [s.q.shrink_core hs]
    exact h.span
  parallel := h.parallel
  scale := h.scale
  discount := h.discount
  cap := h.cap
  total := h.total
  charge := h.charge
  test := h.test
  bounded := h.bounded
  width := h.width
  mass := h.mass

abbrev interim (A : Attachment T) (Y : Template F) (k N : ℕ) (L : BorderLimit F x y)
    (u z payload Δ C : ℕ) (P : Bound) :=
  (A.transport Y k).frame x y u payload
    (fun s => Ready (A.transport Y k) L z Δ C P s ∧ A.Sparse Y k N s.raw)

theorem shrink {n : ℕ} {W : Set (Table F)} (hu : 3 ≤ n)
    (fit : A.shrinkWidth Y k N ≤ n) (allow : A.shrinkGate Y k N ∈ W) :
    Transforms F n W (interim A Y k N L u z payload Δ C P)
      (frame (A.shrink Y k N) L u z payload Δ C P) (A.shrinkCost Y k N x y payload) :=
  Attachment.shrink_frames hu fit allow (fun _ h => h.2) (fun _ h => h.1.shrink h.2)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # The available reserves and address space at the intermediate boundary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Block
variable {F : Type} [Field F] {x y : Wire} {T Y : Template F}
  {A : Attachment T} {A' : Attachment Y} {L : BorderLimit F x y}
  {r b b' u v z payload d B n n' K J H G H' : ℕ}
  {ρ c σ : ℝ} {P : Bound} {p : Prices F}

variable (h : Start A L P p r (b * b') u v z payload d B (n + n') (fee K ρ c * J) G σ)

include h

theorem Start.first (hb : 0 < b') (hj : 0 < J) (hh : 0 < H) (hH : H ≤ G) :
    Start A L P p r b u (b' * v) z payload d B n K H σ := by
  have hk := (Nat.le_add_right K J).trans (add_fee (ρ := ρ) (c := c) hj)
  have f := h.shrink hk hh hH
  have hn := Nat.mul_le_mul_right r (Nat.le_add_right n n')
  exact { f with
    units := by rw [h.units, mul_assoc]
    vpos := h.vpos.trans (Nat.le_mul_of_pos_left _ hb)
    height := hn.trans f.height
    space := by have := f.space; omega }

theorem Start.second (hb : 0 < b) (hn : 0 < n') (hk : 0 < K) (hj : 0 < J)
    (hr : 0 ≤ ρ) (hc : 0 ≤ c) (hh : 0 < H') (g : Growth A A' r z payload n K H)
    (hs : (short A' r z payload) ^ H' ≤ (short A r z payload) ^ G) :
    Start A' L (limit L P K ρ c σ) p r b' (b' * v) v z payload H (K * B) n' J H' σ := by
  let Q := limit L P K ρ c σ
  have hfee := add_fee (K := K) (ρ := ρ) (c := c) hj
  have hw := h.width
  have ht := add_nonneg h.total h.nonneg
  have hl := (Nat.cast_nonneg u).trans h.load
  have hw' : 0 ≤ Q.width := add_nonneg (mul_nonneg hr hw) (mul_nonneg hc ht)
  have hm' : 0 ≤ Q.mass := by
    have := h.mass
    unfold Q limit
    positivity
  have hn' : n' * r ≤ Y.scheme.h := by
    have := g.height
    have ht := h.height
    rw [add_mul] at ht
    omega
  have hspace : 2 * (Y.scheme.m + n' * r + J) ≤ p.w := by
    have := g.upper
    have ht := h.space
    rw [add_mul] at ht
    omega
  have hreserve : Q.mass + 2 * J * (Q.width + (L.total + σ)) ≤ L.cap :=
    (chain_mass (τ := 0) (b := 0) hj hw ht hr hc).trans h.reserve
  have hKK : (1 : ℝ) ≤ K := by exact_mod_cast hk
  have hJJ : (1 : ℝ) ≤ J := by exact_mod_cast hj
  refine ⟨⟨rfl, h.zpos, h.vpos, ?_, ?_, h.denom, h.scale.trans (Nat.le_mul_of_pos_left _ hk),
    h.discount.trans (Nat.le_mul_of_pos_left _ hk), h.total, (Nat.le_mul_of_pos_left _ hn).trans hn',
    (Nat.le_add_left J K).trans (hfee.trans h.room), g.degree, g.full, g.single, hh, h.alphabet,
    (by have := h.four; have := g.height; have := g.lower; omega), hs.trans (h.small.trans g.lower),
    (by omega), hw', hm', ?_, (chain_seats g hl).trans h.slack⟩, h.nonneg, hn', hspace, hreserve⟩
  · have hv : b' * v ≤ u := by rw [h.units, mul_assoc]; exact Nat.le_mul_of_pos_left _ hb
    exact ((Nat.cast_le.mpr hv).trans h.load).trans (le_mul_of_one_le_left hl hKK)
  · change K * P.load ≤ (K * B : ℕ) * (z : ℝ)
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h.ceiling (Nat.cast_nonneg _)
  · change Q.mass + 2 * Q.width ≤ L.cap
    refine le_trans ?_ hreserve
    nlinarith only [mul_nonneg (sub_nonneg.mpr hJJ) hw', mul_nonneg (Nat.cast_nonneg (α := ℝ) J) ht]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-!
# Composing contractions with frozen vertices

Form the union of the two finite sets of labels. Since both
transformations use the same border and intermediate port order,
composition sums exactly over the intermediate records.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly
open scoped Classical

variable {F k : Type} [Field F] [Field k] {x y : Wire} {T : Template F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r u v w z payload Δ Δ' Δ'' C C' C'' b b' n n' e e' K J H H' : ℕ} {ρ c τ a σ : ℝ}

private theorem Stop.chain (s : Stop A L P p r u v z payload Δ Δ' C C' n K H ρ c σ)
    (t : Stop s.pack L (limit L P K ρ c σ) p r v w z payload Δ' Δ'' C' C'' n' J H' τ a σ)
    (hj : 0 < J) (hl : 0 ≤ P.load) (hw : 0 ≤ P.width) (ht : 0 ≤ L.total + σ)
    (hr : 0 ≤ ρ) (hc : 0 ≤ c) :
    Nonempty (Stop A L P p r u w z payload Δ Δ'' C C'' (n + n') (Block.fee K ρ c * J)
      (Growth.join n K H H') (τ * ρ) (τ * c + a) σ) := by
  let U := s.keys ∪ t.keys
  let h := s.growth.keys H'
  have h₁ := (Nat.le_add_right ..).trans h
  have h₂ := (Nat.le_add_left ..).trans h
  have f := s.transfer.widen (L' := ↑U) h₁ (fun _ he => Finset.mem_union_left _ he)
  have g := t.transfer.widen (L' := ↑U) h₂ (fun _ he => Finset.mem_union_right _ he)
  refine ⟨⟨t.next, t.pack, (s.growth.comp t.growth).overhead (Block.add_fee hj), U,
    (Finset.card_union_le ..).trans ((Nat.add_le_add s.few t.few).trans h), ?_⟩⟩
  exact relax_frame ((f.comp g).mono (s.growth.cost H' p)) le_rfl le_rfl
    (Block.chain_load hl) Block.chain_width.le (Block.chain_mass hj hw ht hr hc)

theorem Block.comp (s : Block k Δ Δ' b n e K ρ c) (t : Block k Δ' Δ'' b' n' e' J τ a) :
    Block k Δ Δ'' (b * b') (n + n') (e * e') (Block.fee K ρ c * J) (τ * ρ) (τ * c + a) := by
  have hp := (Nat.add_pos_left s.overhead J).trans_le (Block.add_fee (ρ := ρ) (c := c) t.overhead)
  refine ⟨Nat.mul_pos s.unit t.unit, Nat.add_pos_left s.steps _, hp, ?_, mul_nonneg t.factor s.factor,
    add_nonneg (mul_nonneg t.factor s.loss) t.loss, fun C d B hC => ?_⟩
  · intro C hC
    rw [pow_mul]
    exact t.degree _ (s.degree C hC)
  obtain ⟨H, hH, step⟩ := s.run C d B hC
  obtain ⟨H', hH', next⟩ := t.run (C ^ e) H (K * B) (s.degree C hC)
  have hs := (Nat.le_add_right H H').trans (Growth.add_le n K H H')
  refine ⟨Growth.join n K H H', hH.trans_le hs, ?_⟩
  intro F _ _ _ x y T A L P p r u v z payload σ h
  obtain ⟨f⟩ := step F A L P p r u (b' * v) z payload σ (h.first t.unit t.overhead hH hs)
  have h' := h.second s.unit t.steps s.overhead t.overhead s.factor s.loss hH' f.growth
    ((Nat.le_add_left ..).trans (f.growth.keys H'))
  obtain ⟨g⟩ := next F f.pack L _ p r (b' * v) v z payload σ h'
  rw [pow_mul]
  exact f.chain g t.overhead ((Nat.cast_nonneg u).trans h.load) h.width
    (add_nonneg h.total h.nonneg) s.factor s.loss

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Repeated contraction and degree reset on an attached core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Packing

variable {k : Type} [Field k]

private theorem subrounds (sub : SubroundRule k) (P : Gadget k) (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (t : ℕ) (ht : 0 < t) :
    ∃ K c, Block k Δ (Δ ^ (degreePower ^ t)) (P.b ^ t) t (degreePower ^ t) K (P.ratio ^ t) c := by
  have step (D : ℕ) (hd : 3 ≤ D) :
      ∃ K, Block k D (D ^ degreePower) P.b 1 degreePower K P.ratio 1 := by
    obtain ⟨K, hK, p⟩ := sub P D hd
    exact ⟨K, p.block P.pos hK (fun _ h => Nat.pow_le_pow_left h _) P.ratio_bounds.1 zero_le_one⟩
  have : 0 < degreePower := by decide
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨K, p⟩ := step Δ hΔ
    exact ⟨K, 1, by simpa only [pow_one] using p⟩
  | succ t _ ih =>
    obtain ⟨K, c, p⟩ := ih
    obtain ⟨K', q⟩ := step (Δ ^ (degreePower ^ t)) (hΔ.trans (Nat.le_self_pow (by positivity) _))
    have h := p.comp q
    rw [← pow_mul Δ (degreePower ^ t) degreePower, ← pow_succ degreePower,
      ← pow_succ P.b, ← pow_succ' P.ratio] at h
    exact ⟨_, _, h⟩

private theorem beat (sub : SubroundRule k) (reset : ResetRule k) (tag : Radix.WideTag k)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ∃ b n e K c, 0 < e ∧ Block k Δ 3 b n e K (1 / 2) c := by
  obtain ⟨P⟩ := gadget_exists k
  obtain ⟨t, y, w, R, c, ht, hw, hc, hsize, en, hdecay⟩ :=
    choose_rotor (.inl tag) Δ degreePower P.ratio 250 P.ratio_bounds.1 P.ratio_bounds.2 (by norm_num)
  obtain ⟨K, a, p⟩ := subrounds sub P Δ hΔ t ht
  have : 0 < degreePower := by decide
  let D := Δ ^ (degreePower ^ t)
  have hd : 3 ≤ D := hΔ.trans (Nat.le_self_pow (by positivity) _)
  have enough : 4 * coreBins D ≤ 2 ^ y := by
    simpa only [coreBins, mul_assoc] using en D le_rfl
  obtain ⟨K', hK', q⟩ := reset y w D R c hw hd enough hc
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsize)
  have hp : 0 ≤ 2 * resetWidth c w := by unfold resetWidth; positivity
  have q' := q.block (by decide) hK'
    (fun C hC => (hd.trans hC).trans (Nat.le_self_pow (by positivity) C)) hp hp
  have bound : 2 * resetWidth c w ≤ 250 * (1 + c + Nat.clog 2 w) := by
    unfold resetWidth
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 w)]
  have decrease := (mul_le_mul_of_nonneg_right bound (pow_nonneg P.ratio_bounds.1 t)).trans hdecay
  exact ⟨_, _, _, _, _, by positivity, (p.comp q').relax le_rfl decrease le_rfl⟩

/-- Prepending the same block keeps its composition fee fixed. The loss
after each repetition is bounded by a geometric sum. -/
theorem Block.iterate {Δ b n e K : ℕ} {c : ℝ} (p : Block k Δ 3 b n e K (1 / 2) c)
    (hΔ : 3 ≤ Δ) (he : 0 < e) (t : ℕ) (ht : 0 < t) :
    Block k Δ 3 (b ^ t) (n * t) (e ^ t) ((fee K (1 / 2) c) ^ t) ((1 / 2) ^ t) (2 * c) := by
  let H := Block.fee K (1 / 2) c
  have w := p.degree_mono hΔ (fun D hd => hd.trans (Nat.le_self_pow he.ne' D))
  have hk : K ≤ H := by unfold H Block.fee; omega
  have hit (t : ℕ) (ht : 0 < t) :
      Block k Δ 3 (b ^ t) (n * t) (e ^ t) (H ^ t) ((1 / 2) ^ t) (2 * c * (1 - (1 / 2) ^ t)) := by
    induction t, ht using Nat.le_induction with
    | base =>
      simp only [Nat.succ_eq_add_one, Nat.zero_add, pow_one, mul_one, show 2 * c * (1 - (1 / 2)) = c by ring]
      exact p.relax hk le_rfl le_rfl
    | succ t _ ih =>
      have h := w.comp ih
      rw [show Block.fee K (1 / 2) c = H from rfl,
        ← pow_succ' b, ← pow_succ' e, ← pow_succ' H, ← pow_succ (1 / 2 : ℝ),
        show n + n * t = n * (t + 1) by ring,
        show (1 / 2 : ℝ) ^ t * c + 2 * c * (1 - (1 / 2) ^ t) = 2 * c * (1 - (1 / 2) ^ (t + 1)) by rw [pow_succ]; ring] at h
      exact h
  refine (hit t ht).relax le_rfl le_rfl ?_
  exact mul_le_of_le_one_right (mul_nonneg (by norm_num) p.loss) (sub_le_self _ (by positivity))

/-- For any positive number of repetitions the core degree returns to three
and the width factor halves at each repetition, with uniformly bounded loss. -/
theorem beats (sub : SubroundRule k) (reset : ResetRule k) (tag : Radix.WideTag k)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ∃ (b n e H : ℕ) (C : ℝ), 0 < n ∧ 0 < e ∧ ∀ t : ℕ, 0 < t →
      Block k Δ 3 (b ^ t) (n * t) (e ^ t) (H ^ t) ((1 / 2) ^ t) C := by
  obtain ⟨b, n, e, K, c, he, p⟩ := beat sub reset tag Δ hΔ
  exact ⟨b, n, e, Block.fee K (1 / 2) c, 2 * c, p.steps, he, p.iterate hΔ he⟩

/-- Fix the degree scale and repetition count together so that restoring
the core fits the next round's budgets. -/
theorem plan (sub : SubroundRule k) (reset : ResetRule k) (tag : Radix.WideTag k)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1) (C d₀ : ℕ) :
    ∃ s : Plan, s.C = C ∧ d₀ ≤ s.d ∧ s.Fits ∧ 0 < s.v ∧ 0 < s.p ∧
      (s.p : ℝ) ≤ s.v * (1 + δ / 3) ∧ Block k s.c 3 s.b s.n s.e s.K s.ρ s.loss := by
  obtain ⟨b, n, e, H, B, _, _, run⟩ := beats sub reset tag (C + 12) (by omega)
  obtain ⟨d, v, p, hlarge, hv, hp, hvp, hb, hK, hm, hq, ha⟩ :=
    choose_restart (C + 12) e b H (d₀ + C + 12) (↑(10000 * (C + 1) : ℕ)) B δ
      (by positivity) (run 1 (by decide)).loss hδ hd
  let s : Plan := ⟨C, d, v, p, b ^ (2 * v), n * (2 * v), e ^ (2 * v), H ^ (2 * v), B⟩
  have grow : d < s.D := Nat.lt_two_pow_self
  have fits : s.Fits := ⟨(show C + 12 ≤ s.D by omega), hK, hb, hm, hq, ha⟩
  exact ⟨s, rfl, show d₀ ≤ d by omega, fits, hv, hp, hvp, run (2 * v) (by omega)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
