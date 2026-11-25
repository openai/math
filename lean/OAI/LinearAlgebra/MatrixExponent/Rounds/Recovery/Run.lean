import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Rate
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Repost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry

/-! # Restoring the frozen border after the final contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
open Assembly Contraction

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
    {A : Attachment D} {s : Plan} {T : ℕ} {L : ℝ} {z k : ℕ}
    (hs : s.Fits) (hz : 0 < z) (ht : T ≤ z * s.M)
local notation "I" => Snapshot.state (final (x := x) (y := y) A s T L z k)

include hs hz ht in
theorem feasible (i : I) : Restore.Feasible i.val s.full s.slots s.slots :=
  ⟨allocation hs hz ht i, i.property.1.bounded.1, i.property.1.simple le_rfl⟩

abbrev data (i : I) := (feasible hs hz ht i).data

theorem board_ready (hL : 0 ≤ L) (i : I) :
    (data hs hz ht i).board.Ready 5 s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor := by
  have h := i.property.1
  have lo (t : i.val.T) : (z : ℝ) ≤ i.val.L.charge t := by
    obtain ⟨n, hn, he⟩ := h.charge t
    rw [he]; exact Nat.cast_le.mpr hn
  exact Restore.Data.ready (data hs hz ht i) hs hL ht h.test.cover
    (fun j => Nat.cast_le.mpr (h.parallel j)) lo h.bounded h.width h.total h.test.square h.test.maximum

def height (s : Plan) (T : ℕ) := s.d + s.p + Nat.clog 2 T

theorem arity (hL : 0 ≤ L) (i : I) (v : (data hs hz ht i).board.diagram.V) :
    (data hs hz ht i).board.diagram.arity v ≤ 2 ^ (height s T) := by
  let P := (data hs hz ht i).board
  have hc := (P.cover v).trans ((board_ready hs hz ht hL i).2.2.2 v).1
  have hu : (P.diagram.arity v : ℝ) ≤ (s.D : ℝ) * (2 ^ s.p * T : ℕ) :=
    hc.trans (div_le_self (by positivity) (by norm_num))
  have hu' : P.diagram.arity v ≤ s.D * (2 ^ s.p * T) := by exact_mod_cast hu
  refine hu'.trans ?_
  rw [height, pow_add, pow_add, mul_assoc, Plan.D]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _))

variable (x y A k) (hL : 0 ≤ L)
abbrev raw := Restore.rawLayer (fun i : I => data hs hz ht i) (height s T) (arity hs hz ht hL)
abbrev layer := Restore.layer (fun i : I => data hs hz ht i) (height s T) (arity hs hz ht hL)

theorem ready :
    (layer x y A k hs hz ht hL).Ready s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
    (layer x y A k hs hz ht hL).Loopless :=
  Restore.ready _ _ _ (board_ready hs hz ht hL)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
end

/-! # Fixed port count at a round boundary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
open Assembly Contraction

section
variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (s : Plan) (T k : ℕ) (W : Prices F)

abbrev measure : Restore.Measure where
  F := F
  D := D
  A := A
  N := s.full
  r := s.slots
  s := s.slots
  c := W
  w := max k (D.scheme.h + height s T) + 1
  fst := k
  snd := height s T

end
variable {F : Type} [Field F] {D : Template F} (x y : Wire) (A : Attachment D) (k : ℕ)
  {s : Plan} {T : ℕ} {L : ℝ} {z : ℕ}
  (hs : s.Fits) (hz : 0 < z) (ht : T ≤ z * s.M) (hL : 0 ≤ L)
local notation "Y" => layer x y A k hs hz ht hL

abbrev restored : Layer F x y :=
  Merge.layer (layer x y A k hs hz ht hL) (ready x y A k hs hz ht hL).2 rfl

theorem stable :
    (restored x y A k hs hz ht hL).Ready s.D (2 ^ s.p * T) (L / (2 : ℝ) ^ s.v) s.floor ∧
    (restored x y A k hs hz ht hL).Loopless :=
  ⟨Merge.ready Y _ _ (ready x y A k hs hz ht hL).1, Merge.loopless Y _ _⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
end

/-! # A uniform budget for restoration, scalar withdrawal and span merging -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
open Assembly Contraction BatchDescent.Phase

/-- One exponent works for all fields and legal input layers. The sum
of the four gate sizes bounds the largest gate arity. -/
theorem estimate : ∃ K : ℕ, ∀ {F : Type} [Field F] {D : Template F}
    (x y : Wire) (A : Attachment D) (k : ℕ) {s : Plan} {T : ℕ} {L : ℝ} {z : ℕ}
    (hs : s.Fits) (hz : 0 < z) (ht : T ≤ z * s.M) (hL : 0 ≤ L) (W : Prices F),
    let i := measure A s T k W
    let P := raw x y A k hs hz ht hL
    let Q := layer x y A k hs hz ht hL
    Restore.gateWidth A i.N i.r i.s + Restore.commandSize A i.N i.r i.s i.w +
        2 * (Restore.script A.scheme).width +
        SpanProgram.size Q.template.scheme 0 (Q.height + 1) (Merge.dim Q.template.scheme) ≤ i.short ^ K ∧
    Restore.stageCost A i.N i.r i.s z i.w x y i.fst i.snd W +
      P.encoding.sweepCost + Merge.layerCost Q W ≤ i.budget x y K := by
  obtain ⟨f, hf⟩ := Restore.Measure.bound
  obtain ⟨g, hg⟩ := Restore.Measure.sweep_bound
  obtain ⟨h, hh⟩ := Merge.price
  refine ⟨max (max f g + 1) h + 1, ?_⟩
  intro F _ D x y A k s T L z hs hz ht hL W i P Q
  obtain ⟨gate, stage⟩ := hf i z x y
  have sweep := (i.sweep_estimate x y z P rfl rfl rfl).trans (hg i x y)
  obtain ⟨merge, hcost⟩ := hh i Q z rfl rfl rfl
  constructor
  · have ht : i.short ^ f ≤ i.short ^ (max f g + 1) :=
      Nat.pow_le_pow_right (lt_of_lt_of_le (by decide) i.short_two) (by omega)
    exact (Nat.add_le_add (gate.trans ht) merge).trans (Poly.pow_sum i.short_two ..)
  · have hj := (Nat.add_le_add stage sweep).trans (i.add x y f g)
    exact (Nat.add_le_add hj hcost).trans (i.add x y _ h)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
end

/-!
# Reassembling one complete round

Choose four shared dictionary entries before fixing the admissible
set of tables. The output has one station at each occurrence and
a fixed, degree-independent number of port indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
open Assembly Contraction
open scoped Classical

private theorem more {a b m l : ℕ} :
    (b + 1) * (2 ^ (m + l) + 2 ^ (m + l)) ≤ 2 ^ l * ((max a b + 1) * (2 ^ m + 2 ^ (m + l))) := by
  rw [mul_left_comm (2 ^ l), mul_add (2 ^ l), pow_add]
  apply Nat.mul_le_mul (Nat.succ_le_succ (le_max_right a b))
  exact Nat.add_le_add (mul_comm ..).le (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos l))

theorem run : ∃ K : ℕ, ∀ {F : Type} [Field F] {D : Template F}
    (x y : Wire) (A : Attachment D) (k : ℕ) {s : Plan} {T : ℕ} {L : ℝ} {z : ℕ}
    (hs : s.Fits) (hz : 0 < z) (ht : T ≤ z * s.M) (hL : 0 ≤ L) (W : Prices F),
    let i := measure A s T k W
    1 ≤ i.m → i.m + i.d ≤ W.w →
    2 ^ i.l * ((max i.fst (i.h + i.snd) + 1) * (2 ^ i.m + 2 ^ (i.m + i.l))) < 2 ^ W.w →
    ∃ gates : Finset (Table F), gates.card ≤ 4 ∧
      ∀ {U : ℕ} {C : Set (Table F)}, 3 ≤ U → ↑gates ⊆ C → i.short ^ K ≤ U →
        Transforms F U C (final (x := x) (y := y) A s T L z k)
          (restored x y A k hs hz ht hL).snapshot (i.budget x y K) := by
  obtain ⟨K, hK⟩ := estimate
  refine ⟨K, ?_⟩
  intro F _ D x y A k s T L z hs hz ht hL W i hm hd hc
  let ok := Ready (u := z) A (fringe (x := x) (y := y) s T L) z 3 s.full (destination s T L)
  let P := raw x y A k hs hz ht hL
  let Q := layer x y A k hs hz ht hL
  have hk : k < i.w := Nat.lt_succ_of_le (le_max_left ..)
  have hw : i.h + i.snd < i.w := Nat.lt_succ_of_le (le_max_right ..)
  obtain ⟨a, ha⟩ := Restore.stage ok (feasible hs hz ht) (arity hs hz ht hL) W hm hd hc hk hw
  let b := (Restore.program A i.N i.r i.s i.w).gate
  let c := P.encoding.sweepTable
  let d := (Merge.script Q).gate
  let menu : Finset (Table F) := {a, b, c, d}
  refine ⟨menu, ?_, ?_⟩
  · exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right Finset.card_le_three _)
  intro U C hu incl fit
  have ga : a ∈ C := incl (by simp [menu])
  have gb : b ∈ C := incl (by simp [menu])
  have gc : c ∈ C := incl (by simp [menu])
  have gd : d ∈ C := incl (by simp [menu])
  obtain ⟨hf, he⟩ := hK x y A k hs hz ht hL W
  have widths := hf.trans fit
  obtain ⟨h₁, h₂, h₃, h₄⟩ :
      Restore.gateWidth A i.N i.r i.s ≤ U ∧ Restore.commandSize A i.N i.r i.s i.w ≤ U ∧
        2 * (Restore.script A.scheme).width ≤ U ∧
        SpanProgram.size Q.template.scheme 0 (Q.height + 1) (Merge.dim Q.template.scheme) ≤ U := by
    refine ⟨?_, ?_, ?_, (Nat.le_add_left ..).trans widths⟩
    · exact ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))).trans widths
    · exact ((Nat.le_add_left ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))).trans widths
    · exact ((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans widths
  have recode := ha hu ga gb h₁ h₂
  have clean := Restore.withdraw (fun j => data hs hz ht j) (height s T) (arity hs hz ht hL) hu h₃ gc
  have join := Merge.transforms Q (ready x y A k hs hz ht hL).2 rfl W hu h₄ gd
    (hm.trans (Nat.le_add_right ..)) (more.trans_lt hc)
  exact ((recode.comp clean).comp join).mono he

end OAI.LinearAlgebra.MatrixExponent.Rounds.Recovery
end
