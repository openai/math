import OAI.Computability.BorderVNP.PackedHistoryGeometryRate
import OAI.Computability.BorderVNP.PackedDirectoryNative
import OAI.Computability.BorderVNP.PrivatePlacementProof

/-! # A single public tick budget for geometry and the two delivery scans

The public history interpreter, private-site prefix pass, and seven-word directory
writer traverse their actual sparse capacities. The same bound also pays for the
serialized geometry packet and the broadcast profile reservation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork TeamContraction TeamScales GeometryAdvice GeometryAdviceRate Filter
open Packing

/-- Combined certified time for placing the original descriptions and emitting all
private, literal and optional extra-pin candidates. The table writer visits empty
candidates as well. -/
def deliveryScanTicks (original teams sites : ℕ) :=
  (RoutingISA.PrivatePlacement.setup.slots+(original*15+1)) +
    (Directory.ISA.setup.slots+(Directory.ISA.candidate.slots+19)*(8*(teams*sites))+8)

private theorem scan_bound (J R V : ℕ) (cap : J ≤ R*V) :
    deliveryScanTicks J R V ≤ (RoutingISA.PrivatePlacement.setup.slots+Directory.ISA.setup.slots+
      8*Directory.ISA.candidate.slots+200)*(R*V+1) := by
  unfold deliveryScanTicks
  nlinarith only [Nat.mul_le_mul_right 15 cap,
    Nat.zero_le (RoutingISA.PrivatePlacement.setup.slots*(R*V)),
    Nat.zero_le (Directory.ISA.setup.slots*(R*V)),Nat.zero_le Directory.ISA.candidate.slots,Nat.zero_le (R*V)]


/-- Full native clock and literal fit for any admitted gate count, including the
public fixed reservation used when the circuit emits its own absolute addresses. -/
theorem eventually_numeric_reconstruction_clock (D E : ℕ) {α τ : ℝ} {K : ℕ} (hα : 0 < α)
    (hsmall : α < 1/1000) (hτ : 0 ≤ τ) (hk : 1 ≤ K) (growth : τ*Real.logb 2 K ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ (p : UniversalMachine.Program) (args regs : ℕ), ∀ᶠ n : ℕ in atTop,
      ∀ {g k reserve o b : ℕ} (r W V J : ℕ),
      1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → 1 ≤ W → k ≤ 4*g →
      ((g+reserve+o*b : ℕ):ℝ) ≤
        A*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^D → (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) → J ≤ teams α τ K n * V →
      let bits := packetWords k reserve o b*W
      let scans := deliveryScanTicks J (teams α τ K n) V
      ((ticks k reserve o b W + bits + reserve + scans : ℕ):ℝ) < r*(n:ℝ)^(93/100:ℝ) ∧
        entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) < literal α n/4 ∧
        bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal α n/8 ∧
        literal α n/4+stripeWidth bits r ≤ literal α n-literal α n/2 := by
  obtain ⟨ω,hω,pay⟩ := eventually_fits_exponent D E (by norm_num : (0:ℝ) ≤ 92/100)
    (by norm_num : (92/100:ℝ) < 925/1000) (by linarith : (925/1000:ℝ)<1-α/3)
  let c : ℕ := RoutingISA.PrivatePlacement.setup.slots+Directory.ISA.setup.slots+8*Directory.ISA.candidate.slots+200
  let γ : ℝ := 2*α+9/10
  have hg : γ < 93/100 := by dsimp [γ]; linarith
  refine ⟨ω,hω,fun A B hA hB p args regs => ?_⟩
  filter_upwards [pay A B hA hB p args regs, eventually_rpow_gap hg (8*c:ℝ),
    eventually_rpow_gap (by norm_num : (925/1000:ℝ) < 93/100) 8,
    eventually_ge_atTop 1] with n geometry gap small hn
  intro g k reserve o b r W V J hr range hb hw gates size words hV hJ bits scans
  have stage := geometry r g k reserve o b W hr range hb gates size words
  have reserveFit : reserve ≤ bits := by
    have hh : reserve ≤ packetWords k reserve o b := by unfold packetWords; omega
    exact hh.trans (Nat.le_mul_of_pos_right _ hw)
  let R := teams α τ K n
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn1
  have hr1 : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have hR := teams_le hk hn hτ growth
  have prod : (R*V:ℕ) ≤ (r:ℝ)*(n:ℝ)^γ := calc
    ((R*V:ℕ):ℝ) ≤ (n:ℝ)^(2*α)*(r*(n:ℝ)^(9/10:ℝ)) := by push_cast; gcongr
    _ = _ := by rw [Real.rpow_add hn0 (2*α) (9/10)]; ring
  have pos : 1 ≤ (r:ℝ)*(n:ℝ)^γ := one_le_mul_of_one_le_of_one_le hr1
    (Real.one_le_rpow hn1 (by dsimp [γ]; positivity))
  have sr : (scans:ℝ) ≤ 2*r*(c:ℝ)*(n:ℝ)^γ := calc
    _ ≤ (c:ℝ)*((R*V:ℕ)+1) := by exact_mod_cast scan_bound J R V hJ
    _ ≤ (c:ℝ)*(2*(r*(n:ℝ)^γ)) := mul_le_mul_of_nonneg_left (by linarith only [prod,pos]) (Nat.cast_nonneg c)
    _ = _ := by ring
  have times : (ticks k reserve o b W+bits+reserve : ℕ) ≤ 2*(r*width n (925/1000)) := by
    have h := stage.1
    change ticks k reserve o b W + bits ≤ r*width n (925/1000) at h
    omega
  have raw : ((ticks k reserve o b W+bits+reserve : ℕ):ℝ) ≤ 2*r*(n:ℝ)^(925/1000:ℝ) := calc
    _ ≤ (2:ℝ)*(r*width n (925/1000)) := by exact_mod_cast times
    _ ≤ _ := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
  refine ⟨?_,stage.2⟩
  rw [Nat.cast_add]
  have a := mul_le_mul_of_nonneg_left small (Nat.cast_nonneg (α:=ℝ) r)
  have b' := mul_le_mul_of_nonneg_left gap (Nat.cast_nonneg (α:=ℝ) r)
  nlinarith only [a,b',sr,raw,mul_pos (zero_lt_one.trans_le hr1) (Real.rpow_pos_of_pos hn0 (93/100))]

/-- At the scales of Proposition 7.2, one team pays strictly fewer than
`r * n ^ 0.93` ticks for the concrete geometry and delivery programs together.
The count includes the bits of the full geometry packet and the profile reservation.
The payload of a private box enters the data delivery width, while its public prefix
pass makes only one directory visit per original site. -/
theorem eventually_reconstruction_clock (D E : ℕ) {α τ : ℝ} {K : ℕ} (hα : 0 < α)
    (hsmall : α < 1/1000) (hτ : 0 ≤ τ) (hk : 1 ≤ K) (growth : τ*Real.logb 2 K ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ (p : UniversalMachine.Program) (args regs : ℕ), ∀ᶠ n : ℕ in atTop,
      ∀ {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S], ∀ {active reserve o b : ℕ} (r W V J : ℕ)
      (history : Frame (X ⊕ Y) (S ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
      (emit : Frame ((X ⊕ Fin reserve) ⊕ S) (Fin o × Fin b)) (x : X → Bool),
      1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → 1 ≤ W →
      ((history.size+emit.size+3*(reserve-active)+3+reserve+o*b : ℕ):ℝ) ≤
        A*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^D → (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) → J ≤ teams α τ K n * V →
      let t := geometryTable history order fit emit x
      let bits := packetWords t.size reserve o b*W
      let scans := deliveryScanTicks J (teams α τ K n) V
      ((ticks t.size reserve o b W + bits + reserve + scans : ℕ):ℝ) < r*(n:ℝ)^(93/100:ℝ) ∧
        entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) < literal α n/4 ∧
        bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal α n/8 ∧
        literal α n/4+stripeWidth bits r ≤ literal α n-literal α n/2 := by
  obtain ⟨ω,positive,charge⟩ := eventually_numeric_reconstruction_clock D E hα hsmall hτ hk growth
  refine ⟨ω,positive,fun A B hA hB p args regs => ?_⟩
  filter_upwards [charge A B hA hB p args regs] with n clock
  intro X Y S _ _ _ active reserve o b r W V J hist order fit emit x hr range hb hw size words hV hJ
  exact clock r W V J hr range hb hw (exportRows_size hist order fit emit x) size words hV hJ

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
