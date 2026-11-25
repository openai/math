import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # The copied profile, its physical row outputs and all five scratch regions

The charged gate list includes the true history circuit, the sparse emitter and the test
of the unused broadcast bits. The same uniform polylogarithmic bound that pays for the
native reader pays for the complete address reservation above the chosen startup arena.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork TeamContraction TeamScales GeometryAdvice GeometryAdviceRate Filter

/-- When native words and output fields are nonempty, four copies of the literal packet bit
length pay for every scratch word from the first gate valuation to the final end sentinel. -/
theorem geometry_stop_packet (fresh u k o b w : ℕ) (hb : 1 ≤ b) (hw : 1 ≤ w) :
    Allocation.stop fresh u k o b w ≤ fresh + 4*(packetWords k u o b*w) := by
  have outputs : o ≤ o*b := Nat.le_mul_of_pos_right _ hb
  have copies : packetWords k u o b ≤ packetWords k u o b*w := Nat.le_mul_of_pos_right _ hw
  unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp GeometryOutput.packetCount
  unfold packetWords at copies ⊢; omega

/-- A geometry charge below the rounded physical clock uses at most one further batch of
`r*n` memory addresses, uniformly in the public circuit and number of processors. -/
theorem eventually_geometry_addresses {γ : ℝ} (gap : γ < 1) : ∀ᶠ n : ℕ in atTop,
    ∀ (r fresh k u o b W : ℕ), 1 ≤ b → 1 ≤ W →
    ticks k u o b W+packetWords k u o b*W ≤ r*width n γ →
    Allocation.stop fresh u k o b W ≤ fresh+r*n := by
  filter_upwards [eventually_rpow_gap gap 4] with n bound
  intro r fresh k u o b W hb hw charged
  have floor : (width n γ : ℝ) ≤ (n : ℝ)^γ := Nat.floor_le (by positivity)
  have scale : 4*width n γ ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [Nat.cast_mul,Nat.cast_ofNat,Real.rpow_one] at bound ⊢
    exact (mul_le_mul_of_nonneg_left floor (by norm_num : (0:ℝ) ≤ 4)).trans bound
  calc
    _ ≤ fresh+4*(packetWords k u o b*W) := geometry_stop_packet fresh u k o b W hb hw
    _ ≤ fresh+4*(r*width n γ) := by omega
    _ = fresh+r*(4*width n γ) := by ring
    _ ≤ _ := by gcongr


/-- Reserve the demand directory before the first geometry valuation. Its half of the
`r*n` allowance and the rounded geometry packet fit in the same native address interval. -/
theorem eventually_reserved_geometry {γ : ℝ} (gap : γ < 1) : ∀ᶠ n : ℕ in atTop,
    ∀ (r base reserve k u o b W : ℕ), 2*reserve ≤ r*n → 1 ≤ b → 1 ≤ W →
    packetWords k u o b*W ≤ r*width n γ → Allocation.stop (base+reserve) u k o b W ≤ base+r*n := by
  filter_upwards [eventually_rpow_gap gap 8] with n bound
  intro r base reserve k u o b W reserved hb hw charge
  have floor : (width n γ : ℝ) ≤ (n : ℝ)^γ := Nat.floor_le (by positivity)
  have scale : 8*width n γ ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [Nat.cast_mul,Nat.cast_ofNat,Real.rpow_one] at bound ⊢
    exact (mul_le_mul_of_nonneg_left floor (by norm_num : (0:ℝ) ≤ 8)).trans bound
  have half : 8*(packetWords k u o b*W) ≤ r*n := calc
    _ ≤ 8*(r*width n γ) := Nat.mul_le_mul_left _ charge
    _ = r*(8*width n γ) := by ring
    _ ≤ _ := Nat.mul_le_mul_left r scale
  have stop := geometry_stop_packet (base+reserve) u k o b W hb hw
  omega

/-- The actual compiled profile table fits its public stripe and the free memory above
startup, while all interpreted gate, bit and output passes are charged at the 0.95 exponent.
The charge counts the concrete Boolean gates and all physical input and output bits. -/
theorem eventually_profile_geometry (D E : ℕ) {α : ℝ} (hα : (95/100:ℝ) < 1-α/3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ (p : UniversalMachine.Program) (args regs : ℕ), ∀ᶠ n : ℕ in atTop,
      ∀ {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V], ∀ {active reserve o b : ℕ} (r W fresh : ℕ)
      (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
      (emit : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : X → Bool),
      1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → 1 ≤ W →
      ((history.size+emit.size+3*(reserve-active)+3+reserve+o*b : ℕ):ℝ) ≤
        A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^D → (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      let t := geometryTable history order fit emit x
      let bits := packetWords t.size reserve o b*W
      ticks t.size reserve o b W+bits ≤ r*width n (95/100:ℝ) ∧
      Allocation.stop fresh reserve t.size o b W ≤ fresh+r*n ∧
      entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) < literal α n/4 ∧
      bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal α n/8 ∧
      literal α n/4+stripeWidth bits r ≤ literal α n-literal α n/2 := by
  obtain ⟨ω,hω,budget⟩ := eventually_fits D E hα
  refine ⟨ω,hω,fun A B hA hB p args regs => ?_⟩
  filter_upwards [budget A B hA hB p args regs,eventually_geometry_addresses (by norm_num : (95/100:ℝ)<1)] with n pay room
  intro X Y V _ _ _ active reserve o b r W fresh history order fit emit x hr small hb hw size word t bits
  have charge := pay r (history.size+emit.size+3*(reserve-active)+3) t.size reserve o b W hr small hb
    (exportRows_size history order fit emit x) size word
  exact ⟨charge.1,room r fresh t.size reserve o b W hb hw charge.1,charge.2⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
