import OAI.Computability.BorderVNP.GeometryAdviceCharge
import OAI.Computability.BorderVNP.PackedPotential

/-! # Literal reserve and running time for the geometry advice

A fixed polynomial in the rounded address length can be absorbed in the
exponent gap between the input charge and the geometry clock. One eighth of
each literal suffices for its stripe, starting at one quarter. The processor
prefix and the private directory tail are both disjoint from this interval.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdviceRate

open Filter TeamScales VPVNP TeamContraction

/-- Number of reserved geometry bits per processor, with at least one position
so that the stripe reader's Euclidean division is always defined. -/
def stripeWidth (bits r : ℕ) := max 1 (bits ⌈/⌉ r)

/-- Every serialized bit has a processor and an offset in its stripe. -/
theorem stripe_capacity (bits : ℕ) {r : ℕ} (hr : 1 ≤ r) : bits ≤ r*stripeWidth bits r :=
  (ceilDiv_le_iff_le_mul hr).mp (le_max_right ..)

private theorem charge_bound {g k u o b W r n D E : ℕ} {A B σ : ℝ} (hσ : 0 ≤ σ)
    (hr : 1 ≤ r) (hn : 1 ≤ n) (hb : 1 ≤ b) (hk : k ≤ 4*g)
    (hsize : ((g+u+o*b : ℕ) : ℝ) ≤ A*r*(n:ℝ)^σ*(logWidth r n : ℝ)^D)
    (hword : (W : ℝ) ≤ B*(logWidth r n : ℝ)^E) :
    ((ticks k u o b W + packetWords k u o b*W : ℕ) : ℝ) ≤
      r * (3072*(A+1)*(B+1)*(n:ℝ)^σ*(logWidth r n : ℝ)^(D+E)) := by
  let L : ℝ := logWidth r n
  let H := (r : ℝ)*(n:ℝ)^σ*L^D
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast (indexWidths hr hn).1
  have hN : 1 ≤ (n:ℝ)^σ := Real.one_le_rpow (by exact_mod_cast hn) hσ
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hr) hN) (one_le_pow₀ hL)
  have hS : ((g+u+o*b+1 : ℕ) : ℝ) ≤ (A+1)*H := by
    have hs : ((g+u+o*b : ℕ) : ℝ) ≤ A*H := by simpa [H,L,mul_assoc] using hsize
    rw [Nat.cast_add_one,add_mul,one_mul]
    linarith
  have hW : ((W+1 : ℕ) : ℝ) ≤ (B+1)*L^E := by
    rw [Nat.cast_add_one,add_mul,one_mul]
    exact add_le_add hword (one_le_pow₀ hL)
  have h := charge_le (W := W) (u := u) (o := o) hk hb
  calc
    _ ≤ (3072:ℝ)*((g+u+o*b+1:ℕ):ℝ)*((W+1:ℕ):ℝ) := by exact_mod_cast h
    _ ≤ (3072:ℝ)*((A+1)*H)*((B+1)*L^E) := by
      have nonneg := (Nat.cast_nonneg (g+u+o*b+1)).trans hS
      gcongr
    _ = _ := by simp only [H,L,pow_add]; ring

/-- One team-size exponent suffices for both native time and literal storage,
uniformly for all constants in the fixed polynomial bounds. The input bound uses
the original frame gate count, the query wires, and all output bits. The physical
processor startup uses the actual fixed program, register frame, metadata fields
and the independent residue-advice bit. -/
theorem eventually_fits_exponent (D E : ℕ) {σ γ α : ℝ} (hσ : 0 ≤ σ) (slack : σ < γ) (hα : γ < 1-α/3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ (p : UniversalMachine.Program) (args regs : ℕ), ∀ᶠ n : ℕ in atTop,
      ∀ (r g k u o b W : ℕ), 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → k ≤ 4*g →
      ((g+u+o*b : ℕ):ℝ) ≤ A*r*(n:ℝ)^σ*(logWidth r n:ℝ)^D →
      (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      let bits := packetWords k u o b*W
      ticks k u o b W + bits ≤ r*width n γ ∧
      entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) < literal α n/4 ∧
      bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal α n/8 ∧
      literal α n/4+stripeWidth bits r ≤ literal α n-literal α n/2 := by
  let δ := (γ-σ)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hγ : 0 < γ := hσ.trans_lt slack
  obtain ⟨ω,hω,hlog⟩ := exists_polylog_budget (D+E+1) hδ
  refine ⟨ω,hω,fun A B hA hB p args regs => ?_⟩
  let C := (3072:ℝ)*(A+1)*(B+1)
  let M : ℝ := (UniversalMachine.programPrefix p).length + (args+regs+12:ℕ)*B + 12 + 16
  have clock := Packing.eventually_le_rounded_width (by dsimp [δ]; linarith : σ+δ<γ)
    hγ (by norm_num : (0:ℝ)<1) C
  have head := Packing.eventually_le_rounded_width (by dsimp [δ]; linarith : δ<γ)
    hγ (by norm_num : (0:ℝ)<1) M
  have room := Packing.eventually_le_rounded_width hα (by linarith) (by norm_num : (0:ℝ)<1) 16
  filter_upwards [hlog,clock,head,room,eventually_ge_atTop 1] with n logN clockN headN roomN hn
  simp only [one_mul] at clockN headN roomN
  intro r g k u o b W hr hrω hb hk hsize hword bits
  let L : ℝ := logWidth r n
  let powN := (n:ℝ)^δ
  let clockWidth := width n γ
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast (indexWidths hr hn).1
  have oneN : 1 ≤ powN := Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  have logPow (i : ℕ) (hi : i ≤ D+E+1) : L^i ≤ powN :=
    (pow_le_pow_right₀ hL hi).trans (logN r hr hrω)
  have hcost : ticks k u o b W + bits ≤ r*clockWidth := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_mul]
    calc
      _ ≤ (r:ℝ)*(C*(n:ℝ)^σ*L^(D+E)) :=
        charge_bound hσ hr hn hb hk hsize hword
      _ ≤ (r:ℝ)*(C*(n:ℝ)^σ*powN) := by
        have hC : 0 ≤ C := by unfold C; positivity
        gcongr
        exact logPow _ (by omega)
      _ = (r:ℝ)*(C*(n:ℝ)^(σ+δ)) := by
        rw [mul_assoc C, ← Real.rpow_add npos]
      _ ≤ _ := mul_le_mul_of_nonneg_left clockN (by positivity)
  have hpre : entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) ≤ clockWidth := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hp := prefix_le p args regs W hr hn
    have hw := hword.trans (mul_le_mul_of_nonneg_left (logPow E (by omega)) hB)
    have hl : L ≤ powN := by simpa using logPow 1 (by omega)
    calc
      _ ≤ (((UniversalMachine.programPrefix p).length : ℝ) + (args+regs+12:ℕ)*(W:ℝ) + 12*L+16) := by
        dsimp only [L]
        exact_mod_cast hp
      _ ≤ (UniversalMachine.programPrefix p).length*powN + (args+regs+12:ℕ)*(B*powN) + 12*powN+16*powN := by
        gcongr
        · exact (le_mul_of_one_le_right (by positivity) oneN)
        · linarith
      _ = M*powN := by unfold M; ring
      _ ≤ _ := headN
  have hwpos : 1 ≤ clockWidth := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using
      (Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n:ℝ)) hγ.le)
  have scale : 16*clockWidth ≤ literal α n := by
    have hf : (clockWidth:ℝ) ≤ (n:ℝ)^γ := Nat.floor_le (by positivity)
    exact_mod_cast ((mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ) ≤ 16)).trans roomN)
  have hs : stripeWidth bits r ≤ clockWidth := max_le hwpos ((ceilDiv_le_iff_le_mul hr).mpr (by omega))
  exact ⟨hcost,by omega,stripe_capacity bits hr,by omega,by omega⟩

/-- The previously used 0.93-to-0.95 rate follows by specializing the two exponents. -/
theorem eventually_fits (D E : ℕ) {α : ℝ} (hα : (95/100:ℝ) < 1-α/3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ (p : UniversalMachine.Program) (args regs : ℕ), ∀ᶠ n : ℕ in atTop,
      ∀ (r g k u o b W : ℕ), 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → k ≤ 4*g →
      ((g+u+o*b : ℕ):ℝ) ≤ A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^D →
      (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      let bits := packetWords k u o b*W
      ticks k u o b W + bits ≤ r*width n (95/100:ℝ) ∧
      entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) < literal α n/4 ∧
      bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal α n/8 ∧
      literal α n/4+stripeWidth bits r ≤ literal α n-literal α n/2 :=
  eventually_fits_exponent D E (by norm_num) (by norm_num) hα

/-- A 0.92 input exponent leaves a strictly smaller than 0.93 native running
time in Proposition 7.2(ii), including the physical packet. -/
theorem eventually_paper_clock (D E : ℕ) {α : ℝ} (hα : (93/100:ℝ) < 1-α/3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ᶠ n : ℕ in atTop,
      ∀ (r g k u o b W : ℕ), 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → k ≤ 4*g →
      ((g+u+o*b : ℕ):ℝ) ≤ A*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^D →
      (W:ℝ) ≤ B*(logWidth r n:ℝ)^E →
      ((ticks k u o b W+packetWords k u o b*W:ℕ):ℝ) < r*(n:ℝ)^(93/100:ℝ) := by
  obtain ⟨ω,hω,h⟩ := eventually_fits_exponent D E (σ:=92/100) (γ:=37/40) (by norm_num)
    (by norm_num) (lt_trans (by norm_num : (37/40:ℝ)<93/100) hα)
  refine ⟨ω,hω,fun A B hA hB => ?_⟩
  filter_upwards [h A B hA hB UniversalMachine.emptyProgram 0 0,eventually_ge_atTop 2] with n hn hn2
  intro r g k u o b W hr small hb hk size word
  have ct := (hn r g k u o b W hr small hb hk size word).1
  have floor : ((width n (37/40):ℕ):ℝ) ≤ (n:ℝ)^(37/40:ℝ) := Nat.floor_le (by positivity)
  have nr : (1:ℝ) < n := by exact_mod_cast (by omega : 1<n)
  have rr : (0:ℝ) < r := by exact_mod_cast (by omega : 0<r)
  exact (by exact_mod_cast ct : ((ticks k u o b W+packetWords k u o b*W:ℕ):ℝ) ≤
    (r:ℝ)*(width n (37/40):ℝ)).trans_lt (mul_lt_mul_of_pos_left
      (floor.trans_lt (Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num))) rr)

end GeometryAdviceRate

end BorderVNP
end Computability
end OAI
