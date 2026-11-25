import OAI.Hierarchy.CollapseEnvelopes
import OAI.Hierarchy.CollapseNetworks
import OAI.Hierarchy.GridReuse

namespace OAI
/-! # The size, open-bit, and price invariants for the dominant collapse iteration -/

noncomputable section
namespace Hierarchy.CollapseOracle

open Catalyst ThreeFlat Filter GridScale
open scoped Classical BigOperators

variable {F : Type*} [Field F]

def Layer (F : Type*) [Field F] (k A' : ℕ) (b : ℝ) (i : ℕ)
    (Q : ℕ → ℕ) (D : ℕ → ℝ) : Prop :=
  ∀ᶠ w : ℕ in atTop, ∀ (p : ℕ) (tick : BitNetwork F p),
    tick.cells + tick.internal + p ≤ 2^w → p*w^A' ≤ 2^w →
    ∃ q : ℕ, 0<q ∧ q≤Q w ∧ ∃ X : Approximation F k (q*p),
      (X.size:ℝ)*(w:ℝ)^(b*i) ≤ q*(2:ℝ)^w ∧
      Fintype.card (Port (q*p) X.width)*w^A' ≤ 2*q*2^w ∧
      X.PointwiseGap (tickProduct tick q) (D w)

def Attained (F : Type*) [Field F] (k A' : ℕ) (b : ℝ) (i : ℕ) : Prop :=
  ∃ Q D, Small Q ∧ Near D ∧ Layer F k A' b i Q D

theorem layer_zero (k A' : ℕ) (b : ℝ) : Attained F k A' b 0 := by
  refine ⟨fun _ => 1,fun w => (2:ℝ)^w,small_one,near_volume,?_⟩
  apply Filter.Eventually.of_forall
  intro w p tick size pin
  refine ⟨1,by decide,le_rfl,single k tick,?_,?_,single_gap tick _⟩
  · simp only [single_size,Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,Nat.cast_one,one_mul]
    exact_mod_cast size
  · rw [single_ports]
    omega

theorem layer_finish {k A A' L : ℕ} {b : ℝ} (good : Attained F k A' b L)
    (gain : (A:ℝ)≤b*L) :
    ∃ Q : ℕ → ℕ, ∃ D : ℕ → ℝ, Envelopes Q D ∧
      ∀ᶠ w : ℕ in atTop, ∀ (p : ℕ) (tick : BitNetwork F p),
        tick.cells+tick.internal+p≤2^w → p*w^A'≤2^w →
        ∃ q : ℕ, 0<q ∧ q≤Q w ∧ ∃ X : Approximation F k (q*p),
          X.size*w^A ≤ q*2^w ∧ X.PointwiseGap (tickProduct tick q) (D w) := by
  obtain ⟨Q,D,hQ,hD,stage⟩ := good
  refine ⟨Q,D,fun ε he => (hQ ε he).and (hD ε he),?_⟩
  filter_upwards [stage,eventually_ge_atTop (1:ℕ)] with w live big
  intro p tick size pins
  obtain ⟨q,pos,cap,X,cost,_,price⟩ := live p tick size pins
  refine ⟨q,pos,cap,X,?_,price⟩
  have power : (w:ℝ)^A ≤ (w:ℝ)^(b*L) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast big) gain
  exact_mod_cast (mul_le_mul_of_nonneg_left power (Nat.cast_nonneg X.size)).trans cost

theorem layer_induction {k : ℕ} {b : ℝ} (hb : 0<b)
    (advance : ∀ A' L : ℕ, b*L+4≤A' → ∀ i<L,
      Attained F k A' b i → Attained F k A' b (i+1)) :
    HasPointwiseCollapse F k := by
  apply Filter.Eventually.of_forall
  intro A
  let L := ⌈(A:ℝ)/b⌉₊
  let A' := ⌈b*L+4⌉₊
  have depth : (A:ℝ)≤b*L := by
    rw [mul_comm]
    exact (div_le_iff₀ hb).mp (Nat.le_ceil _)
  have room : b*L+4≤A' := Nat.le_ceil _
  have strict : A<A' := by exact_mod_cast (show (A:ℝ)<A' by linarith)
  refine ⟨A',strict,layer_finish (L:=L) (b:=b) ?_ depth⟩
  have loop : ∀ i≤L, Attained F k A' b i := by
    intro i
    induction i with
    | zero => exact fun _ => layer_zero k A' b
    | succ i ih => intro le; exact advance A' L room i (by omega) (ih (by omega))
  exact loop L le_rfl

omit [Field F] in
theorem replicated_open {m p n q w A' : ℕ} (X : Approximation F (m+1) (q*p))
    (side : n+1=w^A') (pins : p*w^A'≤2^w) (compact : X.size ≤ q*2^w) :
    Fintype.card (Port ((GridReuse.Copies m n*q)*p) (GridReuse.spliceTicks n q X).width) *
      w^A' ≤ 2*(GridReuse.Copies m n*q)*2^w := by
  let L := GridReuse.Copies m n
  let E := GridReuse.rails n X.width
  have same : (GridReuse.spliceTicks n q X).width = (GridReuse.splice n X).width :=
    castPins_width _ _
  rw [same,Fintype.card_sum,Fintype.card_fin]
  change ((L*q)*p + Fintype.card (Wire (GridReuse.width n X.width) × Bool))*w^A' ≤ _
  rw [Fintype.card_prod,Fintype.card_bool]
  change ((L*q)*p + E*2)*w^A' ≤ _
  have wire := (GridReuse.splice_open n X).2.trans (Nat.mul_le_mul_left _ compact)
  change (n+1)*(2*E) ≤ L*(q*2^w) at wire
  rw [side] at wire
  have data := Nat.mul_le_mul_left (L*q) pins
  change _ ≤ 2*(L*q)*2^w
  nlinarith only [wire,data]


end Hierarchy.CollapseOracle

end
end OAI
