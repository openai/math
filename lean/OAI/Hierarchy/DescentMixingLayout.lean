import OAI.Hierarchy.DescentLinearLayouts
import OAI.Hierarchy.DescentMixingBudget

namespace OAI
/-! # One invertible layout meeting the simultaneous exceptional-base budget -/

namespace Hierarchy.DescentBaseVariance
open DescentGL DescentLinearLayouts
open scoped BigOperators Classical
noncomputable section

private theorem average_addend {P : Type*} [Fintype P] (f g : P → ℝ) :
    average (fun p => f p+g p) = average f+average g := by
  unfold average
  rw [Finset.sum_add_distrib,add_div]

private theorem exists_of_average_le {P : Type*} [Fintype P] [Nonempty P] {f : P → ℝ}
    {b : ℝ} (hb : average f ≤ b) : ∃ p,f p ≤ b := by
  obtain ⟨p,hp⟩ := exists_layout_le_average f
  exact ⟨p,hp.trans hb⟩

/-- The prefix lengths may differ between positions, levels and neighbor pairs.
Every term here is evaluated at the same actual invertible binary layout. -/
theorem average_mixing_layout {A C : Type*} [Fintype A] [Fintype C]
    (bits k : ℕ) (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (hj : ∀ a s,j a s≤bits)
    (cj : C→ℕ) (hcj : ∀ c,cj c≤bits)
    (x : A→Bits bits→ℝ) (n : A→ℝ) (y : C→Bits bits→ℝ)
    (B K X : ℝ) (hB : 0<B) (count : ∀ a (s : Fin (levels a)),(2:ℝ)^(j a s)=n a*2^s.val)
    (hn : ∀ a,0<n a) (hx : ∀ a i,0≤x a i) (small : ∀ a i,x a i≤1/(2:ℝ)^k)
    (mass : ∀ a,∑ i,x a i≤n a) (hy : ∀ c i,0≤y c i) (thin : ∀ c i,y c i≤1/(2:ℝ)^k)
    (quota : (∑ c,∑ i,y c i)≤X/(2^k*B)) :
    let r := (2:ℝ)^(1/8:ℝ)
    average (fun L : Layout bits =>
      ((2:ℝ)^k*B)*((∑ a,∑ s : Fin (levels a),4*(2:ℝ)^((s.val+7)/8)*
        levelCharge s.val (2^k) (layout (hj a s) L) (x a)) +
        ∑ c,K^2*variance (layout (hcj c) L) (y c))) ≤
      ((2:ℝ)^k*B)*(∑ a,n a)*(8*((2:ℝ)^k)^(-(7/8):ℝ)*(1/(r-1)+1/(1-r/2))) +
        K^2*X/2^k := by
  dsimp only
  let : Nonempty (Layout bits) := ⟨LinearEquiv.refl _ _⟩
  let r := (2:ℝ)^(1/8:ℝ)
  have hr : 1<r := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hlt : r<2 := by
    calc
      r < (2:ℝ)^(1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have h8 : r^8=2 := by
    dsimp only [r]
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
    norm_num
  have cardinal (a) (s : Fin (levels a)) : (Fintype.card (Bits (j a s)):ℝ)=n a*2^s.val := by
    rw [card_bits]
    push_cast
    exact count a s
  have base := total_level_budget levels (fun a s=>Bits (j a s))
    (fun a s=>layout (hj a s)) (fun a s=>pairBound bits _ (hj a s)) x n k r hr hlt h8
    hn cardinal hx small mass
  have cap := capacity_budget (F:=(2:ℝ)^k) (B:=B) (fun c=>Bits (cj c)) (fun c=>layout (hcj c))
    (fun c=>pairBound bits _ (hcj c)) y (K:=K) (by positivity) hB hy thin quota
  rw [average_mul,average_addend]
  refine (mul_le_mul_of_nonneg_left (add_le_add base cap) (by positivity : 0≤(2:ℝ)^k*B)).trans ?_
  rw [show (r/2)^k=((2:ℝ)^k)^(-(7/8):ℝ) from root_eighth_decay k]
  have capacity_scale : ((2:ℝ)^k*B)*(K^2*X/(((2:ℝ)^k)^2*B))=K^2*X/2^k := by
    field_simp
  rw [mul_add,capacity_scale]
  apply le_of_eq
  ring

theorem exists_mixing_layout {A C : Type*} [Fintype A] [Fintype C]
    (bits k : ℕ) (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (hj : ∀ a s,j a s≤bits)
    (cj : C→ℕ) (hcj : ∀ c,cj c≤bits)
    (x : A→Bits bits→ℝ) (n : A→ℝ) (y : C→Bits bits→ℝ)
    (B K X : ℝ) (hB : 0<B) (count : ∀ a (s : Fin (levels a)),(2:ℝ)^(j a s)=n a*2^s.val)
    (hn : ∀ a,0<n a) (hx : ∀ a i,0≤x a i) (small : ∀ a i,x a i≤1/(2:ℝ)^k)
    (mass : ∀ a,∑ i,x a i≤n a) (hy : ∀ c i,0≤y c i) (thin : ∀ c i,y c i≤1/(2:ℝ)^k)
    (quota : (∑ c,∑ i,y c i)≤X/(2^k*B)) :
    let r := (2:ℝ)^(1/8:ℝ)
    ∃ L : Layout bits,
      ((2:ℝ)^k*B)*((∑ a,∑ s : Fin (levels a),4*(2:ℝ)^((s.val+7)/8)*
        levelCharge s.val (2^k) (layout (hj a s) L) (x a)) +
        ∑ c,K^2*variance (layout (hcj c) L) (y c)) ≤
      ((2:ℝ)^k*B)*(∑ a,n a)*(8*((2:ℝ)^k)^(-(7/8):ℝ)*(1/(r-1)+1/(1-r/2))) +
        K^2*X/2^k := by
  let : Nonempty (Layout bits) := ⟨LinearEquiv.refl _ _⟩
  exact exists_of_average_le
    (average_mixing_layout bits k levels j hj cj hcj x n y B K X hB count hn hx small mass hy thin quota)

end
end Hierarchy.DescentBaseVariance

end OAI
