import OAI.Computability.MultitapeWeakETH.InputCharge
import OAI.Computability.MultitapeWeakETH.MaskCharge

/-! # Joint pin budget for one fixed high input part and four columns -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork
open Finset MatrixMultiplication.Foundation
open scoped BigOperators Classical
noncomputable section
variable {n b N L : ℕ} {A : Type} [Fintype A] (G : Network n b)

def rowPin (fits : L ≤ n) (high : Fin (2^(n-L))) (low : A → Fin (2^L))
    (z : A → Fin 4 → Word n) (target : A → Fin 4 → Fin (2^n)) (v : Site G N) (x : A) : Pin G v :=
  pinFor G (residueWord n (joinPayload n L fits (high,low x))) (errorMasks b (z x) (target x)) v

def charge (p : FiniteLaw A) (pin : (v : Site G N) → A → Pin G v) (v : Site G N) :=
  finiteEntropy (p.map (pin v)).mass / Real.log 2

theorem pin_budget (hb : 0 < b) (p : FiniteLaw A) (fits : L ≤ n) (high : Fin (2^(n-L)))
    (low : A → Fin (2^L)) (z : A → Fin 4 → Word n) (target : A → Fin 4 → Fin (2^n))
    (budget : ∀ x r, 100*errors (z x r) (residueWord n (target x r)) ≤ n) :
    let h := charge G (N:=N) p (rowPin G fits high low z target)
    (∀ v, 0 ≤ h v ∧ h v ≤ 4*b) ∧
      ∑ v, h v ≤ L + ((n ⌈/⌉ b : ℕ):ℝ)*(4*b:ℕ)*entropyBits (1/100) := by
  intro h
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have input (v : Fin G.vertices) : h (original G v) ≤ Fintype.card (Varying G L v) := by
    apply (div_le_iff₀ logpos).mpr
    convert! input_entropy G p fits high low v using 1
    unfold rowPin original pinFor
    congr!
    subst_vars
    rfl
  have proc (j : Block n b) : h (processor G j) ≤ 4*b := by
    apply (div_le_iff₀ logpos).mpr
    apply ((p.map (rowPin G (N:=N) fits high low z target (processor G j))).entropy_le_log_card).trans_eq
    have card : Fintype.card (Pin G (processor G (N:=N) j)) = 2^(b*4) := by
      rw [← Nat.card_eq_fintype_card]
      simp [processor,Pin,Word,pow_mul]
    rw [card,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    push_cast
    ring
  have term (t : Fin N) : h (terminal G t) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ logpos.le
    apply ((p.map (rowPin G fits high low z target (terminal G t))).entropy_le_log_card).trans_eq
    have card : Fintype.card (Pin G (terminal G t)) = 1 := by
      rw [← Nat.card_eq_fintype_card]
      simp [terminal,Pin]
    simp [card]
  constructor
  · intro v
    refine ⟨div_nonneg (p.map _).entropy_nonneg logpos.le,?_⟩
    rcases v with v | j | t
    · apply (input v).trans
      have le : (Fintype.card (Varying G L v):ℝ) ≤ b := by exact_mod_cast varying_card G hb v
      linarith [Nat.cast_nonneg (α:=ℝ) b]
    · exact proc j
    · exact (term t).trans (by positivity)
  · have I := sum_le_sum (s:=univ) (fun v _ => input v)
    have total := Nat.cast_le (α:=ℝ) |>.mpr (total_varying (L:=L) G hb)
    push_cast at total
    have T := sum_le_sum (s:=univ) (fun t _ => term t)
    have P : ∑ j : Block n b, h (processor G j) ≤
        ((n ⌈/⌉ b : ℕ):ℝ)*(4*b:ℕ)*entropyBits (1/100) := by
      change ∑ j, finiteEntropy (p.map (rowPin G fits high low z target (processor G j))).mass / Real.log 2 ≤ _
      rw [← sum_div,entropyBits,← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ logpos.le
      convert! processor_entropy hb p z target budget using 1
    simp only [sum_const_zero] at T
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    exact (add_le_add (I.trans total) (add_le_add P T)).trans_eq (by ring)

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
