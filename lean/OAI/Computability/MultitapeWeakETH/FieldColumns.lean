import OAI.Computability.MultitapeWeakETH.CorrectedDisplay
import OAI.Computability.MultitapeWeakETH.Retention

/-! # Applying the weighted four-column lemma to the successful field tables -/

namespace OAI.Computability.MultitapeWeakETH

open Finset
open scoped Classical BigOperators
noncomputable section

variable {n b : ℕ} {K : Type} [Field K] (G : Network n b)
    (tables : Word n → (v : Fin G.vertices) → G.View v → K)

/-- Residues are uniform words, including all inputs with leading zeros. -/
theorem residue_density (P : Word n → Word n → Prop) :
    density P = 𝔼 x : Fin (2^n), 𝔼 y : Fin (2^n),
      if P (residueWord n x) (residueWord n y) then (1:ℝ) else 0 := by
  let indicator (p : Word n × Word n) : ℝ := if P p.1 p.2 then 1 else 0
  let eqv := (residueWord n).prodCongr (residueWord n)
  have equiv := Fintype.expect_equiv eqv (indicator ∘ eqv) indicator (fun _ => rfl)
  rw [← Finset.expect_product']
  simp only [univ_product_univ]
  calc
    density P = 𝔼 p, indicator p := by simp [density,indicator,Fintype.expect_eq_sum_div_card]
    _ = _ := equiv.symm

def quadColumns (y z y' z' : Fin (2^n)) : Fin 4 → Fin (2^n) := ![y,z,y',z']

def commonRows (c : Fin 4 → Fin (2^n)) (x : Fin (2^n)) : Bool :=
  decide (∀ i, G.FieldGood tables (residueWord n x) (residueWord n (c i)))

def rowMass (c : Fin 4 → Fin (2^n)) : ℝ :=
  𝔼 x, if commonRows G tables c x then 1 else 0

theorem rowMass_le_one (c : Fin 4 → Fin (2^n)) : rowMass G tables c ≤ 1 := by
  unfold rowMass
  simpa using (expect_le_expect (s:=univ) (g:=fun _ => (1:ℝ)) (fun x _ =>
    show (if commonRows G tables c x then (1:ℝ) else 0) ≤ 1 by split <;> norm_num))

theorem exists_field_columns (u : ℕ) {γ : ℝ} (hγ : γ < 1) :
    ∃ c : Fin 4 → Fin (2^n), c 2-c 3 = 2^u*(c 0-c 1) ∧
      (density (G.FieldGood tables))^4*((2:ℝ)^γ)^(trailing n (c 0-c 1).val) ≤
        (1+1/(2-(2:ℝ)^γ))*rowMass G tables c := by
  let good (x y : Fin (2^n)) := decide (G.FieldGood tables (residueWord n x) (residueWord n y))
  obtain ⟨y,z,y',z',shift,h⟩ := exists_shifted_columns n u good hγ
  let c := quadColumns y z y' z'
  refine ⟨c,shift,?_⟩
  have joint (x : Fin (2^n)) :
      (if commonRows G tables c x then (1:ℝ) else 0) =
        ((if good x y then 1 else 0)*(if good x y' then 1 else 0)) *
        ((if good x z then 1 else 0)*(if good x z' then 1 else 0)) := by
    have iff : commonRows G tables c x = true ↔
        ((good x y ∧ good x z) ∧ (good x y' ∧ good x z')) := by
      simp [commonRows,good,c,quadColumns,Fin.forall_fin_succ, and_assoc]
    simp only [iff]
    split_ifs <;> simp_all
  rw [residue_density,rowMass]
  simp_rw [joint]
  simpa only [good,decide_eq_true_eq,show c 0 = y by rfl,show c 1 = z by rfl] using h

theorem joinPayload_low {L : ℕ} (fits : L ≤ n) (h : Fin (2^(n-L))) (l : Fin (2^L)) :
    (joinPayload n L fits (h,l)).val % 2^L = l.val := by
  change (l.val+2^L*h.val) % 2^L = _
  simp [Nat.mod_eq_of_lt l.isLt]

namespace FoldedNetwork

/-- Once the high input bits and the four columns have been fixed, a
successful low part selects four near-product outputs. Their corrected
display has the odd multiple of that low part at both shifted endpoints. -/
theorem returns_on_low {N L s u d : ℕ} [NeZero N] (hb : 0 < b)
    (fits : s+u+L ≤ n) (odd : Odd d) (hL : L ≤ n) (high : Fin (2^(n-L)))
    (low : Fin (2^L)) (c : Fin 4 → Fin (2^n))
    (factor : (c 0-c 1).val = 2^s*d) (shift : c 2-c 3=2^u*(c 0-c 1))
    (good : commonRows G tables c (joinPayload n L hL (high,low))) :
    let x := joinPayload n L hL (high,low)
    let target := fun i => x*c i
    let w := oddMultiplier L d odd low
    let l := position s (show s+L ≤ n by omega)
    let r := position (s+u) fits
    ∃ (z : Fin 4 → Word n) (k : K), k ≠ 0 ∧ (∀ i, 100*errors (z i) (residueWord n (target i)) ≤ n) ∧
      VPVNP.WireTensor.applyLocal (fun v => maps G hb l r (fun i => tables (residueWord n (c i)))
        v (pinFor G (residueWord n x) (errorMasks b z target) v)) (typedSupply G K (N:=N)).coeff =
        fun ext => if ext = VPVNP.WireTensor.edgeAssignment (destination G hb ∘ l) (destination G hb ∘ r)
          (fun j : Fin L => w.val.testBit j.val) then k else 0 := by
  intro x target w l r
  have allGood : ∀ i, G.FieldGood tables (residueWord n x) (residueWord n (c i)) := of_decide_eq_true good
  choose z support err using allGood
  choose k nz returns using support
  refine ⟨z,∏ i,k i,prod_ne_zero_iff.mpr (fun i _ => nz i),?_,?_⟩
  · simpa only [lowProduct_residueWord] using err
  have intervals := shifted_payload odd fits x (c 0-c 1) (c 2-c 3) factor shift
  have same : (⟨x.val % 2^L,Nat.mod_lt _ (by positivity)⟩ : Fin (2^L)) = low :=
    Fin.ext (joinPayload_low hL high low)
  dsimp only at intervals
  rw [same] at intervals
  apply corrected_display G hb s u fits _ _ z k returns target w
  · change (x*c 0-x*c 1).val / 2^s % 2^L = _
    rw [← mul_sub]
    exact intervals.1
  · change (x*c 2-x*c 3).val / 2^(s+u) % 2^L = _
    rw [← mul_sub]
    exact intervals.2

end FoldedNetwork
end
end OAI.Computability.MultitapeWeakETH
