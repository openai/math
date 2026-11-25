import OAI.Computability.MultitapeWeakETH.BitRates
import OAI.Computability.MultitapeWeakETH.BinaryDisplay
import OAI.Computability.MultitapeWeakETH.PinBudget
import OAI.Computability.MultitapeWeakETH.ExternalRoot

/-! # Entropy price of a retained payload on the common folded supply -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork
open VPVNP.WireTensor MatrixMultiplication.Foundation Finset
open scoped Classical BigOperators
noncomputable section

variable {n b N Q : ℕ} [NeZero N] [NeZero b] {K X : Type} [Field K] [PseudoMetricSpace X]
    (G : Network n b) (tables : Word n → (v : Fin G.vertices) → G.View v → K)

def supplyCost (place : Site G N → X) (a : ℝ) :=
  ∑ e, (width G e:ℝ)*(a*dist (place (src G e)) (place (dst G e)))

/-- All prices use the same graph, side lengths, scale and root. Only the
source law, rate profile, pins and local matrices vary with the shift. -/
theorem shift_law (realizable : VPVNP.WireGeometry.RealizableConfigurations K X)
    (place : Site G N → X) (root : X) (a : ℝ) (ha : 0 ≤ a)
    (s d : ℕ) (t : Fin N) (c : Fin 4 → Fin (2^n))
    (factor : (c 0-c 1).val = 2^s*d) (odd : Odd d) (shift : c 2-c 3=2^(t.val*b)*(c 0-c 1))
    (fits : s+t.val*b+Q*(N*b) ≤ n) (pos : 0 < rowMass G tables c) :
    let L := Q*(N*b)
    ∃ (rate : Fin L → ℝ) (h : Site G N → ℝ),
      (∀ j, 0 ≤ rate j ∧ rate j ≤ 1) ∧ (∀ v, 0 ≤ h v ∧ h v ≤ 4*b) ∧
      L + Real.logb 2 (rowMass G tables c) ≤ ∑ j, rate j ∧
      (∑ v, h v) ≤ L + ((n ⌈/⌉ b : ℕ):ℝ)*(4*b:ℕ)*entropyBits (1/100) ∧
      (∑ j, rate j*(a*dist (place (terminal G (foldedTerminal s j)))
        (place (terminal G (foldedTerminal s j+t))))) ≤
        supplyCost G place a + ∑ v, h v*(a*dist (place v) root) := by
  intro L
  have hL : L ≤ n := by dsimp [L]; omega
  let good := commonRows G tables c
  obtain ⟨high,size⟩ := fix_high_payload hL odd good (show rowMass G tables c ≤ _ by rfl)
  let lows := univ.filter fun low => good (joinPayload n L hL (high,low))
  change rowMass G tables c*(2:ℝ)^L ≤ ((lows.image (oddMultiplier L d odd)).card:ℝ) at size
  rw [card_image_of_injective _ (oddMultiplier L d odd).injective] at size
  have positive := (mul_pos pos (pow_pos (by norm_num : (0:ℝ)<2) L)).trans_le size
  let _ : Nonempty ↥lows := (card_pos.mp (Nat.cast_pos.mp positive)).to_subtype
  let p := FiniteLaw.uniform ↥lows
  let low (x : ↥lows) := x.val
  let word (x : ↥lows) := oddMultiplier L d odd (low x)
  have inj : Function.Injective word := (oddMultiplier L d odd).injective.comp Subtype.val_injective
  let target (x : ↥lows) (i : Fin 4) := joinPayload n L hL (high,low x)*c i
  let labels := payloadLabels word
  let rate := bitRate p labels L
  let hb := NeZero.pos b
  let l := position s (show s+L ≤ n by dsimp [L]; omega)
  let r := position (s+t.val*b) fits
  have rows (x : ↥lows) := returns_on_low (N:=N) G tables hb fits odd hL high (low x) c factor shift
    ((mem_filter.mp x.property).2)
  choose z scalar nz budget disp using rows
  let pin := rowPin (N:=N) G hL high low z target
  let h := charge G p pin
  have pinBound := pin_budget (N:=N) G hb p hL high low z target budget
  refine ⟨rate,h,bitRate_range p labels L,pinBound.1,?_,pinBound.2,?_⟩
  · rw [show (∑ j, rate j) = _ from sum_bitRate word inj,Fintype.card_coe]
    have logSize := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos pos (pow_pos (by norm_num) _)) size
    rw [Real.logb_mul pos.ne' (pow_pos (by norm_num) _).ne',Real.logb_pow,Real.logb_self_eq_one (by norm_num)] at logSize
    linarith
  · let u := destination G (N:=N) hb ∘ l
    let v := destination G (N:=N) hb ∘ r
    let M := binaryMaps G (N:=N) hb l r (fun i => tables (residueWord n (c i)))
    have paired := paired_entropy_external_root realizable place root (src G) (dst G) (width G)
      (Pin G) pin p labels L (payload_separates word inj) u v M scalar nz (by
        intro x
        apply (binary_contraction G hb l r _ (fun v => pin v x)).trans
        apply (disp x).trans
        funext y
        split <;> first | rfl | (split <;> first | rfl | contradiction))
    have left (j : Fin L) : u j = terminal G (foldedTerminal s j) := by
      apply congrArg (terminal G)
      apply Fin.ext
      exact (foldedTerminal_val s j).symm
    have right (j : Fin L) : v j = terminal G (foldedTerminal s j+t) :=
      congrArg (terminal G) (Difference.shifted_terminal t s j)
    change (∑ j, rate j * dist (place (u j)) (place (v j))) ≤
      (∑ e, (width G e:ℝ)*dist (place (src G e)) (place (dst G e))) +
      ∑ v, h v * dist root (place v) at paired
    simp_rw [left,right] at paired
    have scaled := mul_le_mul_of_nonneg_left paired ha
    simp only [supplyCost]
    simp_rw [mul_left_comm _ a _,← mul_sum,← mul_add]
    simpa only [dist_comm root] using scaled

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
