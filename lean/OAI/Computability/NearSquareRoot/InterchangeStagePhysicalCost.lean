import OAI.Computability.NearSquareRoot.InterchangeStageWords
import OAI.Computability.NearSquareRoot.InterchangeBatch

/-!
# Recursive price of the concrete Hamming address instructions

The price is evaluated on the literal stage script. Preparations are charged
once per incident copy and each triangular query instruction costs zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open StageRoute StageLedger Filter

/-- Exact support sizes of the four paid conversions give the factored finite
stage bound, for any layout atlas and any choices of selected rows and columns. -/
theorem RectangleAtlas.stage_cost_le {a m inc : ℕ} {L B H : Type} [DecidableEq L]
    [Fintype L] [Fintype B] [Fintype H] {r : B → Rectangle L} (atlas : RectangleAtlas r a)
    (I J : H → L) (Row : Type) [Fintype Row] {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] (M : Matrix H H K) (A₀ : E →+ E) (A : Fin m → E →+ E)
    (hinc : ∀ side v, Fintype.card (Incident r side v) ≤ inc) :
    Fintype.card Row * StageScript.cost (fun u => (atlas.routeWord u).price)
      (stage r I J M A₀ A) ≤ 2*(54*(a+2))*Fintype.card Row*(1+inc)*(Fintype.card L+m*Fintype.card H) := by
  simpa only [Fintype.card_fin] using scalar_stage_cost_le Row M A₀ A
    (fun u => (atlas.routeWord u).price) (atlas.routeWord_price_idle I J)
    (atlas.routeWord_price_align I J) (atlas.routeWord_price_unalign I J)
    (fun _ => atlas.routeWord_price_le _) (fun _ => atlas.routeWord_price_le _)
    (fun _ _ => atlas.routeWord_price_le _) (fun _ _ => atlas.routeWord_price_le _) hinc

/-- The concrete Hamming rectangles have a single physical layout for all
stages meeting the batch exponent. The exponent counts the literal recursive
prices of their supported words, together with the spectral repair calls. -/
theorem eventually_hamming_physical_stage_cost (p : ℕ) [Fact p.Prime] (E : Type)
    [AddCommGroup E] [Module (ZMod p) E] (γ C : ℝ)
    (hγ : 1/2 + (3*p-1)/(p : ℝ)^2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := 2^k
      let N := Fintype.card (Label p q)
      let rank := (hammingLabelMatrix p q).rank
      let a := (2*p-1)*Fintype.card (Word p q)
      let r := hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos)
      (m : ℝ) ≤ (q : ℝ) ^ (p^2) ∧ (q : ℝ) ≤ 2 * (m : ℝ)^((p^2 : ℕ) : ℝ)⁻¹ ∧
      ∃ atlas : RectangleAtlas r a, ∀ stages R defect : ℕ, 0 < R →
        (stages : ℝ) ≤ C * Real.sqrt (m * (1+Real.log m)) → 2*m^3*defect ≤ R →
        ∀ (I J : Fin rank → Label p q) (M : Matrix (Fin rank) (Fin rank) (ZMod p))
          (A₀ : Fin stages → (Fin R → E) →+ (Fin R → E))
          (A : Fin stages → Fin m → (Fin R → E) →+ (Fin R → E)),
          ((∑ s, R * StageScript.cost (fun u => (atlas.routeWord u).price)
            (stage r I J M (A₀ s) (A s)) : ℕ) : ℝ) +
            4*(m : ℝ)*defect*N ≤ (R : ℝ)*N*(m : ℝ)^γ := by
  filter_upwards [eventually_hamming_script_cost p E γ C 54 hγ] with m hm
  obtain ⟨k,hlo,hup,hbudget⟩ := hm
  obtain ⟨atlas⟩ := hamming_atlas p k (Fact.out : p.Prime).pos
  refine ⟨k,hlo,hup,atlas,?_⟩
  intro stages R defect hR hst hdef I J M A₀ A
  have cap (u : Move _ (Fin m) I J) : (atlas.routeWord u).price ≤
      54*Fintype.card (GramIndex (2*p-1) (Word p (2^k))) := by
    simpa only [card_gramIndex, Nat.add_comm 2] using atlas.routeWord_price_le u
  exact hbudget stages R defect hR hst hdef I J M A₀ A (fun _ u => (atlas.routeWord u).price)
    (fun _ => atlas.routeWord_price_idle I J) (fun _ => atlas.routeWord_price_align I J)
    (fun _ => atlas.routeWord_price_unalign I J) (fun _ _ => cap _) (fun _ _ => cap _)
    (fun _ _ _ => cap _) (fun _ _ _ => cap _)

/-- The finite stage bound uses the same integer `batchCalls` as the reserve
contraction theorem. It holds for every dyadic alphabet, so the alphabet can
be chosen jointly for the recursive price and the physical address length. -/
theorem hamming_cost_le_batchCalls (p k m : ℕ) [Fact p.Prime] {E : Type}
    [AddCommGroup E] [Module (ZMod p) E] :
    let q := 2^k
    let N := Fintype.card (Label p q)
    let rank := (hammingLabelMatrix p q).rank
    let a := (2*p-1)*Fintype.card (Word p q)
    let r := hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos)
    let stages := 4*SwapRepair.order m
    let R := independentRows m
    ∀ (atlas : RectangleAtlas r a) (I J : Fin rank → Label p q)
      (M : Matrix (Fin rank) (Fin rank) (ZMod p)) (A₀ : Fin stages → E →+ E)
      (A : Fin stages → Fin m → E →+ E),
      (∑ s, R * StageScript.cost (fun u => (atlas.routeWord u).price) (stage r I J M (A₀ s) (A s))) +
        4*m*correctedRows m*N ≤ batchCalls p k m 108 := by
  intro q N rank a r stages R atlas I J M A₀ A
  have hD : 2*(54*(a+2)) = 108*Fintype.card (GramIndex (2*p-1) (Word p q)) := by
    rw [card_gramIndex]
    dsimp only [a]
    omega
  let inc := labelIncidence p k (Fact.out : p.Prime).pos
  have hstage (s : Fin stages) := atlas.stage_cost_le I J (Fin R) M (A₀ s) (A s)
    (hamming_incident_le p k (Fact.out : p.Prime).pos)
  simp only [Fintype.card_fin,hD] at hstage
  dsimp only [batchCalls]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _s : Fin stages, 108*Fintype.card (GramIndex (2*p-1) (Word p q))*R*(1+inc)*
          (N+m*rank) := Finset.sum_le_sum fun s _ => hstage s
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

end Interchange

end NearSquareRoot
end Computability
end OAI
