import OAI.Hierarchy.ProbePermutationRoute
import OAI.Hierarchy.ProbeStageMaskCost
import OAI.Hierarchy.FixedMaskAdvice

namespace OAI
/-! # The advised permutation route and its total fallback charges -/

noncomputable section
namespace Hierarchy.ProbeStage

open scoped BigOperators

/-- One fixed table for every level and every matching of the format. -/
def formatAdvice (h d : ℕ) : MaskAdvice (radix h d) (8*(4*h+2)) := by
  have fits : radix h d ≤ 2^h := Nat.pow_le_pow_right (by decide) (Nat.div_le_self h (9*d))
  let ex := FixedMaskAdvice.exists_advice (radix_pos h d) fits
  exact ⟨ex.choose,ex.choose_spec⟩

def advisedRoute (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    Routes (Fin (2^h)) (permutationFabric h d) (permutationTiles π).first (permutationTiles π).last :=
  route _ _ _ (fun p => allocateMasked p (radix_pos h d) (formatAdvice h d).row) _ (permutationTiles π)

def MaskAdvice.roundCharge {B ℓ n m : ℕ} {G : Type} [Fintype G]
    (A : MaskAdvice B ℓ) (pos : 0<B) (p : Tiles (Fin n) G m) : ℕ := by
  classical
  exact ∑ g : G × Fin (blocks m B), (B * (A.sourceCharges p pos g).card +
    B * (A.targetCharges p pos g).card)

private theorem roundCharge_le {B ℓ n m : ℕ} {G : Type} [Fintype G]
    (A : MaskAdvice B ℓ) (pos : 0<B) (p : Tiles (Fin n) G m) :
    A.roundCharge pos p ≤ 2 * (Fintype.card G * blocks m B * blockSize B) := by
  classical
  unfold MaskAdvice.roundCharge
  calc
    _ ≤ ∑ _ : G × Fin (blocks m B), (blockSize B + blockSize B) := by
      apply Finset.sum_le_sum
      intro g _
      exact add_le_add (A.scan_bounds p pos g).1 (A.scan_bounds p pos g).2
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; ring

def MaskAdvice.fallbacks {B ℓ n m : ℕ} {G : Type} (A : MaskAdvice B ℓ)
    (pos : 0<B) (p : Tiles (Fin n) G m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => freeBits (A.row (maskIndex p pos i))
    (Greedy.available (leftBlock p pos) (rightBlock p pos) (Greedy.before n i)
      (Greedy.colors pos (A.pick p pos) (leftBlock p pos) (rightBlock p pos) i) i) = ∅

theorem fallback_cost_le {B ℓ n m : ℕ} {G : Type} [Fintype G]
    (A : MaskAdvice B ℓ) (pos : 0<B) (p : Tiles (Fin n) G m) :
    B * (A.fallbacks pos p).card ≤ A.roundCharge pos p := by
  classical
  let both := fun g => A.sourceCharges p pos g ∪ A.targetCharges p pos g
  have cover : A.fallbacks pos p ⊆ Finset.univ.biUnion both := by
    intro i hi
    rcases A.charged p pos i (Finset.mem_filter.mp hi).2 with left | right
    · exact Finset.mem_biUnion.mpr ⟨leftBlock p pos i,Finset.mem_univ _,Finset.mem_union_left _ left⟩
    · exact Finset.mem_biUnion.mpr ⟨rightBlock p pos i,Finset.mem_univ _,Finset.mem_union_right _ right⟩
  have count := (Finset.card_le_card cover).trans Finset.card_biUnion_le
  calc
    _ ≤ B*(∑ g,(both g).card) := Nat.mul_le_mul_left B count
    _ = ∑ g,B*(both g).card := Finset.mul_sum ..
    _ ≤ A.roundCharge pos p := by
      apply Finset.sum_le_sum
      intro g _
      exact (Nat.mul_le_mul_left B (Finset.card_union_le (A.sourceCharges p pos g)
        (A.targetCharges p pos g))).trans_eq (Nat.mul_add ..)

/-- Count the charges along exactly the sequence of shorter inner matchings
chosen by the fixed mask algorithm. -/
def MaskAdvice.routeCharge {B ℓ n : ℕ} (A : MaskAdvice B ℓ) (pos : 0<B) :
    (q : ℕ) → {G : Type} → [Fintype G] → {m : ℕ} → Tiles (Fin n) G m → ℕ
  | 0,_,_,_,_ => 0
  | q+1,_,_,_,p => A.roundCharge pos p +
      A.routeCharge pos q (inner p pos (allocateMasked p pos A.row))

theorem charge_aux {h d n ℓ : ℕ} (hd : 1≤d) (A : MaskAdvice (radix h d) ℓ)
    (remaining : ℕ) : ∀ j : ℕ, j+remaining=rounds d → ∀ {G : Type} [Fintype G],
    Fintype.card G=(radix h d)^j → ∀ p : Tiles (Fin n) G (2^widthLog h d j),
    A.routeCharge (radix_pos h d) remaining p ≤ remaining*(2*4^rounds d*2^h) := by
  induction remaining with
  | zero => intros; simp [MaskAdvice.routeCharge]
  | succ r ih =>
    intro j eq G _ card p
    have here : j<rounds d := by omega
    have total := roundCharge_le A (radix_pos h d) p
    rw [card,blocks_exact,blockSize_radix] at total
    have split : 2^blockLog h d j * 2^(9*digit h d) = 2^widthLog h d j := by
      rw [← pow_add,widthLog,Nat.add_comm]
    rw [Nat.mul_assoc _ (2^blockLog h d j),split,material_exact hd here.le] at total
    have bound := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2^h)
      (Nat.pow_le_pow_right (by decide : 0<4) here.le))
    have step : A.roundCharge (radix_pos h d) p ≤ 2*4^rounds d*2^h :=
      total.trans (bound.trans_eq (by ring))
    let t := inner p (radix_pos h d) (allocateMasked p (radix_pos h d) A.row)
    have eqsize := inner_exact (h:=h) here
    have nextCard : Fintype.card (G × Fin (radix h d)) = (radix h d)^(j+1) := by
      rw [Fintype.card_prod,Fintype.card_fin,card,pow_succ]
    have tail : A.routeCharge (radix_pos h d) r t ≤ r*(2*4^rounds d*2^h) := by
      have enough := ih (j+1) (by omega) nextCard
      rw [← eqsize] at enough
      exact enough t
    exact (add_le_add step tail).trans_eq (by ring)

theorem charge_linear (h d : ℕ) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) :
    (formatAdvice h d).routeCharge (radix_pos h d) (rounds d) (permutationTiles π) ≤
      rounds d*(2*4^rounds d*2^h) := by
  have H := charge_aux (n:=2^h) hd (formatAdvice h d) (rounds d) 0
    (by omega) (G:=Unit) (by simp)
  rw [widthLog_start (h:=h) hd] at H
  exact H (permutationTiles π)

/-- Count precisely the fallback invocations in the advised hierarchy, at
the full B color inspections per fallback. -/
def MaskAdvice.inspections {B ℓ n : ℕ} (A : MaskAdvice B ℓ) (pos : 0<B) :
    (q : ℕ) → {G : Type} → [Fintype G] → {m : ℕ} → Tiles (Fin n) G m → ℕ
  | 0,_,_,_,_ => 0
  | q+1,_,_,_,p => B*(A.fallbacks pos p).card +
      A.inspections pos q (inner p pos (allocateMasked p pos A.row))

theorem inspections_le {B ℓ n : ℕ} (A : MaskAdvice B ℓ) (pos : 0<B) (q : ℕ)
    {G : Type} [Fintype G] {m : ℕ} (p : Tiles (Fin n) G m) :
    A.inspections pos q p ≤ A.routeCharge pos q p := by
  induction q generalizing G m with
  | zero => rfl
  | succ q ih => exact add_le_add (fallback_cost_le A pos p) (ih _)

theorem permutation_inspections_linear (h d : ℕ) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) :
    (formatAdvice h d).inspections (radix_pos h d) (rounds d) (permutationTiles π) ≤
      rounds d*(2*4^rounds d*2^h) :=
  (inspections_le ..).trans (charge_linear h d hd π)

end Hierarchy.ProbeStage

end
end OAI
