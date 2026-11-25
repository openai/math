import OAI.Hierarchy.TaggedWideSockets
import OAI.Hierarchy.TaggedShorterAmplified
import OAI.Hierarchy.TaggedBatchSlices
import OAI.Hierarchy.TaggedShorterAssembly
import OAI.Hierarchy.TaggedMenuFit

namespace OAI
/-! # Installing amplified shorter batches in the wide-width induction -/

noncomputable section
namespace Hierarchy.Tagged

open Catalyst CatalystSubstitution CorrectionFrame Filter Real
open scoped BigOperators

namespace ShorterBank

/-- Physical cost is meaningful for all arguments of an assembly map, including
arguments outside its gap guarantee. A board with only its exposed pins supplies
the size bound on those arguments. -/
private def vacant (F : Type*) (k p : ℕ) : Approximation F k p :=
  ⟨fun _ => 0, ⟨0,0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩

private theorem vacant_size (F : Type*) [Field F] (k p : ℕ) : (vacant F k p).size = p := by
  let : IsEmpty (Wire (fun _ : Fin k => 0) × Bool) := ⟨fun j => Fin.elim0 j.1.2⟩
  let e := Equiv.sumEmpty (Fin p) (Wire (fun _ : Fin k => 0) × Bool)
  change 0 + 0 + Fintype.card (Catalyst.Port p (fun _ : Fin k => 0)) = p
  simp only [Nat.zero_add]
  exact (Fintype.card_congr e).trans (Fintype.card_fin p)

end ShorterBank

/-- The amplification price `K` is chosen once, before the protocol. -/
def SliceAmplifier (F : Type*) [Field F] (K : ℕ) : Prop :=
  ∀ (k : ℕ) {C fraction b : ℝ}, 6 ≤ C → 0 < fraction → 0 < b →
    ∃ h₀ t₀ : ℕ, ∀ (h : ℕ) (B : ShorterBank),
      h₀ ≤ h → t₀ ≤ B.height → 3*B.height ≤ 2*h → 0 < B.copies →
      fraction*(2:ℝ)^h ≤ (B.copies:ℝ)*2^B.height →
      logb 2 B.copies ≤ (B.height:ℝ)^b → 0 < B.payload → 0 < B.capacity →
      2*(k:ℝ)*(B.slices:ℝ) ≤ gap C h →
      ∀ X : ∀ j, Approximation F k (pins B.height (B.width j)),
      ∃ Y : B.Output F k, Y.size ≤ (K*B.copies)*∑ j,(X j).size ∧
        ((∀ j, (X j).Gap (coeff F B.height (B.width j)) (gap C B.height)) →
          Y.Gap (B.target F) (2*gap C h))

namespace ShorterBank

/-- Amplify each balanced slice before taking their product on the shared tags.
The number of substituted calls for this whole bank is one. -/
theorem amplified_slices (F : Type*) [Field F] :
    ∃ K : ℕ, 0 < K ∧ SliceAmplifier F K := by
  obtain ⟨K,make⟩ := shorter_batches F
  refine ⟨K+1,by omega,fun k {C fraction b} hC hf hb => ?_⟩
  obtain ⟨h₀,t₀,build⟩ := make k hC hf hb (by norm_num : (0:ℝ) ≤ 3)
  refine ⟨h₀,t₀,fun h B hh ht short hc slots logsize wp cap allowance X => ?_⟩
  have per (j : Fin B.slices) :
      ∃ Y : Approximation F k (B.copies*pins B.height (B.width j)),
        Y.size ≤ ((K+1)*B.copies)*(X j).size ∧
        ((X j).Gap (coeff F B.height (B.width j)) (gap C B.height) →
          Y.Gap (dataProduct B.copies (coeff F B.height (B.width j))) (3*gap C h)) := by
    by_cases good : (X j).Gap (coeff F B.height (B.width j)) (gap C B.height)
    · obtain ⟨Y,_,cost,price⟩ := build h B.height B.copies (B.width j)
        hh ht short hc slots logsize (X j) good
      exact ⟨Y,cost.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ K))),fun _ => price⟩
    · refine ⟨vacant F k _,?_,fun yes => (good yes).elim⟩
      rw [vacant_size]
      have p : pins B.height (B.width j) ≤ (X j).size := by
        simp [Approximation.size,Catalyst.Port]; omega
      calc
        _ ≤ B.copies*(X j).size := Nat.mul_le_mul_left _ p
        _ ≤ _ := by
          apply Nat.mul_le_mul_right
          simpa only [one_mul] using
            (Nat.mul_le_mul_right B.copies (show 1≤K+1 by omega))
  choose Z size price using per
  obtain ⟨Y,cost,join⟩ := Slices.batch B.copies B.width
    (TaggedWidthSlices.sum_width cap) (TaggedWidthSlices.count_pos wp cap) Z
  refine ⟨Y,cost.trans ?_,fun good => ?_⟩
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => size j)
  · have margin : 2 * gap C h ≤ 3 * gap C h - 2 * (k : ℝ) * (B.slices : ℝ) := by
      linarith only [allowance]
    exact Approximation.Gap.mono Y (join (3 * gap C h) (fun j => price j (good j))) margin

end ShorterBank

private def spread {I : Type} {N : ℕ} (e : Fin N ≃ I) (P : I → Type*)
    (X : ∀ i,P (e i)) (x : I) : P x :=
  Equiv.piCongrLeft P e X x

private theorem spread_at {I : Type} {N : ℕ} (e : Fin N ≃ I) (P : I → Type*)
    (X : ∀ i,P (e i)) (i : Fin N) : spread e P X (e i) = X i := by
  exact Equiv.piCongrLeft_apply_apply ..

/-- Substituting the actual amplified banks and the control calls produces a
strictly shorter recurrence. The host bill includes every exposed socket.
The two numerical half-budgets are the conclusions of `eventually_menu_fit`
and `eventually_fixed_work`. -/
theorem shorterCalls_of_banks {F : Type*} [Field F] {k n h w K : ℕ} {A C fixed : ℝ}
    (u : ℝ → ℝ) (B : Fin n → ShorterBank) (controls : List (Occurrence F k))
    (smaller : ∀ i,(B i).height < h)
    (within : ∀ i j,inRange A (B i).height ((B i).width j))
    (produce : ∀ i, ∀ X : ∀ j,Approximation F k (pins (B i).height ((B i).width j)),
      ∃ Y : (B i).Output F k, Y.size ≤ (K*(B i).copies)*∑ j,(X j).size ∧
        ((∀ j,(X j).Gap (coeff F (B i).height ((B i).width j)) (gap C (B i).height)) →
          Y.Gap ((B i).target F) (2*gap C h)))
    (host : ∀ Y,Host F k (pins h w) (Sockets (bankCalls B Y controls)))
    (booked : ∀ Y,(hostSize (host Y):ℝ) + ((controls.map (·.replacement.size)).sum:ℝ) ≤ fixed)
    (original : ∀ Y,(tableApprox (host Y).width
      (exactValue (bankCalls B Y controls) (host Y))).Gap (coeff F h w) (2*gap C h))
    (controlGap : ∀ o∈controls,o.replacement.Gap o.target (2*gap C h))
    (loss : 2*(k:ℝ)*((n:ℝ)+controls.length) ≤ gap C h)
    (fixedWork : fixed ≤ unitWork u h w/2)
    (budget : ∑ i, ((K:ℝ)*(B i).copies) *
      ∑ j,unitWork u (B i).height ((B i).width j) ≤ unitWork u h w/2) :
    ∃ r : ShorterCalls F k h w A C, FitsWork u r := by
  classical
  let I := Σ i : Fin n, Fin (B i).slices
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let P (x : I) := Approximation F k (pins (B x.1).height ((B x.1).width x.2))
  let height (i : Fin (Fintype.card I)) := (B (e i).1).height
  let payload (i : Fin (Fintype.card I)) := (B (e i).1).width (e i).2
  let multi (i : Fin (Fintype.card I)) := K*(B (e i).1).copies
  let Y (X : ∀ i,P (e i)) (i : Fin n) := (produce i (fun j => spread e P X ⟨i,j⟩)).choose
  have size (X : ∀ i,P (e i)) (i : Fin n) :=
    (produce i (fun j => spread e P X ⟨i,j⟩)).choose_spec.1
  have price (X : ∀ i,P (e i)) (i : Fin n) :=
    (produce i (fun j => spread e P X ⟨i,j⟩)).choose_spec.2
  let calls (X : ∀ i,P (e i)) := bankCalls B (Y X) controls
  have billed (X : ∀ i,P (e i)) :
      (hostSize (host (Y X)):ℝ) + (((calls X).map (·.replacement.size)).sum:ℝ) ≤
        fixed + ∑ i,(multi i:ℝ)*((X i).size:ℝ) := by
    let charge (x : I) := (K*(B x.1).copies)*(spread e P X x).size
    have short : (∑ i,(Y X i).size) ≤ ∑ i,multi i*(X i).size := calc
      _ ≤ ∑ i,(K*(B i).copies)*∑ j,(spread e P X ⟨i,j⟩).size :=
        Finset.sum_le_sum fun i _ => size X i
      _ = ∑ x : I,charge x := by rw [Fintype.sum_sigma]; simp [charge,Finset.mul_sum]
      _ = ∑ i,charge (e i) := (e.sum_comp charge).symm
      _ = _ := by simp only [charge,spread_at,multi]
    have cast : (∑ i,((Y X i).size:ℝ)) ≤ ∑ i,(multi i:ℝ)*((X i).size:ℝ) := by exact_mod_cast short
    have eq : ((calls X).map (fun o => (o.replacement.size : ℝ))).sum =
        (∑ i,((Y X i).size : ℝ)) + (controls.map (fun o => (o.replacement.size : ℝ))).sum := by
      simp [calls,bankCalls,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    rw [eq]
    linarith only [booked (Y X),cast]
  have adequate (X : ∀ i,P (e i))
      (good : ∀ i,(X i).Gap (coeff F (height i) (payload i)) (gap C (height i))) :
      ∀ o∈calls X,o.replacement.Gap o.target (2*gap C h) := by
    intro o mem
    obtain mem | mem := List.mem_append.mp mem
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
      apply price X i
      intro j
      let x : I := ⟨i,j⟩
      have all (x : I) : (spread e P X x).Gap
          (coeff F (B x.1).height ((B x.1).width x.2)) (gap C (B x.1).height) := by
        obtain ⟨l,rfl⟩ := e.surjective x
        rw [spread_at]
        exact good l
      exact all x
    · exact controlGap o mem
  let r := fromCallList height payload multi (fun i => smaller (e i).1)
    (fun i => within (e i).1 (e i).2) calls (fun X => host (Y X)) billed
    (fun X => original (Y X)) adequate (fun X => by
      simp only [calls,bankCalls,List.length_append,List.length_ofFn,Nat.cast_add]
      linarith only [loss])
  refine ⟨r,ShorterCalls.fitsWork_of_menu u r (fun i => (B i).slices)
    (fun i => (B i).height) (fun i => (B i).copies) (fun i => (B i).width)
    e (fun _ => rfl) (fun _ => rfl) (fun i => ?_) fixedWork budget⟩
  change ((K*(B (e i).1).copies:ℕ):ℝ) ≤ (K:ℝ)*(B (e i).1).copies
  exact_mod_cast le_rfl

end Hierarchy.Tagged

end
end OAI
