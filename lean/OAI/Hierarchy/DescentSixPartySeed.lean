import OAI.Computability.VPVNP.WireCATZero
import OAI.Computability.VPVNP.MotifBase
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI
/-! # The fixed six-party strict wire identity for trace descent

The two demands are AB and CD. The eight supplies are AC, BC, AM, BN,
CM, CN, DM, DN. A strict gap in their unweighted total width pays for the
complete selector and for the additive rounding charge on eight ports. -/

noncomputable section
namespace Hierarchy.DescentSixParty

open scoped Classical BigOperators
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.VPVNP.WireTensor.RestrictionClass Computability.VPVNP.MotifBase

def demandSrc : Fin 2 → Fin 6 := ![0,2]
def demandDst : Fin 2 → Fin 6 := ![1,3]
def supplySrc : Fin 8 → Fin 6 := ![0,1,0,1,2,2,3,3]
def supplyDst : Fin 8 → Fin 6 := ![2,2,4,5,4,5,4,5]

/-- Agreement on the eight supply edges forces every coloring to be constant. -/
theorem connected {I : Type*} (color : Fin 6 → I)
    (onEdge : ∀ e, color (supplySrc e) = color (supplyDst e)) :
    ∀ i j, color i = color j := by
  have hAC : color 0 = color 2 := onEdge 0
  have hBC : color 1 = color 2 := onEdge 1
  have hCM : color 2 = color 4 := onEdge 4
  have hCN : color 2 = color 5 := onEdge 5
  have hDM : color 3 = color 4 := onEdge 6
  have center (i : Fin 6) : color i = color 2 := by
    fin_cases i
    · exact hAC
    · exact hBC
    · rfl
    · exact hDM.trans hCM.symm
    · exact hCM.symm
    · exact hCN.symm
  exact fun i j => (center i).trans (center j).symm

/-- If all eight supply distances are at most M, the sum of the two demand
distances is at most 95 M / 24. -/
theorem demand_bound {k : Type*} [Field k] (f : SpectralPoint k (Fin 6)) {M : ℝ}
    (hM : 0 < M) (bound : ∀ i, f.wireDistance (supplySrc i) (supplyDst i) ≤ M) :
    f.wireDistance 0 1 + f.wireDistance 2 3 ≤ (95/24 : ℝ)*M := by
  let d := f.wireDistance
  have box (i : Fin 8) : (d (supplySrc i) (supplyDst i))^2 ≤ M^2 :=
    (sq_le_sq₀ (f.wireDistance_nonneg _ _) hM.le).mpr (bound i)
  have e0 : d 0 2^2 ≤ M^2 := box 0
  have e1 : d 1 2^2 ≤ M^2 := box 1
  have e2 : d 0 4^2 ≤ M^2 := box 2
  have e3 : d 1 5^2 ≤ M^2 := box 3
  have e4 : d 2 4^2 ≤ M^2 := box 4
  have e5 : d 2 5^2 ≤ M^2 := box 5
  have e6 : d 3 4^2 ≤ M^2 := box 6
  have e7 : d 3 5^2 ≤ M^2 := box 7
  have energy : (1/3 : ℝ)*(d 0 1)^2 + (d 2 3)^2 ≤ (31/6 : ℝ)*M^2 := by
    have h := f.sixParty_wire_energy 0 1 2 3 4 5
    change (1/3 : ℝ)*(d 0 1)^2 + (d 2 3)^2 ≤ _ at h
    linarith only [h,e0,e1,e2,e3,e4,e5,e6,e7]
  have A : d 0 1 ≤ 2*M := by
    have left : d 0 2 ≤ M := bound 0
    have right : d 2 1 ≤ M := (f.wireDistance_comm 2 1).le.trans (bound 1)
    exact (f.wireDistance_triangle 0 2 1).trans (by linarith)
  change d 0 1 + d 2 3 ≤ _
  by_contra! bad
  have hpos := mul_pos hM (sub_pos.mpr bad)
  nlinarith only [hpos,energy,sq_nonneg (2*M-d 0 1),sq_nonneg (2*M-d 2 3),
    mul_nonneg hM.le (sub_nonneg.mpr A)]

/-- One of the eight single-edge profiles strictly beats the demand at each
spectral point. The selected profile may depend on that point. -/
theorem max_distance {k : Type*} [Field k] (f : SpectralPoint k (Fin 6)) :
    ∃ i, 0 < f.wireDistance (supplySrc i) (supplyDst i) ∧
      48 * (f.wireDistance 0 1 + f.wireDistance 2 3) <
        191*f.wireDistance (supplySrc i) (supplyDst i) := by
  let d i := f.wireDistance (supplySrc i) (supplyDst i)
  obtain ⟨i,_,hm⟩ := Finset.univ.exists_max_image d Finset.univ_nonempty
  have high (j : Fin 8) : d j ≤ d i := hm _ (Finset.mem_univ _)
  obtain ⟨j,hj⟩ := f.exists_pos_connected_wireDistance supplySrc supplyDst connected
  have hi : 0 < d i := hj.trans_le (high j)
  exact ⟨i,hi,by linarith only [demand_bound f hi high,hi]⟩

def oneEdge (t : ℕ) (i e : Fin 8) := if e=i then 191*t else 0

theorem strict_profile {k : Type*} [Field k] {t : ℕ} (ht : 0 < t) :
    StrictAtSpectrum k demandSrc demandDst supplySrc supplyDst (fun _ => 48*t) (oneEdge t) := by
  intro f
  obtain ⟨i,_,cheap⟩ := max_distance f
  refine ⟨i,?_⟩
  simp only [Fin.sum_univ_two,demandSrc,demandDst,Matrix.cons_val_zero,Matrix.cons_val_one,
    oneEdge,Nat.cast_ite,Nat.cast_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [mul_lt_mul_of_pos_right cheap (Nat.cast_pos.mpr ht)]

theorem seed_payload (t : ℕ) {h : ℕ} (σ : Fin h → Fin 8) :
    ∑ e, payload (oneEdge t) σ e = 191*t*h := by
  unfold payload
  rw [Finset.sum_comm]
  simp [oneEdge,Nat.mul_comm]

/-- The actual selector (a copy and an ordered word of eights) fits in the
announced fixed-width bit field. -/
def seed_encoding (K h : ℕ) : (Fin K × (Fin h → Fin 8)) ↪ Fin (2^MotifWidths.selectorBits K 8 h) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa using MotifWidths.selector_capacity K 8 h))

/- The comparison is stated at the level of restriction classes so the same
witness is available both to the powered descent and to the ordinary local
matrix identity. The spectral-comparison step follows MotifBase. -/
section Comparison
variable {k J : Type*} [Field k] [Fintype J] [Nontrivial J]
  {D S : Type} [Fintype D] [Fintype S] {W : Type*} [Fintype W]
private theorem copyBound (a b : D → J) (c d : S → J) (z : D → ℕ) (w : W → S → ℕ)
    (hs : StrictAtSpectrum k a b c d z w) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ h : ℕ,
      binaryNetworkClass (k := k) a b z ^ h ≤
        (K : RestrictionClass k J) * (∑ i, binaryNetworkClass c d (w i)) ^ h := by
  classical
  let a₀ := Classical.choice (inferInstance : Nonempty J)
  let rank := flatteningRankHom (k := k) a₀
  let : CharZero (RestrictionClass k J) := rank.charZero
  let X := binaryNetworkClass (k := k) a b z
  let Y : RestrictionClass k J := ∑ i, binaryNetworkClass c d (w i)
  have comp (f : RestrictionClass k J →+* ℝ) (hf : Monotone f) : f X < f Y := by
    let F := toSpectralPoint f hf
    obtain ⟨i, hi⟩ := hs F
    have h₁ : f X < f (binaryNetworkClass c d (w i)) := by
      change (F.value (binaryWires a b z) : ℝ) < (F.value (binaryWires c d (w i)) : ℝ)
      rw [F.value_binary_wireNetwork, F.value_binary_wireNetwork]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hi
    change _ < f (∑ j, binaryNetworkClass c d (w j))
    rw [map_sum]
    exact h₁.trans_le (Finset.single_le_sum
      (fun j _ ↦ by simpa using hf (orderBounds.zero_le (binaryNetworkClass c d (w j))))
      (Finset.mem_univ i))
  have hy : Y ≠ 0 := by
    intro hY
    let F := flatteningPoint (k := k) a₀
    have hm := ofSpectralPoint_monotone F
    have hx := comp (ofSpectralPoint F) hm
    rw [hY, map_zero] at hx
    exact hx.not_ge (by simpa using hm (orderBounds.zero_le X))
  exact Spectral.strict_spectral_comparison orderBounds rank (flatteningRankHom_monotone a₀) hy comp

end Comparison

private theorem classProfile {F : Type*} [Field F] {t K h : ℕ}
    (bound : binaryNetworkClass (k := F) demandSrc demandDst (fun _ => 48*t) ^ h ≤
      (K : RestrictionClass F (Fin 6)) *
        (∑ i, binaryNetworkClass supplySrc supplyDst (oneEdge t i))^h) :
    binaryNetworkClass (k := F) demandSrc demandDst (fun _ => h*(48*t)) ≤
      ∑ σ : Fin K × (Fin h → Fin 8), binaryNetworkClass supplySrc supplyDst (payload (oneEdge t) σ.2) := by
  rw [binaryNetworkClass_pow]
  have term (σ : Fin K × (Fin h → Fin 8)) :
      binaryNetworkClass (k := F) supplySrc supplyDst (payload (oneEdge t) σ.2) =
        ∏ j, binaryNetworkClass supplySrc supplyDst (oneEdge t (σ.2 j)) :=
    binaryNetworkClass_sum supplySrc supplyDst Finset.univ _
  simp_rw [term]
  simpa only [Fintype.sum_pow,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using bound

private theorem choose_scale (F : Type*) [Field F] :
    ∃ t h K : ℕ, 0 < t ∧ 0 < h ∧ 1 ≤ K ∧
      191*t*h + 8 + 8*MotifWidths.selectorBits K 8 h < 4*(h*(48*t)) ∧
      binaryNetworkClass (k := F) demandSrc demandDst (fun _ => h*(48*t)) ≤
        ∑ σ : Fin K × (Fin h → Fin 8), binaryNetworkClass supplySrc supplyDst (payload (oneEdge t) σ.2) := by
  let m (i : ℕ) := 16*(i+1)
  have pos (i : ℕ) : 0 < m i := Nat.mul_pos (by decide) (Nat.succ_pos i)
  choose K good valid using fun i : ℕ =>
    copyBound demandSrc demandDst supplySrc supplyDst (fun _ => 48*m i) (oneEdge (m i))
      (strict_profile (k := F) (pos i))
  obtain ⟨i,h,hi,hh,rate⟩ := MotifWidths.exists_selector_block 1 8 (by decide) K
    (show (0:ℝ) < 1 by norm_num)
  have den : (0 : ℝ) < (h:ℝ)*((i:ℝ)*1) := by positivity
  simp only [Nat.cast_one,mul_one] at rate den
  have rate' := (div_lt_iff₀ den).mp rate
  have tinyReal : (MotifWidths.selectorBits (K i) 8 h : ℝ) < ((h*i : ℕ) : ℝ) := by
    simpa only [one_mul,mul_one,Nat.cast_mul] using rate'
  have tiny : MotifWidths.selectorBits (K i) 8 h < h*i := by exact_mod_cast tinyReal
  refine ⟨m i,h,K i,pos i,hh,good i,?_,classProfile (valid i h)⟩
  dsimp only [m]
  nlinarith only [tiny,hh,hi,Nat.zero_le (h*i)]

/-- Genuine ordinary coefficient tensors over the given field, with room
for rounding eight supply widths and broadcasting the selector. -/
theorem exists_seed (F : Type*) [Field F] :
    ∃ t h K : ℕ, 0 < t ∧ 0 < h ∧ 1 ≤ K ∧
      BaseIdentity F demandSrc demandDst supplySrc supplyDst (fun _ => 48*t) (oneEdge t) K h ∧
      191*t*h + 8 + 8*MotifWidths.selectorBits K 8 h < 4*(h*(48*t)) := by
  obtain ⟨t,h,K,ht,hh,hK,paid,bound⟩ := choose_scale F
  exact ⟨t,h,K,ht,hh,hK,ordinary_sum_of_class_le _ _ bound,paid⟩

/-- Restriction-class seed consumed by the subsequent powering and grouping
of the ordinary coefficient identities. -/
theorem exists_class_seed (F : Type*) [Field F] :
    ∃ b k C : ℕ, C+8+8*k < 4*b ∧
      ∃ (H : Type) (fh : Fintype H) (w : H → Fin 8 → ℕ),
        letI := fh
        Fintype.card H ≤ 2^k ∧ (∀ σ, (∑ e, w σ e) ≤ C) ∧
          binaryNetworkClass (k := F) demandSrc demandDst (fun _ => b) ≤
            ∑ σ, binaryNetworkClass supplySrc supplyDst (w σ) := by
  obtain ⟨t,h,K,_,_,_,paid,bound⟩ := choose_scale F
  refine ⟨h*(48*t),MotifWidths.selectorBits K 8 h,191*t*h,paid,
    Fin K × (Fin h → Fin 8),inferInstance,fun σ => payload (oneEdge t) σ.2,?_,?_,bound⟩
  · simpa using MotifWidths.selector_capacity K 8 h
  · exact fun σ => (seed_payload t σ.2).le


end Hierarchy.DescentSixParty
end

end OAI
