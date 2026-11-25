import OAI.Combinatorics.Sunflower.Fourier
import OAI.Combinatorics.Sunflower.BroadcastCode
import OAI.Combinatorics.Sunflower.BroadcastParameters
import OAI.Combinatorics.Sunflower.Rigidity
import OAI.Combinatorics.Sunflower.Prices
import OAI.Combinatorics.Sunflower.Control

/-! # Controlled broadcasting by character orthogonality -/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

noncomputable section

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

/-- A restriction controlled at its source sites that reproduces the common
source label at the target sites while returning a fixed resource. -/
def Broadcasts (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
  ∃ M : Control.Map (fun _ : I => A) R.Leg (fun i => Q.Leg i × MaskLeg T A i),
    ∀ (a : A) (c : I → A), (∀ i ∈ P, c i = a) →
      ∀ y, Control.eval M c R.coeff y = Q.coeff (fun i => (y i).1) *
        (if (fun i => (y i).2) = (fun _ _ => a) then 1 else 0)

/-- The distinguished source contributes both the control and the reference
source index. Other source indices enter with negative sign. -/
private def phase {Γ : Type} [AddCommGroup Γ] (P T : Finset I) (s : I)
    (H : A → Γ) (V : A → A → Γ) (i : I) (c : A)
    (y : MaskLeg P A i × MaskLeg T A i) : Γ :=
  if hp : i ∈ P then
    if i = s then (P.erase s).card • V c (y.1 hp) - T.card • H c
    else -V c (y.1 hp)
  else if ht : i ∈ T then H (y.2 ht) else 0

omit [Fintype I] [Fintype A] in
private theorem sum_phase {Γ : Type} [AddCommGroup Γ] (P T : Finset I)
    (hPT : Disjoint P T) (s : I) (hs : s ∈ P)
    (H : A → Γ) (V : A → A → Γ) (a : A) (c : I → A)
    (hc : ∀ i ∈ P, c i = a) (y : ∀ i, MaskLeg P A i × MaskLeg T A i) :
    (∑ i ∈ P ∪ T, phase P T s H V i (c i) (y i)) = 0 ↔
      (∑ z : T, H ((y z).2 z.property)) + (P.erase s).card • V a ((y s).1 hs) =
        T.card • H a + ∑ j : P.erase s, V a ((y j).1 (Finset.mem_of_mem_erase j.property)) := by
  classical
  let f (i : I) := phase P T s H V i (c i) (y i)
  have hex : (∑ i ∈ P.erase s, f i) =
      -(∑ j : P.erase s, V a ((y j).1 (Finset.mem_of_mem_erase j.property))) := by
    rw [← Finset.sum_coe_sort, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h := Finset.mem_erase.mp j.property
    simp [f, phase, h.1, h.2, hc j h.2]
  have htar : (∑ i ∈ T, f i) = ∑ z : T, H ((y z).2 z.property) := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro z _
    have hz : (z : I) ∉ P := fun hp => Finset.disjoint_left.mp hPT hp z.property
    simp [f, phase, hz, z.property]
  have hsrc : f s = (P.erase s).card • V a ((y s).1 hs) - T.card • H a := by
    simp [f, phase, hs, hc s hs]
  change (∑ i ∈ P ∪ T, f i) = 0 ↔ _
  rw [Finset.sum_union hPT, ← Finset.sum_erase_add P f hs, hex, hsrc, htar]
  constructor
  · intro h
    apply sub_eq_zero.mp
    convert h using 1; abel
  · intro h
    convert sub_eq_zero.mpr h using 1; abel

omit [Fintype I] [Fintype A] in
private theorem zero_sum_agrees {m q N L : ℕ} (d : BroadcastCode m q N) (e : A ≃ Fin N)
    (P T : Finset I) (hPT : Disjoint P T) (s : I) (hs : s ∈ P)
    (hL : (T.card + (P.erase s).card) * (q-1) < L)
    (a : A) (c : I → A) (hc : ∀ i ∈ P, c i = a)
    (y : ∀ i, MaskLeg P A i × MaskLeg T A i) :
    (∑ i ∈ P ∪ T, phase P T s
      (fun x j => ((d.H (e x) j : ℕ) : ZMod L))
      (fun x t j => ((d.V (e x) (e t) j : ℕ) : ZMod L)) i (c i) (y i)) = 0 ↔
      (∀ i (hi : i ∈ P), (y i).1 hi = (y s).1 hs) ∧
      ((fun i => (y i).2) = (fun _ _ => a)) := by
  classical
  rw [sum_phase P T hPT s hs _ _ a c hc]
  let h (x : A) (i : Fin m) : ℕ := d.H (e x) i
  let v (x : A) (i : Fin m) : ℕ := d.V (e a) (e x) i
  let idx (j : P.erase s) := (y j).1 (Finset.mem_of_mem_erase j.property)
  let tar (z : T) := (y z).2 z.property
  let t₀ := (y s).1 hs
  have hinj : Function.Injective h := by
    intro x z he
    exact e.injective (d.H.injective (funext fun i => Fin.ext (congrFun he i)))
  have vinj : Function.Injective v := by
    intro x z he
    exact e.injective ((d.V (e a)).injective (funext fun i => Fin.ext (congrFun he i)))
  have hb (x : Fin q) : x.val ≤ q - 1 := by have := x.isLt; omega
  have rel := broadcast_mod_relation_iff (D := Fin m) (Z := T) (J := P.erase s)
    (q := q) (L := L) (by simpa using hL) (h a) (v t₀)
    (fun z => h (tar z)) (fun j => v (idx j))
    (fun i => hb _) (fun i => hb _) (fun z i => hb _) (fun j i => hb _)
    (fun z => d.H_norm _ _) (fun j => d.V_norm _ _ _) (fun j => d.dot_eq _ _ _)
  simp only [Fintype.card_coe] at rel
  refine rel.trans ?_
  constructor
  · rintro ⟨ht,hp⟩
    constructor
    · intro i hi
      by_cases hsame : i = s
      · subst i; rfl
      · exact vinj (hp ⟨i, Finset.mem_erase.mpr ⟨hsame, hi⟩⟩)
    · funext i hi
      exact hinj (ht ⟨i, hi⟩)
  · rintro ⟨hp, ht⟩
    exact ⟨fun z => congrArg h (congrFun (congrFun ht z) z.property),
      fun j => congrArg v (hp j (Finset.mem_of_mem_erase j.property))⟩

private theorem broadcasts_code {m q N L : ℕ} [NeZero L]
    (d : BroadcastCode m q N) (e : A ≃ Fin N) (P T : Finset I) (hPT : Disjoint P T)
    (s : I) (hs : s ∈ P) (hL : (T.card + (P.erase s).card) * (q-1) < L) :
    Broadcasts P T A (Raw.maskDiagonal ℂ (P ∪ T) (AddChar (Fin m → ZMod L) ℂ))
      (Raw.maskDiagonal ℂ P A) := by
  classical
  let H (x : A) (j : Fin m) : ZMod L := (d.H (e x) j : ℕ)
  let V (x t : A) (j : Fin m) : ZMod L := (d.V (e x) (e t) j : ℕ)
  refine ⟨fourierMatrix (P ∪ T) s (phase P T s H V), ?_⟩
  intro a c hc y
  change ∀ i, MaskLeg P A i × MaskLeg T A i at y
  refine (eval_fourierMatrix (P ∪ T) s (phase P T s H V) c y).trans ?_
  rw [Raw.maskDiagonal_coeff_at (K := ℂ) P hs (fun i => (y i).1)]
  have hz : (∑ i ∈ P ∪ T, phase P T s H V i (c i) (y i)) = 0 ↔ _ :=
    zero_sum_agrees d e P T hPT s hs hL a c hc y
  rw [hz]
  split_ifs <;> simp_all

/-- The alphabet-independent additive cost paid for a chosen broadcast slope. -/
def broadcastOverhead (sites h : ℕ) : ℝ :=
  (BroadcastParameters.dim h : ℝ) * ((BroadcastParameters.dim h : ℝ) + 2 + sites)

/-- On a shared control, broadcast its label to every target and recover a
fixed tensor at the sources. Increasing the fixed parameter h makes the excess
slope arbitrarily small, uniformly in b. -/
theorem exists_broadcast [Nonempty I] [Nonempty A]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hP : P.Nonempty) (_hT : T.Nonempty) (hPT : Disjoint P T)
    {h : ℕ} (hh : 0 < h) (b : ℕ) (hA : Fintype.card A = 2^b) :
    ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ Broadcasts P T A R Q ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤
        (maskDiagonalPrice φ 1 (P ∪ T) - maskDiagonalPrice φ 1 P + 6/(h:ℝ)) * b +
          broadcastOverhead (Fintype.card I) h := by
  classical
  obtain ⟨s, hs⟩ := hP
  let sites := Fintype.card I
  let L := BroadcastParameters.modulus h b sites
  let m := BroadcastParameters.dim h
  let q := BroadcastParameters.side h b
  let : NeZero L := ⟨(BroadcastParameters.modulus_pos _ _ _).ne'⟩
  obtain ⟨code⟩ := BroadcastCode.nonempty_of_card (BroadcastParameters.code_capacity hh b)
  let e : A ≃ Fin (2^b) := Fintype.equivOfCardEq (by simpa using hA)
  have hcard : T.card + (P.erase s).card ≤ sites := by
    have hle := (P ∪ T).card_le_univ
    rw [Finset.card_union_of_disjoint hPT] at hle
    have he := Finset.card_erase_le (s := P) (a := s)
    omega
  have hn : (T.card + (P.erase s).card) * (q-1) < L :=
    (Nat.mul_le_mul_right _ hcard).trans_lt (BroadcastParameters.no_wrap h b sites)
  let D := AddChar (Fin m → ZMod L) ℂ
  have hk : (P ∪ T).Nonempty := ⟨s, Finset.mem_union_left _ hs⟩
  refine ⟨Raw.maskDiagonal ℂ (P ∪ T) D, Raw.maskDiagonal ℂ P A,
    Raw.maskDiagonal_ne_zero _ hk _, Raw.maskDiagonal_ne_zero _ ⟨s,hs⟩ _,
    broadcasts_code code e P T hPT s hs hn, ?_⟩
  have dcard : Fintype.card D = 2 ^ BroadcastParameters.bits h b sites := by
    simp [D, AddChar.card_eq, ZMod.card, L, m, BroadcastParameters.modulus_pow_dim]
  rw [rawLogPrice_maskDiagonal_card φ 1 _ hk D,
    rawLogPrice_maskDiagonal_card φ 1 _ ⟨s, hs⟩ A, dcard, hA]
  push_cast
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2:ℝ)), mul_one]
  have wpos := maskDiagonalPrice_nonneg φ (by norm_num : 0 ≤ (1:ℝ)) (P ∪ T)
  have wle := maskDiagonalPrice_le_one φ (P ∪ T)
  have hbits := BroadcastParameters.bits_le hh b sites
  change _ ≤ _ + broadcastOverhead sites h
  have costnn : 0 ≤ broadcastOverhead sites h := by unfold broadcastOverhead; positivity
  have hover : 0 ≤ 6 / (h : ℝ) * (b : ℝ) + broadcastOverhead sites h := by positivity
  have hu := mul_le_mul_of_nonneg_left hbits wpos
  have hv := mul_le_mul_of_nonneg_right wle hover
  unfold broadcastOverhead at *
  linarith only [hu, hv]

end
end Sunflower
end Combinatorics
end OAI
