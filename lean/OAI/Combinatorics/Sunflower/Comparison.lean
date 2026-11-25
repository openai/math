import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.Combinatorics.Sunflower.Control
import OAI.Combinatorics.Sunflower.Tensor
import OAI.Combinatorics.Sunflower.Rules
import Mathlib.Basic.Complex.Basic

/-! # Comparing a word family with the full diagonal

The input word indices agree inside each group of sites. Keeping these
indices while applying the local tests leaves exactly the full diagonal.
-/

noncomputable section
open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Comparison

variable {S G : Type*} [Fintype S]

/-- The sites labeled by one group. -/
def fiber (group : S → G) (j : G) : Finset S :=
  Finset.univ.filter fun s => group s = j

@[simp] theorem mem_fiber {group : S → G} {j : G} {s : S} :
    s ∈ fiber group j ↔ group s = j := by simp [fiber]

theorem fiber_nonempty {group : S → G} (h : Function.Surjective group) (j : G) :
    (fiber group j).Nonempty := by
  obtain ⟨s, hs⟩ := h j
  exact ⟨s, mem_fiber.mpr hs⟩

/-- Coefficient predicate for independent word indices on the selected groups. -/
def Compatible (group : S → G) (J : Finset G) {L : Type*} (x : S → L) : Prop :=
  ∀ s t, group s ∈ J → group s = group t → x s = x t

def groupTensor (group : S → G) (J : Finset G) (L : Type) [Fintype L] : Raw.{0} S ℂ :=
  ⟨fun _ => L, fun _ => inferInstance, fun x => if Compatible group J x then 1 else 0⟩

omit [Fintype S] in
theorem groupTensor_ne_zero (group : S → G) (J : Finset G)
    (L : Type) [Fintype L] [Nonempty L] : (groupTensor group J L).coeff ≠ 0 := by
  classical
  let l : L := Classical.choice inferInstance
  intro h
  have H := congrFun h (fun _ => l)
  change (if Compatible group J (fun _ => l) then (1 : ℂ) else 0) = 0 at H
  simp [Compatible] at H

theorem groupTensor_insert_restricts_mul [DecidableEq S] [DecidableEq G]
    (group : S → G) (hsur : Function.Surjective group) (j : G) (J : Finset G)
    (L : Type) [Fintype L] :
    (groupTensor group (insert j J) L).Restricts
      ((groupTensor group J L).mul (Raw.maskDiagonal ℂ (fiber group j) L)) := by
  classical
  obtain ⟨s₀, hs₀⟩ := fiber_nonempty hsur j
  apply Raw.restrict_by_read (fun s x => (x, fun _ => x))
  intro (x : S → L)
  change (if Compatible group (insert j J) x then (1 : ℂ) else 0) =
    (if Compatible group J x then 1 else 0) *
      (Raw.maskDiagonal ℂ (fiber group j) L).coeff (fun s _ => x s)
  rw [Raw.maskDiagonal_coeff_at (K := ℂ) (α := L) _ hs₀ (fun s _ => x s)]
  have hh : Compatible group (insert j J) x ↔ Compatible group J x ∧
      ∀ s, s ∈ fiber group j → x s = x s₀ := by
    constructor
    · intro H
      exact ⟨fun s t hs hst => H s t (Finset.mem_insert_of_mem hs) hst,
        fun s hs => H s s₀ (by simp [mem_fiber.mp hs])
          ((mem_fiber.mp hs).trans (mem_fiber.mp hs₀).symm)⟩
    · rintro ⟨H, Hj⟩ s t hs hst
      rcases Finset.mem_insert.mp hs with he | he
      · exact (Hj s (mem_fiber.mpr he)).trans (Hj t (mem_fiber.mpr (hst.symm.trans he))).symm
      · exact H s t he hst
  split_ifs <;> simp_all

theorem groupTensor_price_le [DecidableEq S] [Nonempty S] [DecidableEq G]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))
    (group : S → G) (hsur : Function.Surjective group) (J : Finset G)
    (L : Type) [Fintype L] [Nonempty L] :
    rawLogPrice φ 1 (groupTensor group J L) ≤
      ∑ j ∈ J, rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) L) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have h : (groupTensor group ∅ L).Restricts (Raw.one S ℂ) := by
      apply Raw.restrict_by_read (fun _ _ => PUnit.unit)
      intro x
      simp [groupTensor, Compatible, Raw.one]
    simpa [rawLogPrice, ofRaw_one, φ.property.2.1] using
      rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1) h
  | @insert j J hj ih =>
    have h := rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1)
      (groupTensor_insert_restricts_mul group hsur j J L)
    rw [rawLogPrice_mul φ 1 _ _ (groupTensor_ne_zero _ _ _)
      (Raw.maskDiagonal_ne_zero _ (fiber_nonempty hsur j) L)] at h
    rw [Finset.sum_insert hj, add_comm]
    exact h.trans (add_le_add_left ih _)


/-- A fixed resource and return tensor with a local matrix for every control value. -/
structure Device (S C : Type*) where
  R : Raw.{0} S ℂ
  Q : Raw.{0} S ℂ
  R_ne : R.coeff ≠ 0
  Q_ne : Q.coeff ≠ 0
  M : ∀ s, C → Q.Leg s → R.Leg s → ℂ

variable {C : Type*}

def Device.out (D : Device S C) (c : S → C) : (∀ s, D.Q.Leg s) → ℂ :=
  contract (fun s => D.M s (c s)) D.R.coeff

variable [Nonempty S]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))

def Device.cost (D : Device S C) : ℝ := rawLogPrice φ 1 D.R - rawLogPrice φ 1 D.Q

omit [Fintype S] [Nonempty S] in
private theorem raw_mul_nonzero (X Y : Raw.{0} S ℂ)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hY
  exact Function.ne_iff.mpr ⟨fun i => (a i, b i), mul_ne_zero ha hb⟩

def Device.parallel (D E : Device S C) : Device S C where
  R := D.R.mul E.R
  Q := D.Q.mul E.Q
  R_ne := raw_mul_nonzero _ _ D.R_ne E.R_ne
  Q_ne := raw_mul_nonzero _ _ D.Q_ne E.Q_ne
  M s c b a := D.M s c b.1 a.1 * E.M s c b.2 a.2

omit [Nonempty S] in
theorem Device.out_parallel (D E : Device S C) (c : S → C)
    (b : ∀ s, D.Q.Leg s × E.Q.Leg s) :
    (D.parallel E).out c b = D.out c (fun s => (b s).1) * E.out c (fun s => (b s).2) :=
  contract_mul _ _ _ _ _

theorem Device.cost_parallel (D E : Device S C) :
    (D.parallel E).cost φ = D.cost φ + E.cost φ := by
  unfold Device.cost
  change rawLogPrice _ _ (D.R.mul E.R) - rawLogPrice _ _ (D.Q.mul E.Q) = _
  rw [rawLogPrice_mul _ _ _ _ D.R_ne E.R_ne, rawLogPrice_mul _ _ _ _ D.Q_ne E.Q_ne]
  ring

def Device.unit (S C : Type*) : Device S C where
  R := Raw.one S ℂ
  Q := Raw.one S ℂ
  R_ne := fun h => one_ne_zero (congrFun h (fun _ => PUnit.unit))
  Q_ne := fun h => one_ne_zero (congrFun h (fun _ => PUnit.unit))
  M _ _ _ _ := 1

omit [Nonempty S] in
theorem Device.out_unit (c : S → C) : (Device.unit S C).out c = (Raw.one S ℂ).coeff := by
  funext b
  change (∑ _ : S → PUnit, (1 : ℂ) * ∏ _ : S, (1 : ℂ)) = 1
  simp

/-- Parallel execution of the tests preserves the return tensor on all good
controls. A single failed test annihilates the entire output. -/
theorem parallel_tests {J : Type*} (ids : Finset J)
    (D : J → Device S C) (good : (S → C) → Prop) (bad : J → (S → C) → Prop)
    (hgood : ∀ j ∈ ids, ∀ c, good c → (D j).out c = (D j).Q.coeff)
    (hbad : ∀ j ∈ ids, ∀ c, bad j c → (D j).out c = 0) :
    ∃ T : Device S C, T.cost φ = ∑ j ∈ ids, (D j).cost φ ∧
      (∀ c, good c → T.out c = T.Q.coeff) ∧
      ∀ j ∈ ids, ∀ c, bad j c → T.out c = 0 := by
  classical
  induction ids using Finset.induction_on with
  | empty =>
    exact ⟨Device.unit S C, by simp [Device.cost, Device.unit],
      fun c _ => Device.out_unit c, by simp⟩
  | @insert j ids hj ih =>
    obtain ⟨T, hcost, hpres, hkill⟩ := ih
      (fun k hk => hgood k (Finset.mem_insert_of_mem hk))
      (fun k hk => hbad k (Finset.mem_insert_of_mem hk))
    refine ⟨(D j).parallel T, by rw [Device.cost_parallel, hcost, Finset.sum_insert hj], ?_, ?_⟩
    · intro c hc
      funext b
      rw [Device.out_parallel (D j) T c b, hgood j (Finset.mem_insert_self ..) c hc, hpres c hc]
      rfl
    · intro k hk c hc
      funext b
      rw [Device.out_parallel (D j) T c b]
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [hbad k (Finset.mem_insert_self ..) c hc]
        simp
      · rw [hkill k hk c hc]
        simp

omit [Fintype S] in
private theorem diagonal_coeff (L : Type) [Fintype L] (x : S → L) :
    (Raw.diagonal S ℂ L).coeff x = if IsConstant x then 1 else 0 := by
  classical
  let s : S := Classical.choice inferInstance
  simp only [Raw.diagonal]
  rw [Finset.sum_eq_single (x s)]
  · have he : x = (fun _ => x s) ↔ IsConstant x :=
      ⟨fun h i j => (congrFun h i).trans (congrFun h j).symm, fun h => funext fun i => h i s⟩
    simp [he]
  · intro b _ hbs
    exact ite_eq_right (fun h => (hbs (congrFun h s).symm).elim)
  · simp

/-- The retained word indices give an ordinary local restriction. A coefficient
of the input already vanishes if its indices disagree within a group. On all
remaining nonconstant indices at least one local test gives zero. -/
theorem diagonal_restricts_filtered [Fintype G] (group : S → G)
    {L : Type} [Fintype L] (D : Device S L)
    (hpres : ∀ c, IsConstant c → D.out c = D.Q.coeff)
    (hkill : ∀ c, Compatible group Finset.univ c → ¬ IsConstant c → D.out c = 0) :
    ((Raw.diagonal S ℂ L).mul D.Q).Restricts ((groupTensor group Finset.univ L).mul D.R) := by
  classical
  let N : Control.Map (fun _ : S => Unit × L) D.R.Leg D.Q.Leg := fun i p => D.M i p.2
  refine ⟨fun s => Control.retainMap N s (), ?_⟩
  intro (y : ∀ s, L × D.Q.Leg s)
  let c : S → L := fun s => (y s).1
  let b : ∀ s, D.Q.Leg s := fun s => (y s).2
  change (Raw.diagonal S ℂ L).coeff c * D.Q.coeff b =
    Control.eval (Control.retainMap N) (fun _ => ())
      ((groupTensor group Finset.univ L).mul D.R).coeff y
  rw [Control.eval_retainMap N (fun _ => ()) ((groupTensor group Finset.univ L).mul D.R).coeff y]
  change _ = ∑ a, ((if Compatible group Finset.univ c then (1 : ℂ) else 0) * D.R.coeff a) *
    ∏ s, D.M s (c s) (b s) (a s)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change _ = (if Compatible group Finset.univ c then (1 : ℂ) else 0) * D.out c b
  rw [diagonal_coeff]
  by_cases he : IsConstant c
  · have hm : Compatible group Finset.univ c := fun s t _ _ => he s t
    simp [he, hm, hpres c he]
  · by_cases hm : Compatible group Finset.univ c
    · simp [he, hm, hkill c hm he]
    · simp [he, hm]

/-- Monotonicity of the spectral point applied to the restriction, followed by
the log-price laws for word labels and independent resources. -/
theorem diagonal_price_bound [Fintype G] [DecidableEq S] [DecidableEq G]
    (group : S → G) (hsur : Function.Surjective group)
    {L : Type} [Fintype L] [Nonempty L] (D : Device S L)
    (hpres : ∀ c, IsConstant c → D.out c = D.Q.coeff)
    (hkill : ∀ c, Compatible group Finset.univ c → ¬ IsConstant c → D.out c = 0) :
    (1 - ∑ j, maskDiagonalPrice φ 1 (fiber group j)) * Real.logb 2 (Fintype.card L) ≤
      D.cost φ := by
  classical
  have h := rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1)
    (diagonal_restricts_filtered group D hpres hkill)
  have dne : (Raw.diagonal S ℂ L).coeff ≠ 0 := by
    let l : L := Classical.choice inferInstance
    intro hz
    have H := congrFun hz (fun _ => l)
    change (Raw.diagonal S ℂ L).coeff (fun _ => l) = 0 at H
    rw [diagonal_coeff] at H
    simp [IsConstant] at H
  rw [rawLogPrice_mul φ 1 _ _ dne D.Q_ne, rawLogPrice_mul φ 1 _ _
    (groupTensor_ne_zero group Finset.univ L) D.R_ne] at h
  have hdf : rawLogPrice φ 1 (Raw.diagonal S ℂ L) = Real.logb 2 (Fintype.card L) := by
    have hv := map_natCast (normalizedSpectrum.toRingHom φ) (Fintype.card L)
    change φ.val (Fintype.card L : TensorClass.{0} S ℂ) = (Fintype.card L : NNReal) at hv
    simp [rawLogPrice, ofRaw_diagonal_eq_natCast, hv]
  rw [hdf] at h
  have hm := groupTensor_price_le φ group hsur Finset.univ L
  have price (j : G) : rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) L) =
      maskDiagonalPrice φ 1 (fiber group j) * Real.logb 2 (Fintype.card L) := by
    have hh := ofRaw_maskDiagonal_equiv (K := ℂ) (fiber group j) (fiber_nonempty hsur j)
      (Fintype.equivFin L)
    calc
      _ = rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) (Fin (Fintype.card L))) :=
        congrArg (fun x => (1 : ℝ) * Real.logb 2 (φ.val x : ℝ)) hh
      _ = _ := rawLogPrice_maskDiagonal φ 1 _ (fiber_nonempty hsur j) Fintype.card_pos
  simp_rw [price] at hm
  rw [← Finset.sum_mul] at hm
  unfold Device.cost
  linarith


/-- Read a specified function of the local word index as the control. -/
def Device.pre {B : Type*} (D : Device S C) (f : B → C) : Device S B where
  R := D.R
  Q := D.Q
  R_ne := D.R_ne
  Q_ne := D.Q_ne
  M s b := D.M s (f b)

/-- Proposition 2.1 for the two-anchor forcing rules. One fixed device for
each rule is used once at each coordinate. The index type for the diagonal
is small even when the coordinate alphabet lies in a higher universe. -/
theorem wordComparison [DecidableEq S] {r k : ℕ} {α : Type*}
    (group : S → Fin r) (hsur : Function.Surjective group)
    (A B : Fin r) (hAB : A ≠ B) (W : Finset (Fin k → α))
    (hW : W.Nonempty) (hfree : WordFree r W) (cost : Rule (Fin r) → ℝ)
    (tests : ∀ q ∈ anchorRules A B, ∃ D : Device S α, D.cost φ ≤ cost q ∧
      (∀ x, D.out (fun _ => x) = D.Q.coeff) ∧
      ∀ f : Fin r → α, ¬ q.Holds f → D.out (f ∘ group) = 0) :
    (1 - ∑ j, maskDiagonalPrice φ 1 (fiber group j)) * Real.logb 2 W.card ≤
      (k : ℝ) * ∑ q ∈ anchorRules A B, cost q := by
  classical
  let Q := ↥(anchorRules A B)
  let L := Fin W.card
  let : Nonempty L := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hW)
  let e : L ≃ W := W.equivFin.symm
  let word (i : L) : Fin k → α := (e i).val
  have inj : Function.Injective word := Subtype.val_injective.comp e.injective
  have hw (i : L) : word i ∈ W := (e i).property
  choose D hcost hpres hkill using fun q : Q => tests q.val q.property
  let test (z : Fin k × Q) : Device S L := (D z.2).pre (fun a => word a z.1)
  let bad (z : Fin k × Q) (c : S → L) := ∃ v : Fin r → L,
      c = v ∘ group ∧ ¬ z.2.val.Holds (fun i => word (v i) z.1)
  have hg (z : Fin k × Q) (c : S → L) (hc : IsConstant c) :
      (test z).out c = (test z).Q.coeff := by
    let s₀ : S := Classical.choice inferInstance
    change (D z.2).out (fun s => word (c s) z.1) = (D z.2).Q.coeff
    have he : (fun s => word (c s) z.1) = (fun _ => word (c s₀) z.1) :=
      funext fun s => congrArg (fun x => word x z.1) (hc s s₀)
    rw [he, hpres]
  have hb (z : Fin k × Q) (c : S → L) (hc : bad z c) : (test z).out c = 0 := by
    obtain ⟨v, rfl, hv⟩ := hc
    exact hkill z.2 (fun i => word (v i) z.1) hv
  obtain ⟨T, hprice, hpass, hfail⟩ := parallel_tests φ Finset.univ test IsConstant bad
    (fun z _ => hg z) (fun z _ => hb z)
  have hd (c : S → L) (hm : Compatible group Finset.univ c) (hc : ¬ IsConstant c) :
      T.out c = 0 := by
    choose rep hrep using hsur
    let v : Fin r → L := c ∘ rep
    have he : c = v ∘ group := funext fun s =>
      hm s (rep (group s)) (Finset.mem_univ _) (hrep _).symm
    have hnc : ¬ IsConstant (fun i => word (v i)) := by
      intro hconstant
      apply hc
      intro s t
      rw [congrFun he s, congrFun he t]
      exact inj (hconstant (group s) (group t))
    obtain ⟨i, q, hq, hqv⟩ := exists_violated_anchorRule hfree hAB (fun g => word (v g))
      (fun g => hw (v g)) hnc
    exact hfail (i, ⟨q, hq⟩) (Finset.mem_univ _) c ⟨v, he, hqv⟩
  have hdiag := diagonal_price_bound φ group hsur T hpass hd
  rw [hprice] at hdiag
  have hcst : ∑ z : Fin k × Q, (test z).cost φ ≤ (k : ℝ) * ∑ q ∈ anchorRules A B, cost q := by
    calc
      _ ≤ ∑ z : Fin k × Q, cost z.2.val := Finset.sum_le_sum fun z _ => hcost z.2
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Q, Finset.sum_attach]
  exact (by simpa [L] using hdiag.trans hcst)

end Comparison
end Sunflower
end Combinatorics
end OAI
