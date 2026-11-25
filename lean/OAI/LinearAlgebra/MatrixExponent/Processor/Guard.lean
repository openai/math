import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.Defs
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Replay
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Broadcast
import OAI.LinearAlgebra.MatrixExponent.Control.Named
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present

/-! # Padding finite tables and private bit assignments -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Classical Finset
variable {F A B : Type} [Field F] (e : A ↪ B)

/-- An unused position must contain zero. -/
def unused (j : B) (x : Bool) : F :=
  if x = false ∨ ∃ i, e i = j then 1 else 0

variable [Fintype A] [Fintype B]

theorem prod_padded (g : B → F) (hone : ∀ j, (¬∃ i, e i = j) → g j = 1) :
    (∏ j, g j) = ∏ i, g (e i) := by
  rw [← prod_map univ e g]
  symm
  exact prod_subset (subset_univ _) (fun j _ hj => hone j (by simpa using hj))

/-- Each assignment on the active bits has exactly one extension with
nonzero padding weight, even in characteristic two. -/
theorem sum_padded [DecidableEq A] [DecidableEq B] (f : (A → Bool) → F) :
    (∑ y : B → Bool, f (y ∘ e) * ∏ j, unused e j (y j)) = ∑ x, f x := by
  let pad (x : A → Bool) := Function.extend e x (fun _ => false)
  have hp (x) : pad x ∘ e = x := funext fun i => e.injective.extend_apply x (fun _ => false) i
  have hi : Function.Injective pad := fun x y h => by rw [← hp x, h, hp]
  let S := univ.image pad
  have hz (y : B → Bool) (hy : y ∉ S) : (∏ j, unused e j (y j)) = (0 : F) := by
    have hne : pad (y ∘ e) ≠ y := fun h => hy (mem_image.mpr ⟨_, mem_univ _, h⟩)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    apply prod_eq_zero (mem_univ j)
    have hn : ¬ ∃ i, e i = j := by
      rintro ⟨i, rfl⟩
      exact hj (congrFun (hp (y ∘ e)) i)
    have : y j ≠ false := fun h => hj ((Function.extend_apply' _ _ _ hn).trans h.symm)
    exact ite_eq_right (not_or.mpr ⟨this, hn⟩)
  calc
    _ = ∑ y ∈ S, f (y ∘ e) * ∏ j, unused e j (y j) :=
      (sum_subset (subset_univ _) (fun y _ hy => by rw [hz y hy, mul_zero])).symm
    _ = _ := by
      unfold S
      rw [sum_image hi.injOn]
      apply sum_congr rfl
      intro x _
      have h (j : B) : unused e j (pad x j) = (1 : F) := by
        by_cases hj : ∃ i, e i = j
        · exact ite_eq_left (.inr hj)
        · exact ite_eq_left (.inl (Function.extend_apply' _ _ _ hj))
      simp only [hp, h, prod_const_one, mul_one]

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Summing private bits in a scalar network -/

namespace OAI.LinearAlgebra.MatrixExponent.Install.Weight

variable {F I J : Type} [Field F]

private theorem free (b : Wire) : Net F .unit b (fun _ _ => 1) (wd b) := by
  induction b with
  | unit => exact .empty
  | bit => exact .table .unit .bit _ (by decide)
  | pair a b ha hb => simpa only [one_mul, wd] using (ha.par hb).pre (.unit' .unit)

private theorem sum_layout [Fintype J] [DecidableEq J] (a b : Wire)
    (i : I ≃ slots a) (j : J ≃ slots b) (f : (I ⊕ J → Bool) → F) (x : Val a) :
    (∑ y, f (Sum.elim (bits a x ∘ i) y)) =
      ∑ z : Val b, f (bits (.pair a b) (x, z) ∘ i.sumCongr j) * 1 := by
  let e := (bits b).trans (j.symm.arrowCongr (Equiv.refl Bool))
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  rw [mul_one]
  congr 1
  funext t
  cases t <;> rfl

/-- Trace the named private bits against unary tables of weight one.
Every assignment contributes once, with no division by the alphabet size. -/
theorem sum_right [Fintype J] [DecidableEq J] {m : ℕ} {f : (I ⊕ J → Bool) → F}
    (h : Weight F f m) :
    Weight F (fun x => ∑ y : J → Bool, f (Sum.elim x y)) (m + Fintype.card J) := by
  intro a i
  let b := word (Fintype.card J)
  let j : J ≃ slots (word (Fintype.card J)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, h⟩ := h (.pair a b) (i.sumCongr j)
  have k := ((h.par (free b)).pre (.unit' _)).trace
  refine ⟨v + wd b, by simpa [b] using Nat.add_le_add_right hv (Fintype.card J), ?_⟩
  convert k using 1
  funext x y
  exact sum_layout a b i j f x

end OAI.LinearAlgebra.MatrixExponent.Install.Weight
end

section
/-! # Class counts as linear combinations of broadcast bits -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Finset
variable {w : ℕ}

def number (x : Fin w → Bool) := ∑ i, if x i then 2 ^ i.val else 0

theorem number_succ (x : Fin (w + 1) → Bool) :
    number x = (if x 0 then 1 else 0) + number (x ∘ Fin.succ) * 2 := by
  rw [number, Fin.sum_univ_succ]
  simp only [number, Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, sum_mul,
    Function.comp_apply, ite_mul, zero_mul]

theorem number_test (x : ℕ) (hx : x < 2 ^ w) :
    number (fun i : Fin w => x.testBit i.val) = x := by
  induction w generalizing x with
  | zero => simp [number]; omega
  | succ w ih =>
    have h : x / 2 < 2 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rwa [pow_succ] at hx)
    rw [number_succ]
    simp only [Function.comp_def, Fin.val_succ, Nat.testBit_add_one, Fin.val_zero,
      Nat.testBit_zero, decide_eq_true_eq, ih _ h]
    split_ifs <;> omega

private theorem exists_number (x : Fin w → Bool) :
    ∃ k : Fin (2 ^ w), (fun i : Fin w => k.val.testBit i.val) = x := by
  let f (k : Fin (2 ^ w)) (i : Fin w) := k.val.testBit i.val
  have hi : Function.Injective f := fun a b he => Fin.ext <|
    (number_test a.val a.isLt).symm.trans ((congrArg number he).trans (number_test b.val b.isLt))
  exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨hi, by simp⟩).2 x

theorem number_lt (x : Fin w → Bool) : number x < 2 ^ w := by
  obtain ⟨k, rfl⟩ := exists_number x
  rw [number_test k.val k.isLt]
  exact k.isLt

theorem test_number (x : Fin w → Bool) (i : Fin w) : (number x).testBit i.val = x i := by
  obtain ⟨k, rfl⟩ := exists_number x
  rw [number_test k.val k.isLt]

variable {I : Type} [Fintype I]

def linear (a : I → ℕ) (x : I × Fin w → Bool) := ∑ j, number (fun i => x (j, i)) * a j

theorem linear_register (F : Type) [Field F] (a : I → ℕ) (v w : ℕ) :
    Register F v (linear (w := w) a) (20000 * (1 + Fintype.card I * w) * (1 + v)) := by
  have h := Register.weighted F v (fun j : I × Fin w => 2 ^ j.2.val * a j.1)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  convert h using 1
  funext x
  rw [Fintype.sum_prod_type]
  simp only [linear, number, sum_mul, ite_mul, zero_mul]

theorem linear_le {a : I → ℕ} {M : ℕ} (ha : ∀ i, a i ≤ M) (x : I × Fin w → Bool) :
    linear a x ≤ Fintype.card I * (2 ^ w * M) := by
  unfold linear
  calc
    _ ≤ ∑ _ : I, 2 ^ w * M := sum_le_sum (fun i _ => Nat.mul_le_mul (number_lt _).le (ha i))
    _ = _ := by simp

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Scalar checks of bounded linear inequalities -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Install Coloring
variable {F I J : Type} [Field F] [Fintype I] {m v w : ℕ}

theorem Register.offset {f : (I → Bool) → ℕ} (h : Register F v f m) (n : ℕ) :
    Register F v (fun x => f x + n) (m + 10100 * (1 + v)) := by
  have hp := (h.add_disjoint (Register.const (I := Empty) n)).rename (Equiv.sumEmpty I Empty)
  exact hp.mono (by simp; omega)

structure Form (I : Type) where
  factors : I → ℕ
  offset : ℕ

def Form.value (f : Form I) (x : I × Fin w → Bool) := linear f.factors x + f.offset

theorem Form.net (F : Type) [Field F] (f : Form I) (v w : ℕ) :
    Register F v (f.value (w := w)) (40000 * (1 + Fintype.card I * w) * (1 + v)) := by
  apply ((linear_register F f.factors v w).offset f.offset).mono
  ring_nf
  omega

theorem Form.compare (F : Type) [Field F] (f g : Form I) (v w : ℕ)
    (hf : ∀ x : I × Fin w → Bool, f.value x < 2 ^ v)
    (hg : ∀ x : I × Fin w → Bool, g.value x < 2 ^ v) :
    BNet F (fun x : I × Fin w → Bool => fun _ : Unit => decide (f.value x < g.value x))
      (90000 * (1 + Fintype.card I * w) * (1 + v)) := by
  apply ((f.net F v w).less (g.net F v w) hf hg).mono
  rw [Fintype.card_prod, Fintype.card_fin]
  ring_nf
  omega

/-- Each input count field has `w` bits. The register width `v` is
chosen to rule out overflow even on malformed inputs. -/
theorem checks_net (F : Type) [Field F] [Fintype J] (f g : J → Form I) (v w : ℕ)
    (hf : ∀ j (x : I × Fin w → Bool), (f j).value x < 2 ^ v)
    (hg : ∀ j (x : I × Fin w → Bool), (g j).value x < 2 ^ v) :
    Weight F (fun x : I × Fin w → Bool => if ∀ j, (f j).value x < (g j).value x then 1 else 0)
      (100000 * (1 + Fintype.card J) * (1 + Fintype.card I * w) * (1 + v)) := by
  classical
  let p (j : J) (x : I × Fin w → Bool) : F := if (f j).value x < (g j).value x then 1 else 0
  have hp (j : J) : Weight F (p j) (90000 * (1 + Fintype.card I * w) * (1 + v) + 16) := by
    have act := Weight.dense F Unit (fun x => if x () then 1 else 0)
    have h := ((f j).compare F (g j) v w (hf j) (hg j)).weight act
    simpa only [Function.comp_def, decide_eq_true_eq, Fintype.card_unit, pow_one, p] using h
  have k := Weight.finite_product p hp
  simp only [p, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, forall_const] at k
  apply k.mono
  rw [Fintype.card_prod, Fintype.card_fin]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Masked sums of bounded registers -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Register

open Coloring Install Finset
variable {F I J : Type} [Field F] [Fintype I] {m n w : ℕ}
  {f g : (I → Bool) → ℕ}

theorem add (h : Register F w f m) (k : Register F w g n) :
    Register F w (fun x => f x + g x) (5 * Fintype.card I + m + n + 10000 * (1 + w)) := by
  have t := (BNet.pull (h.add_disjoint k) (Sum.elim id id))
  exact t.mono (by rw [Fintype.card_sum]; omega)

theorem sum [Fintype J] (f : J → (I → Bool) → ℕ) (h : ∀ j, Register F w (f j) m) :
    Register F w (fun x => ∑ j, f j x)
      ((1 + Fintype.card J) * (m + 10000 * (Fintype.card I + w + 1))) := by
  classical
  let M := m + 10000 * (Fintype.card I + w + 1)
  suffices ∀ S : Finset J, Register F w (fun x => ∑ j ∈ S, f j x) ((1 + S.card) * M) from this univ
  intro S
  induction S using Finset.induction_on with
  | empty => simpa using (const (F := F) (I := I) (w := w) 0).mono (n := M) (by unfold M; omega)
  | insert a S ha ih =>
    simp only [sum_insert ha, card_insert_of_notMem ha, ← add_assoc, add_mul, one_mul]
    refine ((h a).add ih).mono ?_
    rw [add_mul, one_mul]
    omega

theorem mask {p : (I → Bool) → Bool} (hp : BNet F (fun x (_ : Unit) => p x) n)
    (h : Register F w f m) :
    Register F w (fun x => if p x then f x else 0)
      (5 * Fintype.card I + n + m + 100 * (w + 1)) := by
  let a (x : Unit ⊕ slots (word w) → Bool) (i : slots (word w)) :=
    if x (.inl ()) then x (.inr i) else digits w 0 i
  have ha : Depends a 2 := by
    intro i
    refine ⟨{.inl (), .inr i}, by simp, fun x y he => ?_⟩
    simp only [a, he (.inl ()) (by simp), he (.inr i) (by simp)]
  have t := (hp.pair h).comp (ha.bnet F)
  have he : (a ∘ (fun x => Sum.elim (fun _ : Unit => p x) (digits w (f x)))) =
      (fun x => digits w (if p x then f x else 0)) := by
    funext x i
    cases hc : p x <;> simp [a, hc]
  rw [he] at t
  apply t.mono
  simp only [Fintype.card_sum, Fintype.card_unit, card_slots, wd_word, localCost]
  omega

end OAI.LinearAlgebra.MatrixExponent.Processor.Register
end

/-!
# Programming a vertex by a constant-size truth table

The fourth address is spare for trivalent vertices. Reading four
addresses per instruction makes the parallel reader a binary tree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

structure Rule (F I : Type) where
  args : Fin 4 → I
  weight : (Fin 4 → Bool) → F

namespace Rule
open Classical

variable {F I J : Type}

def eval (p : Rule F I) (x : I → Bool) : F := p.weight (x ∘ p.args)

def reindex (p : Rule F I) (a : I → J) : Rule F J := ⟨a ∘ p.args, p.weight⟩

theorem of_local [Fintype J] [Nonempty I] (a : J → I) (h : Fintype.card J ≤ 4)
    (k : (J → Bool) → F) :
    ∃ p : Rule F I, ∀ x, p.eval x = k (x ∘ a) := by
  obtain ⟨e⟩ : Nonempty (J ↪ Fin 4) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let spare := fun _ : Fin 4 => Classical.choice (inferInstance : Nonempty I)
  refine ⟨⟨Function.extend e a spare, fun y => k (y ∘ e)⟩, fun x => ?_⟩
  unfold eval
  apply congrArg k
  funext t
  exact congrArg x (e.injective.extend_apply a spare t)

end Rule

open Classical
variable {F I : Type} {a b : Wire} (G : Diagram F a b)

/-- The addresses of a gate may coincide, even across its two sides. -/
theorem vertex_rule [Nonempty I] (h : G.Trivalent)
    (input : slots a → I) (output : slots b → I) (edge : G.E → I) (v : G.V) :
    ∃ p : Rule F I, ∀ x, p.eval x =
      G.vertex ((bits a).symm (x ∘ input)) ((bits b).symm (x ∘ output)) (x ∘ edge) v := by
  let f : G.Port v → I :=
    Sum.elim (fun i => Sum.elim input edge (G.src ⟨v, i⟩))
      (fun i => Sum.elim output edge (G.dst ⟨v, i⟩))
  let k (x : G.Port v → Bool) := (G.table v).2.2
    ((bits (G.table v).1).symm (x ∘ Sum.inl)) ((bits (G.table v).2.1).symm (x ∘ Sum.inr))
  have hc : Fintype.card (G.Port v) ≤ 4 := by
    rw [Fintype.card_sum, card_slots, card_slots]
    exact (h v).trans (by decide)
  obtain ⟨p, hp⟩ := Rule.of_local f hc k
  refine ⟨p, fun x => ?_⟩
  rw [hp, Diagram.vertex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  unfold k f
  apply congrArg₂ (G.table v).2.2
  · apply congrArg (bits (G.table v).1).symm
    funext i
    simp only [Function.comp_apply, Sum.elim_inl]
    cases G.src ⟨v, i⟩ <;> rfl
  · apply congrArg (bits (G.table v).2.1).symm
    funext i
    simp only [Function.comp_apply, Sum.elim_inr]
    cases G.dst ⟨v, i⟩ <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Trivalent diagrams as lists of local instructions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Classical Finset
variable {F J A B : Type} [Field F] [Fintype A] [Fintype B]

private theorem extra_rules [Nonempty J] (p : A → Rule F J) (h : Fintype.card A ≤ Fintype.card B) :
    ∃ q : B → Rule F J, ∀ x, ∏ i, (q i).eval x = ∏ i, (p i).eval x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  let one : Rule F J := ⟨fun _ => choice inferInstance, fun _ => 1⟩
  let q := Function.extend e p (fun _ => one)
  refine ⟨q, fun x => ?_⟩
  rw [prod_padded e _ (fun j hj => by rw [show q j = one from Function.extend_apply' _ _ _ hj]; rfl)]
  simp only [q, e.injective.extend_apply]

/-- One half of the instructions represents vertices. The other half
pins private bits beyond the last internal edge. Both sets of external
slots may refer to any visible data positions. -/
theorem compile {a b : Wire} (G : Diagram F a b) (h : G.Trivalent)
    [DecidableEq B] [Nonempty B] (src : slots a → B) (dst : slots b → B)
    (hv : Fintype.card G.V ≤ Fintype.card B) (he : Fintype.card G.E ≤ Fintype.card B) :
    ∃ p : B ⊕ B → Rule F (B ⊕ B), ∀ x : B → Bool,
      (∑ y : B → Bool, ∏ i, (p i).eval (Sum.elim x y)) =
        G.eval ((bits a).symm (x ∘ src)) ((bits b).symm (x ∘ dst)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le he
  choose p hp using vertex_rule (I := B ⊕ B) G h (Sum.inl ∘ src) (Sum.inl ∘ dst) (Sum.inr ∘ e)
  obtain ⟨q, hq⟩ := extra_rules p hv
  let pin (j : B) : Rule F (B ⊕ B) := ⟨fun _ => .inr j, fun v => unused e j (v 0)⟩
  refine ⟨Sum.elim q pin, fun x => ?_⟩
  have ht (y : B → Bool) :
      (∏ i, ((Sum.elim q pin) i).eval (Sum.elim x y)) =
        (∏ i, G.vertex ((bits a).symm (x ∘ src)) ((bits b).symm (x ∘ dst)) (y ∘ e) i) *
          ∏ j, unused e j (y j) := by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, hq, hp]
    rfl
  simp_rw [ht]
  exact sum_padded e (fun z => ∏ i, G.vertex ((bits a).symm (x ∘ src)) ((bits b).symm (x ∘ dst)) z i)

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# Feasibility of reported selector counts

A class can realize prescribed multiplicities exactly when their sum
equals the size of the class. Combining the classes and checking the
choice of cut then characterizes the reports of actual assignments.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
open Classical

private theorem prescribe {P I : Type} [Fintype P] [Fintype I] [DecidableEq I] (m : I → ℕ) :
    (∑ i, m i) = Fintype.card P ↔ ∃ s : P → I, ∀ i, multiplicity s i = m i := by
  constructor
  · intro h
    let e : P ≃ (Σ i, Fin (m i)) := Fintype.equivOfCardEq (by simp [h])
    refine ⟨fun p => (e p).1, fun i => ?_⟩
    let f : {v : (Σ i, Fin (m i)) // v.1 = i} ≃ Fin (m i) :=
      { toFun := fun v => v.property ▸ v.val.2
        invFun := fun j => ⟨⟨i, j⟩, rfl⟩
        left_inv := by rintro ⟨⟨j, x⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    let e' : {p // (e p).1 = i} ≃ Fin (m i) :=
      (e.subtypeEquiv (fun _ => Iff.rfl)).trans f
    exact (Fintype.card_congr e').trans (Fintype.card_fin _)
  · rintro ⟨s, hs⟩
    simp only [← hs, multiplicity, ← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv s)

variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (R : A.Report r d)

def feasible : Prop :=
  ∀ c, ∑ i, (R.2 (c, i)).val = Fintype.card (A.Members hn R c)

theorem feasible_selectors :
    A.feasible hn R ↔ ∀ c, Nonempty (A.Selectors hn R c) := by
  unfold feasible
  apply forall_congr'
  intro c
  rw [prescribe]
  exact ⟨fun ⟨s, hs⟩ => ⟨⟨s, hs⟩⟩, fun ⟨s⟩ => ⟨s.val, s.property⟩⟩

theorem feasible_valid : A.feasible hn R ∧ A.valid hn R ↔ ∃ s, R = A.report hn s := by
  rw [A.feasible_selectors]
  constructor
  · rintro ⟨hf, hv⟩
    let t := fun c => (hf c).some
    let e := ((Equiv.sigmaFiberEquiv (packetClass (d := d) (r := r) hn R.1)).symm.arrowCongr
      (Equiv.refl A.I)).trans (Equiv.piCurry (fun _ _ => A.I))
    obtain ⟨s, hs⟩ := e.surjective (fun c => (t c).val)
    refine ⟨s, (A.checks_iff hn R s).mp ⟨hv, (A.counts_match hn R s).mp ?_⟩⟩
    intro c z
    change multiplicity (e s c) z = _
    rw [hs]
    exact (t c).property z
  · rintro ⟨s, hs⟩
    obtain ⟨hv, hc⟩ := (A.checks_iff hn R s).mpr hs
    exact ⟨fun c => ⟨⟨fun p => s p.1, (A.counts_match hn R s).mpr hc c⟩⟩, hv⟩

theorem feasible_symbols (N : ℕ) {T : Type} :
    A.feasible hn R ↔ Nonempty ((e : T ⊕ Edge n r d h) → A.ExtraSymbol hn N R e) := by
  rw [A.feasible_selectors]
  constructor
  · intro hs
    refine ⟨?_⟩
    rintro (p|p|c)
    · exact false
    · exact false
    · exact ⟨(hs c).some, fun _ _ => false⟩
  · rintro ⟨x⟩ c
    exact ⟨(x (.inr (.inr c))).1⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# Checking a public report from its binary counts

Check the class sizes and the minimizing coordinate. These checks force
the counts into range and identify an actual report, so the budget
follows from the bound for genuine assignments.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Finset
variable {F : Type} [Field F] {n h r d : ℕ} (A : Expansion F n h) (hn : 2 ≤ n)

def cnt (x : A.CountBit r d → Bool) (z : Class r × A.I) :=
  Processor.number (fun j => x (z, j))

def guard (i : Fin n) (x : A.CountBit r d → Bool) : Prop :=
  (∀ c, ∑ z, A.cnt x (c, z) = Fintype.card {p : Packet n r d // packetClass hn i p = c}) ∧
    i = first hn (fun j => ∑ z, A.cnt x z * A.cross z.2 j)

@[simp] theorem cnt_countBits (R : A.Report r d) (z : Class r × A.I) :
    A.cnt (A.countBits R) z = (R.2 z).val :=
  Processor.number_test _ ((R.2 z).isLt.trans_le (Nat.le_pow_clog (by decide) _))

private theorem guard_report (R : A.Report r d) :
    A.guard hn R.1 (A.countBits R) ↔ A.feasible hn R ∧ A.valid hn R := by
  simp only [guard, cnt_countBits, feasible, valid, total, Members]

theorem guard_iff (N : ℕ)
    (hbudget : ∀ s : Packet n r d → A.I, A.budget hn N (A.report hn s))
    (i : Fin n) (x : A.CountBit r d → Bool) :
    A.guard hn i x ↔ ∃ R : A.Accepted (r := r) (d := d) hn (A.budget hn N),
      A.feasible hn R.val ∧ R.val.1 = i ∧ A.countBits R.val = x := by
  constructor
  · intro hx
    have small (z : Class r × A.I) : A.cnt x z < Fintype.card (Packet n r d) + 1 := by
      apply Nat.lt_succ_of_le
      calc
        A.cnt x z ≤ ∑ j, A.cnt x (z.1, j) :=
          single_le_sum (f := fun j => A.cnt x (z.1, j)) (fun _ _ => Nat.zero_le _) (mem_univ z.2)
        _ = _ := hx.1 z.1
        _ ≤ _ := Fintype.card_subtype_le _
    let R : A.Report r d := (i, fun z => ⟨A.cnt x z, small z⟩)
    have he : A.countBits R = x := by
      funext ⟨z, j⟩
      exact Processor.test_number (fun k => x (z, k)) j
    have hh := (A.guard_report hn R).mp (he.symm ▸ hx)
    obtain ⟨s, hs⟩ := (A.feasible_valid hn R).mp hh
    exact ⟨⟨R, hh.2, hs.symm ▸ hbudget s⟩, hh.1, rfl, he⟩
  · rintro ⟨R, hf, rfl, rfl⟩
    exact (A.guard_report hn R.val).mpr ⟨hf, R.property.1⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

section
/-!
# A programmable product of local weights

A common array stores the data bits. Each row supplies a descriptor and
four addresses in the array. Four batches of indirect reads deliver
the arguments to independent copies of the local table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Install
variable {F C : Type} [Field F]

abbrev Ports (C : Type) (w : ℕ) :=
  Fin (2 ^ w) ⊕ (Fin 4 × Fin (2 ^ w) × slots (word w)) ⊕ (Fin (2 ^ w) × C)

def evaluate (g : (C → Bool) → (Fin 4 → Bool) → F) (w : ℕ) (x : Ports C w → Bool) : F :=
  ∏ i : Fin (2 ^ w), g (fun c => x (.inr (.inr (i, c))))
    (fun k => x (.inl (Control.decode w (fun j => x (.inr (.inl (k, i, j)))))))

def cost (C : Type) [Fintype C] := 50000 + 4 * Fintype.card C + 8 * 2 ^ (4 + Fintype.card C)

theorem evaluate_net [Fintype C] (g : (C → Bool) → (Fin 4 → Bool) → F) (w : ℕ) :
    Weight F (evaluate g w) (cost C * 2 ^ w * (w + 1) ^ 3) := by
  let I := Fin (2 ^ w)
  have reads := BNet.family 2 (fun _ => Control.read w) (fun _ => Control.read_net F w)
  let dup : (Fin 4 × (I ⊕ I × slots (word w))) ⊕ (I × C) → Ports C w
    | .inl (_, .inl i) => .inl i
    | .inl (k, .inr p) => .inr (.inl (k, p))
    | .inr p => .inr (.inr p)
  have gather := (reads.parallel (BNet.id F (I × C))).pull dup
  have table := Weight.dense F (Fin 4 ⊕ C) (fun x => g (x ∘ Sum.inr) (x ∘ Sum.inl))
  let e := (Equiv.prodSumDistrib I (Fin 4) C).trans
    ((Equiv.prodComm I (Fin 4)).sumCongr (.refl _))
  apply (gather.weight ((table.prod w).rename e)).mono
  simp only [I, Ports, cost, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    card_slots, wd_word]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# A binary program for a finite-field table network

For each of the sixteen possible argument strings a descriptor has one
bit per field element. A valid program sets just the bit corresponding
to the desired weight. Even arbitrary descriptor bits have a well-defined
interpretation, the sum of the selected field elements.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

abbrev Descriptor (F : Type) := (Fin 4 → Bool) × F

abbrev Script (F : Type) (w : ℕ) :=
  (Fin 4 × Fin (2 ^ w) × slots (word w)) ⊕ (Fin (2 ^ w) × Descriptor F)

theorem card_script (F : Type) [Fintype F] (w : ℕ) :
    Fintype.card (Script F w) = 2 ^ w * (4 * w + 16 * Fintype.card F) := by
  simp [Script, Descriptor]
  ring

def program (F : Type) [DecidableEq F] (w : ℕ) (P : Fin (2 ^ w) → Rule F (Fin (2 ^ w))) :
    Script F w → Bool
  | .inl (k, i, j) => (Control.decode w).symm ((P i).args k) j
  | .inr (i, t, z) => decide ((P i).weight t = z)

def run (F : Type) [Field F] [Fintype F] (w : ℕ) : (Fin (2 ^ w) ⊕ Script F w → Bool) → F :=
  evaluate (fun (d : Descriptor F → Bool) t => ∑ z, if d (t, z) then z else 0) w

theorem run_program {F : Type} [Field F] [Fintype F] [DecidableEq F] {w : ℕ}
    (P : Fin (2 ^ w) → Rule F (Fin (2 ^ w))) (x : Fin (2 ^ w) → Bool) :
    run F w (Sum.elim x (program F w P)) = ∏ j, (P j).eval x := by
  simp only [run, evaluate, Sum.elim_inl, Sum.elim_inr, program, Equiv.apply_symm_apply,
    decide_eq_true_eq, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Rule.eval, Function.comp_def]

theorem run_net (F : Type) [Field F] [Fintype F] (w : ℕ) :
    Install.Weight F (run F w) (cost (Descriptor F) * 2 ^ w * (w + 1) ^ 3) :=
  evaluate_net _ w

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# Repeated programmable contractions

The two halves of a data array hold exterior and private bits. Each
copy sums its private bits independently. The script is shared.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Install

def dataSlots (w : ℕ) : Fin (2 ^ w) ⊕ Fin (2 ^ w) ≃ Fin (2 ^ (w + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

def data (w : ℕ) (x y : Fin (2 ^ w) → Bool) : Fin (2 ^ (w + 1)) → Bool :=
  Sum.elim x y ∘ (dataSlots w).symm

variable (F : Type) [Field F] [Fintype F]

def template (w : ℕ) (s : Fin (2 ^ w) ⊕ Script F (w + 1) → Bool) : F :=
  ∑ t : Fin (2 ^ w) → Bool, run F (w + 1) (Sum.elim (data w (s ∘ Sum.inl) t) (s ∘ Sum.inr))

private def reorder (X Y : Type) : (X ⊕ X) ⊕ Y ≃ (X ⊕ Y) ⊕ X :=
  (Equiv.sumAssoc _ _ _).trans
    (((Equiv.refl X).sumCongr (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm)

theorem template_net (w : ℕ) :
    Weight F (template F w) (cost (Descriptor F) * 2 ^ (w + 1) * (w + 2) ^ 3 + 2 ^ w) := by
  let e := ((dataSlots w).symm.sumCongr (.refl (Script F (w + 1)))).trans (reorder _ _)
  have h := ((run_net F (w + 1)).rename e).sum_right
  rw [Fintype.card_fin] at h
  convert h using 1
  funext s
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg
  funext k
  rcases k with i | i
  · change Sum.elim (s ∘ Sum.inl) t ((dataSlots w).symm i) =
      Sum.elim s t (reorder _ _ (.inl ((dataSlots w).symm i)))
    cases (dataSlots w).symm i <;> rfl
  · rfl

def repeated (w j : ℕ) (x : (Fin (2 ^ j) × Fin (2 ^ w)) ⊕ Script F (w + 1) → Bool) : F :=
  ∏ i, template F w (Sum.elim (fun k => x (.inl (i, k))) (x ∘ Sum.inr))

def templateCost := 2 * cost (Descriptor F) + 128 * (1 + Fintype.card F)

theorem repeated_net (w j : ℕ) :
    Weight F (repeated F w j) (templateCost F * 2 ^ j * 2 ^ w * (w + 2) ^ 3) := by
  let A := Fin (2 ^ j)
  let X := Fin (2 ^ w)
  let Y := Script F (w + 1)
  let addr : A × (X ⊕ Y) → (A × X) ⊕ Y
    | (i, .inl k) => .inl (i, k)
    | (_, .inr k) => .inr k
  have h := ((template_net F w).prod j).pull addr
  have he (x : (A × X) ⊕ Y → Bool) (i : A) :
      (fun k => (x ∘ addr) (i, k)) = Sum.elim (fun k => x (.inl (i, k))) (x ∘ Sum.inr) := by
    funext k
    cases k <;> rfl
  rw [show repeated F w j = (fun x => ∏ i, template F w (fun k => (x ∘ addr) (i, k))) from
    funext fun x => Finset.prod_congr rfl (fun i _ => congrArg _ (he x i).symm)]
  apply h.mono
  dsimp only [A, X, Y]
  rw [Fintype.card_sum, Fintype.card_prod, card_script, Fintype.card_prod, Fintype.card_sum,
    card_script, Fintype.card_fin, Fintype.card_fin]
  have hp : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
  let S := 2 ^ (w + 1) * (4 * (w + 1) + 16 * Fintype.card F)
  calc
    _ ≤ 3 * 2 ^ j * (2 ^ w + S) + 2 ^ j * (cost (Descriptor F) * 2 ^ (w + 1) * (w + 2) ^ 3 + 2 ^ w) := by
      have hs := Nat.le_mul_of_pos_left S hp
      unfold S at hs ⊢
      nlinarith only [hs]
    _ = (2 ^ j * 2 ^ w) * (4 + 24 * (w + 1) + 96 * Fintype.card F + 2 * cost (Descriptor F) * (w + 2) ^ 3) := by
      unfold S
      rw [pow_succ]
      ring
    _ ≤ (2 ^ j * 2 ^ w) * (templateCost F * (w + 2) ^ 3) := by
      apply Nat.mul_le_mul_left
      unfold templateCost
      have hw : w + 2 ≤ (w + 2) ^ 3 := Nat.le_pow (by decide)
      have hf := Nat.mul_le_mul_left (Fintype.card F) (by omega : 1 ≤ (w + 2) ^ 3)
      nlinarith only [hw, hf]
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# Programming a network template

One script records the wiring and coefficients of a trivalent network.
The script is independent of the values at all visible positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Classical Finset
variable {F : Type} [Field F] [Fintype F] {a b : Wire} {w m : ℕ}

theorem template_program {k : Val a → Val b → F} (h : Net F a b k m)
    (hm : 2 * m ≤ 2 ^ w) (src : slots a → Fin (2 ^ w)) (dst : slots b → Fin (2 ^ w)) :
    ∃ code, ∀ x : Fin (2 ^ w) → Bool,
      template F w (Sum.elim x code) = k ((bits a).symm (x ∘ src)) ((bits b).symm (x ∘ dst)) := by
  obtain ⟨G, rfl, ht, hcard⟩ := h.diagram
  have hc := G.cost_trivalent ht
  rw [Diagram.cost_eq, hcard] at hc
  obtain ⟨p, hp⟩ := compile G ht src dst (by rw [Fintype.card_fin]; omega)
    (by rw [Fintype.card_fin]; omega)
  let e := dataSlots w
  let q i := (p (e.symm i)).reindex e
  refine ⟨program F (w + 1) q, fun x => ?_⟩
  rw [← hp]
  unfold template
  apply sum_congr rfl
  intro y _
  change run F (w + 1) (Sum.elim (data w x y) (program F (w + 1) q)) = _
  rw [run_program, ← e.prod_comp]
  apply prod_congr rfl
  intro i _
  simp only [q, Rule.reindex, Rule.eval, data, e, Function.comp_def, Equiv.symm_apply_apply]

/-- In particular any bounded weighted circuit on named input bits can
be evaluated repeatedly without duplicating its program input. -/
theorem weight_program {I : Type} [Fintype I] {f : (I → Bool) → F}
    (hf : Install.Weight F f m) (hm : 2 * m ≤ 2 ^ w) (src : I → Fin (2 ^ w)) :
    ∃ code, ∀ x : Fin (2 ^ w) → Bool, template F w (Sum.elim x code) = f (x ∘ src) := by
  let e : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, net⟩ := hf _ e
  obtain ⟨code, hcode⟩ := template_program net ((Nat.mul_le_mul_left 2 hv).trans hm)
    (src ∘ e.symm) Empty.elim
  refine ⟨code, fun x => ?_⟩
  simpa only [Function.comp_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hcode x

end OAI.LinearAlgebra.MatrixExponent.Processor
end
