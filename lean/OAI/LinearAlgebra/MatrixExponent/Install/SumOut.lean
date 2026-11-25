import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import Mathlib.Data.Fintype.Option
import OAI.LinearAlgebra.MatrixExponent.Install.Close
import OAI.LinearAlgebra.MatrixExponent.Control.Named
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section
/-! # Packing whole fibres into bins of twice the average capacity -/

namespace OAI.LinearAlgebra.MatrixExponent.Install
open Finset

theorem exists_bins {α β : Type} [Fintype α] [DecidableEq β] (group : α → β) (u v : ℕ)
    (hs : ∀ y, (Finset.univ.filter (fun x => group x = y)).card ≤ u)
    (hu : 0 < u) (hc : Fintype.card α ≤ v * u) :
    ∃ e : α ↪ Fin v × Fin (2 * u), ∀ x y, group x = group y → (e x).1 = (e y).1 := by
  classical
  by_cases hv : v = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by simpa [hv] using hc)
    exact ⟨⟨isEmptyElim, fun x => isEmptyElim x⟩, fun x => isEmptyElim x⟩
  let _ : NeZero v := ⟨hv⟩
  let bin (p : β → Fin v) (s : Finset β) (j : Fin v) :=
    univ.filter (fun x => group x ∈ s ∧ p (group x) = j)
  have assign (s : Finset β) : ∃ p, ∀ j, (bin p s j).card ≤ 2 * u := by
    induction s using Finset.induction with
    | empty => exact ⟨fun _ => 0, by simp [bin]⟩
    | insert y s hy ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨i, hi⟩ := Fintype.exists_card_fiber_le_of_card_le_mul (f := p ∘ group)
        (n := u) (by simpa using hc)
      let q := Function.update p y i
      refine ⟨q, fun j => ?_⟩
      by_cases he : i = j
      · subst j
        have sub : bin q (insert y s) i ⊆
            univ.filter (fun x => (p ∘ group) x = i) ∪ univ.filter (fun x => group x = y) := by
          intro x hx
          by_cases h : group x = y
          · simp [h]
          · have := (mem_filter.mp hx).2.2
            simp [q, h] at this
            simp [this]
        exact (card_le_card sub).trans ((card_union_le _ _).trans (by simpa [two_mul] using Nat.add_le_add hi (hs y)))
      · apply (card_le_card ?_).trans (hp j)
        intro x hx
        by_cases h : group x = y
        · simp [bin, q, h, he] at hx
        · simpa [bin, q, h] using hx
  let s := univ.image group
  obtain ⟨p, hp⟩ := assign s
  have index (j : Fin v) : ∃ f : α → Fin (2 * u), Set.InjOn f (bin p s j) := by
    obtain ⟨e⟩ : Nonempty (bin p s j ↪ Fin (2 * u)) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hp j)
    refine ⟨fun x => if h : x ∈ bin p s j then e ⟨x, h⟩ else ⟨0, by omega⟩, ?_⟩
    intro x hx y hy he
    simp only [mem_coe] at hx hy
    simp only [dite_eq_left hx, dite_eq_left hy] at he
    exact congrArg Subtype.val (e.injective he)
  choose f hf using index
  have mem (x : α) : x ∈ bin p s (p (group x)) := by simp [bin, s]
  let pack (x : α) := (p (group x), f (p (group x)) x)
  have inj : Function.Injective pack := by
    intro x y e
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj e
    rw [h₁] at h₂
    exact hf _ (h₁ ▸ mem x) (mem y) h₂
  exact ⟨⟨pack, inj⟩, fun _ _ h => congrArg p h⟩

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-! # Pushing a weighted network through deterministic postprocessing -/

namespace OAI.LinearAlgebra.MatrixExponent.Install

theorem push {F I J : Type} [Field F] [Fintype J] {a b : Wire}
    {f : Val a → Val b → F} {m n : ℕ} (hf : Net F a b f m) (i : I ≃ slots b)
    {g : (I → Bool) → (J → Bool)} (hg : BNet F g n)
    (valid : (J → Bool) → Prop) (orig : (I → Bool) → F) (result : (J → Bool) → F)
    (h : ∀ x y, f x y ≠ 0 → let z := bits b y ∘ i
      valid (g z) ∧ result (g z) = orig z) :
    ∃ v ≤ m + n, ∃ (c : Wire) (j : J ≃ slots c) (k : Val a → Val c → F),
      Net F a c k v ∧ (∀ x y, k x y ≠ 0 → valid (bits c y ∘ j)) ∧
      ∀ x, (∑ y, f x y * orig (bits b y ∘ i)) = ∑ y, k x y * result (bits c y ∘ j) := by
  let c := word (Fintype.card J)
  let _ : DecidableEq (Val c) := valDecidableEq c
  let j : J ≃ slots (word (Fintype.card J)) := Fintype.equivOfCardEq (by simp)
  let emit (y : Val b) := (bits c).symm (g (bits b y ∘ i) ∘ j.symm)
  have eqn (y) : bits c (emit y) ∘ j = g (bits b y ∘ i) := by
    simp [emit, Function.comp_def]
  obtain ⟨u, hu, emit_net⟩ := hg b c i j
  refine ⟨m + u, Nat.add_le_add_left hu m, c, j, _, hf.comp emit_net, ?_, ?_⟩
  · intro x z hz
    by_contra hn
    apply hz
    apply Finset.sum_eq_zero
    intro y _
    change f x y * (@ite F (emit y = z) (valDecidableEq c _ _) 1 0) = 0
    by_cases hy : f x y = 0
    · simp [hy]
    · have ne : emit y ≠ z := by
        rintro rfl
        exact hn (by rw [eqn]; exact (h x y hy).1)
      simp [ne]
  · intro x
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    change _ = f x y * result (bits c (emit y) ∘ j)
    by_cases hy : f x y = 0
    · simp [hy]
    · rw [eqn, (h x y hy).2]

end OAI.LinearAlgebra.MatrixExponent.Install
end

/-! # Summing a weight over hidden indices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Install.Weight
open Classical

variable {F I J : Type} [Field F] [Fintype I] [Fintype J]

private theorem free (a : Wire) : Net F .unit a (fun _ _ => 1) (wd a) := by
  induction a with
  | unit => exact Net.empty
  | bit => exact Net.table _ _ _ (by decide)
  | pair a b ha hb =>
    simpa only [one_mul, wd] using (ha.par hb).pre (.unit' _)

private theorem sum_aux (b : Wire) (j : J ≃ slots b) {f : (I ⊕ J → Bool) → F} {m : ℕ} (h : Weight F f m) :
    Weight F (fun x => ∑ y : J → Bool, f (Sum.elim x y)) (Fintype.card I + Fintype.card J + m) := by
  intro a i
  obtain ⟨n, hn, k⟩ := h (.pair a b) (i.sumCongr j)
  obtain ⟨u, hu, id⟩ := DNet.id F a
  have G := ((id.par (free b)).pre (.unit' _)).comp k
  refine ⟨u + wd b + n, ?_, ?_⟩
  · simpa [Fintype.card_congr i, Fintype.card_congr j] using Nat.add_le_add (Nat.add_le_add_right hu (wd b)) hn
  have he (x : Val a) (y : Val b) : bits (.pair a b) (x, y) ∘ (i.sumCongr j) =
      Sum.elim (bits a x ∘ i) (bits b y ∘ j) := by funext z; cases z <;> rfl
  convert G using 1
  funext x _
  change (∑ y : J → Bool, f (Sum.elim (bits a x ∘ i) y)) = ∑ p : Val a × Val b,
    ((if x = p.1 then 1 else 0) * 1) * f (bits (.pair a b) p ∘ (i.sumCongr j))
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [mul_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]
  let e := (bits b).trans (j.symm.arrowCongr (Equiv.refl Bool))
  exact (e.sum_comp (fun y => f (Sum.elim (bits a x ∘ i) y))).symm

theorem sum_out {f : (I ⊕ J → Bool) → F} {m : ℕ} (h : Weight F f m) :
    Weight F (fun x => ∑ y : J → Bool, f (Sum.elim x y)) (Fintype.card I + Fintype.card J + m) :=
  sum_aux (word (Fintype.card J)) (Fintype.equivOfCardEq (by simp)) h

end OAI.LinearAlgebra.MatrixExponent.Install.Weight
end

section
/-! # Running a finite family of circuits on shared input bits -/

namespace OAI.LinearAlgebra.MatrixExponent.Install.BNet

theorem finite_share {F I J C : Type} [Field F] [Fintype I] [Fintype J] [Fintype C]
    {m : ℕ} (f : C → (I → Bool) → J → Bool) (h : ∀ c, BNet F (f c) m) :
    BNet F (fun x (p : C × J) => f p.1 x p.2)
      (Fintype.card I + Fintype.card C * (5 * Fintype.card I + m)) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun T => ∀ f : T → (I → Bool) → J → Bool, (∀ c, BNet F (f c) m) →
      BNet F (fun x (p : T × J) => f p.1 x p.2)
        (Fintype.card I + Fintype.card T * (5 * Fintype.card I + m)))
    ?_ ?_ ?_ C f h
  · intro A B _ e ih g hg
    let := Fintype.ofEquiv B e.symm
    have h' := (ih (g ∘ e) (fun c => hg (e c))).rename (.refl I) (e.prodCongr (.refl J))
    rw [Fintype.card_congr e] at h'
    convert h' using 1
    funext x ⟨b, j⟩
    simp
  · intro g _
    have h' : Depends (fun x (p : PEmpty × J) => g p.1 x p.2) 0 := fun p => p.1.elim
    simpa using h'.bnet F
  · intro A _ ih g hg
    have h' := (hg none).pair (ih (fun a => g (some a)) (fun a => hg (some a)))
    convert h'.rename (.refl I) optionProdEquiv.symm using 1
    · funext x ⟨a, j⟩
      cases a <;> rfl
    · rw [Fintype.card_option]
      ring

end OAI.LinearAlgebra.MatrixExponent.Install.BNet
end

section
/-!
# Assigning endpoint records to batches

Compute a bucket mask for each batch and look up the mask bit at
each endpoint's source. The batch is active if the mask is nonempty.
The lookup works for repeated source identifiers.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {I J : Type}

private def masked (x : Bus I J ⊕ I → Bool) : Records I J :=
  Sum.elim (fun i => x (.inl (.inl i)) && x (.inr i)) (fun z => x (.inl (.inr z)))

private theorem masked_local : Depends (masked (I := I) (J := J)) 2 := by
  classical
  rintro (i | z)
  · refine ⟨{.inl (.inl i), .inr i}, by simp, fun x y he => ?_⟩
    exact congrArg₂ Bool.and (he _ (by simp)) (he _ (by simp))
  · exact ⟨{.inl (.inr z)}, by simp, fun _ _ he => he _ (by simp)⟩

variable (F : Type) [Field F] {w r : ℕ} (ids : slots (word w) → Fin r)

private abbrev Port (w r : ℕ) := Bus (Idx w) (Fin r)

private def oneBatch (q j : ℕ) (x : Port w r → Bool) : Unit ⊕ Port w r → Bool :=
  Sum.elim (fun _ => decide (∃ i, bucket q j (x ∘ Sum.inl) i = true))
    (select (fun v => Control.decode w (v ∘ ids)) q j x)

private theorem oneBatch_net (q j : ℕ) :
    BNet F (oneBatch ids q j) (100000 * 2 ^ w * ((1 + w) ^ 4 + r)) := by
  have hb := Control.bucket_bnet F w q j
  have test := (hb.pull (Sum.inl : Idx w → Port w r)).comp (BNet.any F (Idx w))
  have both := hb.parallel (BNet.id F (Idx w × Fin r))
  have get := (Control.read_net F w).pull (Sum.map id (Prod.map id ids))
  have mask := (BNet.id F (Port w r)).pair (both.comp get)
  have mark := (masked_local (I := Idx w) (J := Fin r)).bnet F
  have all := test.pair (mask.comp mark)
  convert all.mono (n := 100000 * 2 ^ w * ((1 + w) ^ 4 + r)) (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word, localCost]
    have hp := Nat.one_le_pow w 2 (by decide)
    ring_nf
    omega) using 1
  funext x z
  cases z with
  | inl b =>
    rw [Bool.eq_iff_iff]
    simp only [oneBatch, Sum.elim_inl, Function.comp_apply, decide_eq_true_eq]
    rfl
  | inr z => cases z <;> rfl

private theorem batches_net (q t : ℕ) :
    BNet F (batches (fun v => Control.decode w (v ∘ ids)) q t)
      (10000000 * 2 ^ t * 2 ^ w * ((1 + w) ^ 4 + r)) := by
  have k := BNet.share t (fun j => oneBatch ids q j.val) (fun j => oneBatch_net F ids q j.val)
  let layout : Idx t × (Unit ⊕ Port w r) ≃ Bus (Idx t) (Port w r) :=
    (Equiv.prodSumDistrib _ _ _).trans ((Equiv.prodUnique _ Unit).sumCongr (.refl _))
  have h := k.rename (.refl _) layout
  convert h.mono (n := 10000000 * 2 ^ t * 2 ^ w * ((1 + w) ^ 4 + r)) (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring_nf
    omega) using 1
  funext x z
  cases z <;> rfl

theorem Plan.distribute_net (p : Plan) (F : Type) [Field F] :
    BNet F p.distribute (10000000 * 2 ^ (p.g + p.t) * 2 ^ p.width * ((1 + p.width) ^ 4 + p.layer.r)) := by
  have k := BNet.family p.g (fun _ => batches p.idOf p.q p.t)
    (fun _ => batches_net F p.ids p.q p.t)
  apply (k.rename (.refl _) p.layout).mono
  rw [pow_add]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Grouped transports before batching

The count and width of candidate groups may depend on the fixed
height ratio. The total width actually used must have a uniform bound.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

structure Grid where
  g : ℕ
  b : ℕ
  r : ℕ
  orientation : Fin r
  ids : slots (word b) → Fin r
  disjoint : ∀ i, ids i ≠ orientation

namespace Grid

variable (p : Grid)

abbrev Ports := Idx p.g × Bus (Idx p.b) (Fin p.r)

def block (x : p.Ports → Bool) (i : Idx p.g) (j : Bus (Idx p.b) (Fin p.r)) : Bool := x (i, j)

noncomputable def idOf (v : Fin p.r → Bool) : Idx p.b :=
  Control.decode p.b (v ∘ p.ids)

def Valid (n : ℕ) (x : p.Ports → Bool) : Prop :=
  (∀ i, Aligned p.orientation p.idOf (p.block x i)) ∧
    (∑ i, (marked (p.block x i)).card) ≤ n

open Classical in
noncomputable def close (F : Type) [Field F] (x : p.Ports → Bool) : F :=
  if ∀ i, Closed p.orientation (p.block x i) then 1 else 0

def Open (F : Type) [Field F] (h v m n : ℕ) : Prop :=
  ∃ (b : Wire) (e : p.Ports ≃ slots b) (f : Val (Tagged.inputs h (word v)) → Val b → F),
    Net F (Tagged.inputs h (word v)) b f m ∧
    (∀ x y, f x y ≠ 0 → p.Valid n (bits b y ∘ e)) ∧
    ∀ x, Tagged.tag F h (word v) x () = ∑ y, f x y * p.close F (bits b y ∘ e)

end Grid

def Plan.grid (p : Plan) : Grid :=
  ⟨p.g, p.width, p.layer.r, p.layer.orientation, p.ids, p.disjoint⟩

/-- Configurable core transports in fixed groups, with endpoint
payloads padded to a common chunk length. -/
def GroupProtocol (F : Type) [Field F] : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∃ Y : ℝ, 0 < Y ∧ ∃ B J : ℕ,
    ∀ A : ℕ, J ≤ A → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in Filter.atTop,
      ∃ (p : Grid) (m n : ℕ), (p.b : ℝ) ≤ τ * h ∧ B + 18 ≤ p.b ∧ p.g + p.b ≤ h + B ∧
        Y * (h : ℝ) ^ A ≤ p.r ∧ 1 + p.b ≤ p.r ∧ p.r ≤ h ^ A ∧
        (n : ℝ) * p.r ≤ C * (2 : ℝ) ^ h * (h : ℝ) ^ A ∧
        (m : ℝ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ ∧ p.Open F h (h ^ A) m n

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Sizing the installation

The slack in each group is one batch. Choosing its exponent below the
group height absorbs the excess candidate capacity. Rounding the total
installed width to a power of two costs a factor at most two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

private theorem round_up (n : ℕ) (hn : 0 < n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  cases h : Nat.clog 2 n with
  | zero => simp; omega
  | succ k =>
    have hk : 2 ^ k < n := Nat.pow_lt_of_lt_clog (by omega)
    rw [pow_succ]
    omega

private theorem reserve (g q B h n : ℕ) (hh : g + q ≤ h) (hn : n ≤ 2 ^ (g + (q + 18 + B))) :
    ∃ o, 1 ≤ o ∧ o ≤ g + (B + 36) ∧
      (n + 2 ^ g * 2 ^ q) * 131072 ≤ 2 ^ o * 2 ^ q ∧
      2 ^ o * 2 ^ (q + 18) * 2 ≤ 2 ^ 37 * (n + 2 ^ h) := by
  let N := n + 2 ^ g * 2 ^ q
  let a := Nat.clog 2 N
  have hq : q ≤ a := by
    have h : 2 ^ q ≤ N := by
      apply le_trans _ (Nat.le_add_left ..)
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    simpa [a, Nat.clog_pow] using Nat.clog_mono_right 2 h
  have ha : a ≤ g + (q + 18 + B) + 1 := by
    apply Nat.clog_le_of_le_pow
    have hl : 2 ^ (g + q) ≤ 2 ^ (g + (q + 18 + B)) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_add] at hl
    rw [pow_succ]
    omega
  let o := 17 + a - q
  have he : 2 ^ o * 2 ^ q = 2 ^ 17 * 2 ^ a := by rw [← pow_add, show o + q = 17 + a by omega, pow_add]
  refine ⟨o, by omega, by omega, ?_, ?_⟩
  · rw [he, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide : 1 < 2) N)
  · have hp : N ≤ n + 2 ^ h := by
      unfold N
      rw [← pow_add]
      exact Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) hh) _
    have hs := (round_up N (by unfold N; positivity)).trans (Nat.mul_le_mul_left 2 hp)
    calc
      2 ^ o * 2 ^ (q + 18) * 2 = (2 ^ o * 2 ^ q) * 2 ^ 18 * 2 := by rw [pow_add]; ring
      _ = 2 ^ 36 * 2 ^ a := by rw [he]; ring
      _ ≤ 2 ^ 36 * (2 * (n + 2 ^ h)) := Nat.mul_le_mul_left _ hs
      _ = _ := by ring

theorem Grid.plan_exists (G : Grid) (h B n : ℕ)
    (hb : B + 18 ≤ G.b) (hc : G.g + G.b ≤ h + B) (hr : 1 + G.b ≤ G.r)
    (hn : n ≤ 2 ^ (G.g + G.b)) :
    ∃ p : Plan, p.grid = G ∧ p.layer.l ≤ G.b ∧ G.r ≤ p.layer.u ∧
      p.layer.u ≤ 2 * G.r ∧ p.g + p.t ≤ G.g + B + 36 ∧
      (n + 2 ^ G.g * 2 ^ p.q) * 131072 ≤ 2 ^ p.layer.o * 2 ^ p.q ∧
      2 ^ p.layer.o * 2 ^ p.layer.l * p.layer.u ≤ 2 ^ 37 * (n + 2 ^ h) * G.r := by
  obtain ⟨g, b, r, orientation, ids, disjoint⟩ := G
  change B + 18 ≤ b at hb
  change g + b ≤ h + B at hc
  change 1 + b ≤ r at hr
  obtain ⟨q, hq⟩ : ∃ q, b = q + 18 + B := ⟨b - B - 18, by omega⟩
  subst b
  obtain ⟨o, ho, ht, hcap, hcost⟩ := reserve g q B h n (by omega) hn
  let l : Layer := ⟨q + 18, 2 * r, o, g + (B + 36) - o, B, r, orientation, by omega, ho, by omega⟩
  have he : o + (g + (B + 36) - o) = g + (B + 36) := by omega
  let f : Idx g × Idx (B + 36) ≃ Idx (o + (g + (B + 36) - o)) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin, he, pow_add])
  let p : Plan := ⟨l, g, B + 36, q, f, by change q + 18 + B ≤ B + 36 + q; omega,
    le_rfl, ids, disjoint⟩
  refine ⟨p, rfl, Nat.le_add_right .., ?_, le_rfl, ?_, hcap, ?_⟩
  · change r ≤ 2 * r
    omega
  · exact (Nat.add_assoc g B 36).ge
  · change 2 ^ o * 2 ^ (q + 18) * (2 * r) ≤ 2 ^ 37 * (n + 2 ^ h) * r
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right r hcost

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-! # Converting bounded groups into candidate batches -/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {F : Type} [Field F] {h v m n : ℕ}

theorem Grid.Open.trim {G : Grid} (ho : G.Open F h v m n) :
    G.Open F h v m (min n (2 ^ (G.g + G.b))) := by
  obtain ⟨b, e, f, hf, hx, he⟩ := ho
  refine ⟨b, e, f, hf, fun x y hy => ?_, he⟩
  obtain ⟨ha, hb⟩ := hx x y hy
  refine ⟨ha, le_min hb ?_⟩
  trans ∑ _ : Idx G.g, 2 ^ G.b
  · exact Finset.sum_le_sum (fun _ _ => (Finset.card_le_card (Finset.subset_univ _)).trans_eq
      (Finset.card_fin _))
  · simp [pow_add]

theorem Plan.compile (p : Plan) (ho : p.grid.Open F h v m n)
    (hc : (n + 2 ^ p.g * 2 ^ p.q) * 131072 ≤ 2 ^ p.layer.o * 2 ^ p.q) :
    ∃ m' ≤ m + 10000000 * 2 ^ (p.g + p.t) * 2 ^ p.width * ((1 + p.width) ^ 4 + p.layer.r),
      p.layer.Open F h v m' := by
  obtain ⟨b, e, f, hf, hv, hs⟩ := ho
  have hw (x y) (hne : f x y ≠ 0) : p.Valid (bits b y ∘ e) := by
    obtain ⟨ha, hb⟩ := hv x y hne
    exact ⟨ha, (Nat.mul_le_mul_right _ (Nat.add_le_add_right hb _)).trans hc⟩
  obtain ⟨t, ht, c, i, g, hg, hw, he⟩ := push hf e (p.distribute_net F)
    p.layer.Valid (p.close F) (p.layer.close F) (fun x y hy => p.distributed F _ (hw x y hy))
  exact ⟨t, ht, c, i, g, hg, hw, fun x => (hs x).trans (he x)⟩

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Cost of distributing the transports

The distribution cost can depend on the excess capacity `B`, which
is fixed before the height tends to infinity. The coefficient in the
bound on installed payload is independent of `B`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

private theorem Plan.capacity (p : Plan) : p.layer.o + p.layer.c = p.g + p.t := by
  have he := Fintype.card_congr p.partition
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add] at he
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm

private theorem Plan.expense (p : Plan) {h B A : ℕ} (hh : B + 36 ≤ h) (ha : 4 ≤ A)
    (hg : p.g + p.width ≤ h + B) (ht : p.g + p.t ≤ p.g + B + 36)
    (hu : p.layer.u ≤ 2 * p.layer.r) (hr : p.layer.r ≤ h ^ A) :
    10000000 * 2 ^ (p.g + p.t) * 2 ^ p.width * ((1 + p.width) ^ 4 + p.layer.r) + p.layer.work ≤
      1000000000 * 2 ^ (2 * B + 36) * 2 ^ h * h ^ A := by
  have scale : 2 ^ (p.g + p.t) * 2 ^ p.width ≤ 2 ^ (2 * B + 36) * 2 ^ h := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have big : h ≤ h ^ A := Nat.le_pow (by omega)
  have fourth : (1 + p.width) ^ 4 ≤ 81 * h ^ A := calc
    (1 + p.width) ^ 4 ≤ (3 * h) ^ 4 := Nat.pow_le_pow_left (by omega) _
    _ = 81 * h ^ 4 := by ring
    _ ≤ 81 * h ^ A := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ha)
  have overhead : (1 + p.width) ^ 4 + p.layer.r ≤ 82 * h ^ A := by omega
  have inner : 1 + p.layer.o + p.layer.c + 2 ^ p.width * (1 + p.width + p.layer.u) ≤
      2 ^ p.width * (10 * h ^ A) := by
    have cap := p.capacity
    calc
      _ ≤ 2 ^ p.width * (1 + p.layer.o + p.layer.c) + 2 ^ p.width * (1 + p.width + p.layer.u) :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) _
      _ ≤ _ := by rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have hw : p.layer.work ≤ 2 ^ (p.g + p.t) * 2 ^ p.width * (10 * h ^ A) := by
    unfold Layer.work
    rw [p.capacity, Nat.add_assoc 1 p.layer.l, mul_assoc]
    exact Nat.mul_le_mul_left _ inner
  calc
    _ ≤ 10000000 * 2 ^ (p.g + p.t) * 2 ^ p.width * (82 * h ^ A) + 2 ^ (p.g + p.t) * 2 ^ p.width * (10 * h ^ A) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ overhead) hw
    _ = 820000010 * (2 ^ (p.g + p.t) * 2 ^ p.width) * h ^ A := by ring
    _ ≤ 1000000000 * (2 ^ (2 * B + 36) * 2 ^ h) * h ^ A :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) scale)
    _ = _ := by ring

private theorem Plan.installed (p : Plan) {n h A : ℕ} {C : ℝ}
    (hr : p.layer.r ≤ h ^ A)
    (hn : (n : ℝ) * p.layer.r ≤ C * (2 : ℝ) ^ h * (h : ℝ) ^ A)
    (hc : 2 ^ p.layer.o * 2 ^ p.layer.l * p.layer.u ≤ 2 ^ 37 * (n + 2 ^ h) * p.layer.r) :
    (2 : ℝ) ^ p.layer.o * (2 : ℝ) ^ p.layer.l * p.layer.u ≤ (2 ^ 37 * (C + 1)) * (2 : ℝ) ^ h * (h : ℝ) ^ A := by
  have hv : (p.layer.r : ℝ) ≤ (h : ℝ) ^ A := by exact_mod_cast hr
  calc
    _ ≤ (2 : ℝ) ^ 37 * (n + (2 : ℝ) ^ h) * p.layer.r := by exact_mod_cast hc
    _ = (2 : ℝ) ^ 37 * (n * p.layer.r + (2 : ℝ) ^ h * p.layer.r) := by ring
    _ ≤ (2 : ℝ) ^ 37 * (C * (2 : ℝ) ^ h * (h : ℝ) ^ A + (2 : ℝ) ^ h * (h : ℝ) ^ A) := by gcongr
    _ = _ := by ring

private theorem absorb {s h A m D : ℕ} {ζ : ℝ} (hh : 0 < h)
    (hm : (m : ℝ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ (ζ / 2))
    (hD : (↑(D + 2) : ℝ) ≤ (h : ℝ) ^ (ζ / 2)) (hcost : s ≤ m + D * 2 ^ h * h ^ A) :
    (s : ℝ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ := by
  have hd : (D : ℝ) + 2 ≤ (h : ℝ) ^ (ζ / 2) := by simpa using hD
  have hsquared : (h : ℝ) ^ (ζ / 2) + D ≤ (h : ℝ) ^ ζ := by
    have he : (h : ℝ) ^ ζ = (h : ℝ) ^ (ζ / 2) * (h : ℝ) ^ (ζ / 2) := by
      rw [← Real.rpow_add (by exact_mod_cast hh), add_halves]
    rw [he]
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  calc
    (s : ℝ) ≤ m + (D : ℝ) * (2 : ℝ) ^ h * (h : ℝ) ^ A := by exact_mod_cast hcost
    _ ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * ((h : ℝ) ^ (ζ / 2) + D) := by linarith only [hm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquared (by positivity)

theorem open_of_groups {F : Type} [Field F] (hg : GroupProtocol F) : OpenProtocol F := by
  obtain ⟨C, hC, H⟩ := hg
  refine ⟨2 ^ 37 * (C + 1), by linarith, fun τ hτ => ?_⟩
  obtain ⟨Y, hY, B, J, hJ⟩ := H τ hτ
  refine ⟨Y, hY, J + 4, fun A hA ζ hζ => ?_⟩
  let D := 1000000000 * 2 ^ (2 * B + 36)
  have grow := (tendsto_rpow_atTop (half_pos hζ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hJ A (by omega) _ (half_pos hζ), grow.eventually_ge_atTop (D + 2 : ℕ),
    Filter.eventually_ge_atTop (B + 36)] with h Hh hD hh
  obtain ⟨G, m, n, hl, hb, hcap, hwidth, hr, hr', hn, hm, ho⟩ := Hh
  obtain ⟨p, rfl, hle, hu, hu', hpt, hp, hv⟩ :=
    G.plan_exists h B (min n (2 ^ (G.g + G.b))) hb hcap hr (min_le_right ..)
  obtain ⟨s, hs, hs'⟩ := p.compile ho.trim hp
  refine ⟨p.layer, s, le_trans (by exact_mod_cast hle) hl,
    hwidth.trans (by exact_mod_cast hu), ?_, ?_, hs'⟩
  · apply p.installed hr' hn
    exact hv.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (min_le_left ..) _)))
  · have hcost : s + p.layer.work ≤ m + D * 2 ^ h * h ^ A := by
      have he := p.expense hh (by omega : 4 ≤ A) hcap hpt hu' hr'
      exact (Nat.add_le_add_right hs _).trans ((Nat.add_assoc ..).le.trans (Nat.add_le_add_left he m))
    exact absorb (by omega) hm hD hcost

end OAI.LinearAlgebra.MatrixExponent.Install
end
