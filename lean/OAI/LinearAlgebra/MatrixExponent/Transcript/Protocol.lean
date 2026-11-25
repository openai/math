import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.HistorySpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.StringOrder
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Physical
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Names

/-! # Charging the original ordinal of every declared message -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
open Coloring
variable {X : Type} {k H : ℕ} (S : Spec X k H) {h c B : ℕ}

theorem ordered_cost (hm : S.messages ≤ h ^ c)
    (hf : ∀ g j, S.guesses g j ≤ B * 2 ^ j.val) :
    (Strings.Position S.messages).width ≤ 1 + c * Nat.clog 2 h ∧
      ∀ g j, S.withOrder.guesses g j ≤ (B + 2 * (k + 1) * (1 + c * Nat.clog 2 h)) * 2 ^ j.val := by
  have hu : (Strings.Position S.messages).width ≤ 1 + c * Nat.clog 2 h := by
    rw [Format.width_addr]
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    have h₁ : h ^ c ≤ 2 ^ (c * Nat.clog 2 h) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    have h₂ := Nat.two_pow_pos (c * Nat.clog 2 h)
    rw [pow_add, pow_one]
    omega
  refine ⟨hu, fun g j => ?_⟩
  have hv : Fintype.card (Slot S.messages (2 ^ j.val) k) ≤ (k + 1) * (2 * 2 ^ j.val) := calc
    _ = ∑ _ : Slot S.messages (2 ^ j.val) k, 1 := by simp
    _ ≤ ∑ i : Slot S.messages (2 ^ j.val) k, capacity i :=
      Finset.sum_le_sum fun i _ => Nat.two_pow_pos i.1.val
    _ ≤ _ := sum_capacity ..
  change S.guesses g j + Fintype.card (S.OrderBits j) ≤ _
  rw [Fintype.card_prod]
  exact (Nat.add_le_add (hf g j) (Nat.mul_le_mul hv hu)).trans_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

/-! # Recovering the local message list in the original order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
variable {X : Type} {k H : ℕ} (S : Spec X k H)
    {n : S.Who → ℕ} (j : S.Who → Level k) (row : Strings.Rows S.key n)
    (p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val)) (hm : ∀ i, n i ≤ S.messages)
    (f : (i : S.Who) → Fin (S.guesses i.1 (j i)) → Bool)

private theorem declares :
    S.withOrder.declared (S.ordered j row p hm f) = Strings.code row p := by
  funext l i
  rcases i with ⟨⟨g, v⟩, t⟩
  dsimp only [declared, ordered, literal, message, Sum.elim_inr]
  exact (S.withStrings.Msg l).code.symm_apply_apply (Strings.code row p l ⟨⟨g, v⟩, t⟩)

private theorem lookup (i : S.Who) (b : Fin (S.guesses i.1 (j i)) ⊕ S.OrderBits (j i)) :
    (S.ordered j row p hm f i.1 i.2).2 (.inl (S.orderPins i.1 (j i) b)) =
      Sum.elim (f i) (fun a : S.OrderBits (j i) =>
        (Strings.Position S.messages).code (Strings.order row p hm i a.1) a.2) b := by
  let F : Fin (S.guesses i.1 (j i)) ⊕ S.OrderBits (j i) → Bool :=
    Sum.elim (f i) (fun a => (Strings.Position S.messages).code (Strings.order row p hm i a.1) a.2)
  exact congrArg F ((S.orderPins i.1 (j i)).symm_apply_apply b)

private theorem numbered : S.ordinals (S.ordered j row p hm f) = Strings.order row p hm := by
  funext i v
  apply (Strings.Position S.messages).code.symm_apply_eq.mpr
  funext b
  exact lookup S j row p hm f i (.inr (v, b))

/-- Local order and the original guesses can be recovered independently
of the direction, key and tape comparison performed by the channel. -/
theorem ordered_correct :
    (∀ i t, S.recover (S.ordered j row p hm f) i t =
      if ht : t < n i then some (row i ⟨t, ht⟩) else none) ∧
    (Channels.good (S.withOrder.declared (S.ordered j row p hm f)) ↔
      Match.good (fun i : Σ s, Fin (n s) => (true, row i.1 i.2))) ∧
    ∀ (i : S.Who) t, (S.ordered j row p hm f i.1 i.2).2 (.inl (S.orderPins i.1 (j i) (.inl t))) = f i t := by
  refine ⟨?_, ?_, ?_⟩
  · intro i t
    unfold recover
    rw [declares, numbered]
    exact Strings.restore_code row p hm i t
  · rw [declares]
    exact Strings.good_iff row p
  · exact fun i t => lookup S j row p hm f i (.inl t)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

/-!
# Realizing a charged adaptive transcript

The hypotheses refer to the local program, its records and their
charges. The processor slots, private matches, dictionary gates and
global message checks are constructed in the proof. The polynomial
exponent on the processor overhead does not depend on the exponent
bounding the local addresses, time fields and transition circuits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Filter

variable {F : Type} [Field F]

private theorem pad_cost (Y t V j r : ℕ) (hY : 0 < Y) (hr : j ≤ r) :
    t * Y ^ j * V ≤ t * Y ^ r * V :=
  Nat.mul_le_mul_right V (Nat.mul_le_mul_left t (Nat.pow_le_pow_right hY hr))

theorem realizes {τ : ℝ} (ht : 0 < τ) (wide : Radix.WideTag F) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ q : ℕ, ∀ᶠ h : ℕ in atTop,
      ∀ (K : Type) [Field K] [Algebra F K] (X : Type) [Fintype X] (k H U V B : ℕ)
        (S : Spec X k H) (D : System S U) (W : List Bool → K),
        (B : ℝ) ≤ (Real.log h) ^ q → D.Bounded V h c B →
        ∃ m, WideWeight K (10 * (U + 1)) (labels U W) (D.tensor W) m ∧
          (m : ℝ) ≤ (h : ℝ) ^ τ * V + S.size * (h : ℝ) ^ C₀ := by
  obtain ⟨C, C₀, p⟩ := prices wide ht (c + 40)
  refine ⟨C₀, fun q => ?_⟩
  let r := max (q + 2) 10000
  filter_upwards [eventual_overhead c q, p r] with h he cost K _ _ X _ k H U V B S D W hB ok
  obtain ⟨hh, hl, hh'⟩ := he
  obtain ⟨t, hw, estimate, hm⟩ := cost
  let Y := overhead h c B
  obtain ⟨hY, hlog⟩ := hh' B hB
  have hBY : B ≤ Y := by unfold Y overhead; omega
  have hcap : 100 + k + Nat.clog 2 (h + 1) + c ≤ Y := by have := ok.height; unfold Y overhead; omega
  have hY' : 0 < Y := by omega
  have hfit : D.Bounded V h c Y :=
    { ok with
      height := ok.height.trans hBY
      guesses := fun i j => (ok.guesses i j).trans (Nat.mul_le_mul_right _ hBY)
      addresses := ok.addresses.trans hBY
      control := fun i j => (ok.control i j).trans hBY }
  obtain ⟨hp, hch⟩ := ok.capacities hh (by omega) (by omega)
  refine ⟨D.cost V h C t, ?_, ?_⟩
  · rw [← D.realization W ok]
    exact D.physical_net W (estimate K) ok.key ok.names hp hch
  · have hsize := hfit.estimate hh hcap (show 1 ≤ t by omega) C
    have ha : D.cost V h C t ≤ t * Y ^ r * (V + S.size * h ^ (C + (c + 40))) := by
      rw [← add_assoc]
      exact hsize.trans (pad_cost Y t _ 10000 r hY' (le_max_right ..))
    refine (Nat.cast_le.mpr ha).trans (hm Y S.size V ?_)
    exact hlog.trans (pow_le_pow_right₀ hl (le_max_left _ _))

theorem realizes_named {τ : ℝ} (ht : 0 < τ) (wide : Radix.WideTag F) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ q : ℕ, ∀ᶠ h : ℕ in atTop,
      ∀ (K : Type) [Field K] [Fintype K] [Algebra F K] (x : Wire) (k H U V B e : ℕ)
        (S : Spec (slots x) k H) (D : System S U) (W : List Bool → K),
        (B : ℝ) ≤ (Real.log h) ^ q → D.Bounded V h c B → Fintype.card K ≤ h ^ e →
        let v := 5 + Nat.clog 2 h * (8 * e + 1)
        let f := fun a (_ : Val .unit) => D.tensor W (bits x a)
        ∃ (m : ℕ) (G : Diagram K x .unit) (name : G.V → Fin (2 ^ v)) (decode : Fin (2 ^ v) → Table K),
          Wide K (10 * (U + 1)) (labels U W) x .unit f m ∧
          (m : ℝ) ≤ (h : ℝ) ^ τ * V + S.size * (h : ℝ) ^ C₀ ∧
          G.eval = f ∧ G.cost = m ∧ (∀ t, G.arity t ≤ 10 * (U + 1)) ∧ ∀ t, decode (name t) = G.table t := by
  obtain ⟨C, hC⟩ := realizes ht wide c
  refine ⟨C, fun q => ?_⟩
  filter_upwards [hC q, eventually_ge_atTop 1] with h hh hp K _ _ _ x k H U V B e S D W hB ok hF v f
  obtain ⟨m, hm, hsize⟩ := hh K _ k H U V B S D W hB ok
  obtain ⟨t, ht', net⟩ := hm x (Equiv.refl _)
  obtain ⟨G, name, decode, he, hcost, har, hname⟩ := named_gates hp ok.dictionary hF net
  exact ⟨t, G, name, decode, net, (Nat.cast_le.mpr ht').trans hsize, he, hcost, har, hname⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end
