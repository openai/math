import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.OrderSpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Machine

/-! # Exact charges and dictionary emissions of a logical history -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open scoped Classical

variable {X K : Type} [Field K] {k H U n : ℕ} {S : Spec X k H}

/-- The charge used in the theorem is the sum of rounded capacities.
This inequality converts an ordinary bound on the sum of local charges. -/
theorem Spec.charge_bound (a : S.History) (cost : (g : Level k) → Fin (S.P g) → ℕ) (V : ℕ)
    (pos : ∀ g p, 0 < cost g p)
    (level : ∀ g p, (a g p).1.val = Nat.clog 2 (cost g p)) (total : ∑ g, ∑ p, cost g p ≤ V) :
    ∑ g, ∑ p, 2 ^ (a g p).1.val ≤ 2 * V := by
  calc
    _ ≤ ∑ g, ∑ p, 2 * cost g p := Finset.sum_le_sum fun g _ =>
      Finset.sum_le_sum fun p _ => by rw [level]; exact pow_clog_le_twice (pos g p)
    _ ≤ _ := by simp only [← Finset.mul_sum]; exact Nat.mul_le_mul_left 2 total

/-- Every permitted issuance has a unique placement. If the
output buffer contains its tokens, the weight is the product
of precisely the emitted dictionary values. -/
theorem System.emissions (D : System S U) (W : List Bool → K) (x : X → Bool)
    (g : Level k) (p : Fin (S.P g)) (a : S.Record g) (strings : Fin n → List Bool)
    (accepted : D.record x g p a (.inl ()) = true)
    (cost : ∑ i, RAM.callCharge (strings i) ≤ 2 ^ a.1.val) (bound : ∀ i, (strings i).length ≤ U) :
    ∃! y : RAM.Calls (2 ^ a.1.val) U → Fin (n + 1), RAM.Issuance strings y ∧
      ((∀ t, (RAM.token t.1.val).code.symm (fun j => D.record x g p a (.inr ⟨t, j⟩)) =
       RAM.tokens strings y t) → D.value W x g p a = ∏ i, W (strings i)) := by
  obtain ⟨y, hy, hu⟩ := RAM.unique_issuance (U := U) strings cost
  refine ⟨y, ⟨hy, fun he => ?_⟩, fun v h => hu _ h.1⟩
  change (if D.record x g p a (.inl ()) then ∏ t : RAM.Calls (2 ^ a.1.val) U,
    RAM.tokenValue U W t.1.val ((RAM.token t.1.val).code.symm (fun j => D.record x g p a (.inr ⟨t, j⟩)))
    else 0) = _
  rw [ite_eq_left accepted]
  simp_rw [he]
  exact hy.product bound W

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Placement preserves the messages of the processor records -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec

variable {X : Type} {k H V : ℕ} {S : Spec X k H}

/-- Every processor carries its own ports to its assigned slot. Vacant slots
have no active messages. -/
theorem Places.messages {x : X → Bool} {a : S.History} {b : S.Tape V}
    (hs : S.Places x a b) : Channels.good (S.issued b) ↔ Channels.good (S.declared a) := by
  obtain ⟨y, hy, h₀, h₁⟩ := hs.spec
  have seat (g : Level k) (p : Fin (S.P g)) :
      ∃ i, y g ⟨(a g p).1, i⟩ = p.castSucc := by
    obtain ⟨⟨j, i⟩, hi, _⟩ := hy.occurs g p
    have hj : (a g p).1 = j := hy.level g ⟨j, i⟩ p hi
    subst j
    exact ⟨i, hi⟩
  let slot (g : Level k) (p : Fin (S.P g)) : Slot (S.P g) V k := ⟨(a g p).1, (seat g p).choose⟩
  have owns (g : Level k) (p : Fin (S.P g)) : y g (slot g p) = p.castSucc :=
    (seat g p).choose_spec
  have hi (g : Level k) : Function.Injective (slot g) := by
    intro p q h
    apply Fin.castSucc_injective
    rw [← owns g p, ← owns g q, h]
  let site : S.Who ↪ S.Site V :=
    Function.Embedding.sigmaMap (.refl _) (fun g => ⟨slot g, hi g⟩)
  let e (l : Level k) : S.Real a l ↪ S.Reserved V l :=
    site.sigmaMap (fun _ => .refl _)
  apply Channels.good_congr (S.declared a) (S.issued b) e
  · rintro l ⟨⟨g, p⟩, v⟩
    obtain ⟨f, ha, hb⟩ := h₁ g (slot g p) p (owns g p)
    have hf : (a g p).2 = f := eq_of_heq (Sigma.mk.inj ha).2
    change S.message (b g (slot g p) ∘ Sum.inr) l v = S.message (a g p).2 l v
    rw [hb, hf]
    rfl
  · rintro l ⟨⟨g, i⟩, v⟩ ha
    have hn : y g i ≠ Fin.last (S.P g) := by
      intro hv
      change (S.message (b g i ∘ Sum.inr) l v).1 = true at ha
      rw [h₀ g i hv] at ha
      cases ha
    obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hn
    have he : i = slot g p := (hy.occurs g p).unique hp.symm (owns g p)
    subst i
    exact ⟨⟨⟨g, p⟩, v⟩, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

/-- Cost of routing a batch of records, including padding and header sorting. -/
def Prices (K : Type) [Field K] (h C W : ℕ) : Prop :=
  ∀ H N t : ℕ, H ≤ h ^ 2 → N ≤ 2 ^ (h ^ 3) → ∃ j n m : ℕ,
    N ≤ 2 ^ j ∧ t ≤ n ∧ Radix.Tag K j (H + j + n + 2) m ∧
    m + 100000 * 2 ^ j * (n + (1 + H + j) * (j + 1) ^ 2) ≤ W * (N + 1) * (t + h ^ C)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Cost of checking a family of payload formats -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Channels

open Coloring Install
open scoped Classical

variable {F G : Type} [Field F] {h C W : ℕ}

private def test (A D : Format) (I : Type) (x : I × (Match.format A D).pins → Bool) : F :=
  if Match.good (fun i => (Match.format A D).code.symm (fun p => x (i, p))) then 1 else 0

private theorem single (A D : Format) (I : Type) [Fintype I]
    (prices : Prices F h C W) (hK : A.width ≤ h ^ 2) (hN : Fintype.card I ≤ 2 ^ (h ^ 3)) :
    Weight F (test A D I) (W * (Fintype.card I + 1) * (D.width + h ^ C)) := by
  obtain ⟨j, n, m, hj, hn, ht, hm⟩ := prices _ _ D.width hK hN
  apply (Match.weight A D hj hn ht).mono
  refine le_trans ?_ hm
  gcongr
  decide

variable (A : Format) (D : G → Format) (E : G → Type)

private abbrev Head := Sigma E × (Match.format A (.addr 0)).pins

private def pick : Head A E → Pins A D E
  | (⟨g, i⟩, .inl p) => ⟨g, i, .inl p⟩
  | (⟨g, i⟩, .inr (.inl p)) => ⟨g, i, .inr (.inl p)⟩
  | (⟨g, i⟩, .inr (.inr (.inl p))) => ⟨g, i, .inr (.inr (.inl p))⟩
  | (_, .inr (.inr (.inr p))) => p.elim

variable [Fintype G]

private theorem test_all (x : Pins A D E → Bool) :
    (∏ g, test (F := F) A (D g) (E g) (fun p => x ⟨g, p⟩)) *
        test A (.addr 0) (Sigma E) (x ∘ pick A D E) =
      if good (decode A D E x) then 1 else 0 := by
  simp only [test, Function.comp_apply, good_iff]
  let r := decode A D E x
  change (∏ g, if Match.good (r g) then (1 : F) else 0) *
      (if Match.good (header r) then 1 else 0) =
    if (∀ g, Match.good (r g)) ∧ Match.good (header r) then 1 else 0
  by_cases hg : ∀ g, Match.good (r g)
  · simp [hg]
  · obtain ⟨g, hf⟩ := not_forall.mp hg
    rw [Finset.prod_eq_zero (Finset.mem_univ g) (ite_eq_right hf)]
    simp [hg]

private theorem format_width (P Q : Format) : (Match.format P Q).width = 2 + P.width + Q.width := by
  simp only [Match.format, Format.width_pair]
  rw [Format.width_bit]
  omega

variable [∀ g, Fintype (E g)]

private theorem sizes :
    Fintype.card (Pins A D E) ≤ (2 + A.width) * Fintype.card (Sigma E) +
      ∑ g, (1 + Fintype.card (E g)) * (D g).width := by
  unfold Pins
  simp only [Fintype.card_sigma, Fintype.card_prod, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  change Fintype.card (E g) * (Match.format A (D g)).width ≤ _
  rw [format_width]
  ring_nf
  omega

private theorem sum_prices (h C W : ℕ) :
    (∑ g, W * (Fintype.card (E g) + 1) * ((D g).width + h ^ C)) =
      W * ((Fintype.card G + Fintype.card (Sigma E)) * h ^ C +
        ∑ g, (1 + Fintype.card (E g)) * (D g).width) := by
  have each (g) : W * (Fintype.card (E g) + 1) * ((D g).width + h ^ C) =
      W * ((1 + Fintype.card (E g)) * h ^ C + (1 + Fintype.card (E g)) * (D g).width) := by ring
  simp_rw [each]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib]
  simp [Fintype.card_sigma]

theorem weight (prices : Prices F h C W) (hK : A.width ≤ h ^ 2)
    (hN : Fintype.card (Sigma E) ≤ 2 ^ (h ^ 3)) :
    Weight F (fun x => if good (decode A D E x) then 1 else 0) (cost A D E h C W) := by
  have count (g : G) : Fintype.card (E g) ≤ 2 ^ (h ^ 3) := by
    apply le_trans _ hN
    exact Fintype.card_le_of_injective (Sigma.mk g) (fun _ _ eq => eq_of_heq (Sigma.mk.inj eq).2)
  have checks := Weight.sigma_prod (fun g => test A (D g) (E g))
    (fun g => single A (D g) (E g) prices hK (count g))
  have all := (single A (.addr 0) (Sigma E) prices hK hN).pull (pick A D E)
  have net := checks.mul all
  rw [← funext (test_all (F := F) A D E)]
  apply net.mono
  have hp := sizes A D E
  have hh : Fintype.card (Head A E) = Fintype.card (Sigma E) * (2 + A.width) := by
    rw [show Fintype.card (Head A E) = Fintype.card (Sigma E) * (Match.format A (.addr 0)).width
      from Fintype.card_prod _ _, format_width, Format.width_addr, add_zero]
  change 5 * Fintype.card (Pins A D E) + _ + (Fintype.card (Pins A D E) + 2 * Fintype.card (Head A E) + _) ≤ _
  rw [hh, sum_prices, Format.width_addr]
  unfold cost
  ring_nf at hp ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Channels
end

/-! # Counts and costs of the local and global checks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring Finset
variable {X : Type} {k H U : ℕ} {S : Spec X k H}

abbrev Spec.Hidden (S : Spec X k H) (V : ℕ) := Σ i : S.Site V, S.Input i.1 i.2.1
abbrev Spec.pool (S : Spec X k H) (V : ℕ) (g : Level k) := S.P g + Fintype.card (Slot (S.P g) V k)

namespace System
variable (D : System S U) (g j : Level k)

def slotCost :=
  (1 + Fintype.card (S.Input g j) + 2 ^ j.val + (RAM.ceiling U + 1) * 2 ^ j.val)*
    (100 + j.val + D.width + (D.verify g j).size + Nat.clog 2 (Fintype.card (S.Input g j) + 1)+
      Nat.clog 2 (Fintype.card (Output (2 ^ j.val) U) + 1)) ^ 212

def cost (V h C W : ℕ) [Fintype X] :=
  10000 * (1 + Fintype.card X + Fintype.card (S.Hidden V) +
    (∑ i : S.Site V, D.slotCost i.1 i.2.1) +
    (k + 1) * S.size * (100 + H) ^ 10 +
    (∑ g, W * (S.pool V g + 1) * ((S.supply g).width + h ^ C)) +
    Channels.cost S.key S.body (S.Reserved V) h C W)

end System
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Population of the private and message channels -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Finset
variable {X : Type} {k H U : ℕ}

namespace Spec
variable (S : Spec X k H) (V : ℕ)

theorem site_count : Fintype.card (S.Site V) ≤ (k + 1) * S.size := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ g, (k + 1) * S.P g := sum_le_sum fun g _ => card_slots (S.P g) V k
    _ = _ := by rw [← mul_sum]

theorem pool_count (g : Level k) : S.pool V g ≤ (k + 2) * S.P g := calc
  _ ≤ S.P g + (k + 1) * S.P g := Nat.add_le_add_left (card_slots (S.P g) V k) _
  _ = _ := by ring

end Spec

namespace System.Bounded
variable [Fintype X] {S : Spec X k H} {D : System S U} {V h c B : ℕ}

/-- Each site reserves at most the message limit in each length class. -/
theorem population (ok : D.Bounded V h c B) :
    Fintype.card (Σ l, S.Reserved V l) ≤ (k + 1) ^ 2 * S.size * h ^ c := by
  have hl (l : Level k) : Fintype.card (S.Reserved V l) ≤ (k + 1) * S.size * h ^ c := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : S.Site V, h ^ c := by
        apply sum_le_sum
        intro i _
        rw [Fintype.card_fin]
        exact (min_le_left _ _).trans ok.count
      _ = Fintype.card (S.Site V) * h ^ c := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (S.site_count V)
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Level k, (k + 1) * S.size * h ^ c := sum_le_sum fun l _ => hl l
    _ = _ := by simp only [sum_const, card_univ, Level, Fintype.card_fin, Nat.nsmul_eq_mul]; ring

/-- The population bounds use the processor names and the message
limit, so no upper bound on the charge budget V is needed. -/
theorem capacities (ok : D.Bounded V h c B) (hh : 100 ≤ h) (hk : k ≤ h) (hc : c ≤ h) :
    (∀ g, S.pool V g ≤ 2 ^ (h ^ 3)) ∧ Fintype.card (Σ l, S.Reserved V l) ≤ 2 ^ (h ^ 3) := by
  let a := 2 ^ (h ^ 2)
  have ha : 0 < a := by unfold a; positivity
  have hn : k + 2 ≤ a := (show k + 2 ≤ h ^ 2 by nlinarith).trans Nat.lt_two_pow_self.le
  have hk' : k + 1 ≤ a := by omega
  have hp (g : Level k) : S.P g ≤ a :=
    (S.named g).le.trans (Nat.pow_le_pow_right (by decide) ok.names)
  have hs : S.size ≤ a * a := calc
    _ ≤ ∑ _ : Level k, a := sum_le_sum fun g _ => hp g
    _ = (k + 1) * a := by simp [Level]
    _ ≤ _ := Nat.mul_le_mul_right _ hk'
  have hm : h ^ c ≤ a := calc
    _ ≤ h ^ h := Nat.pow_le_pow_right (by omega) hc
    _ ≤ (2 ^ h) ^ h := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = _ := by unfold a; rw [← pow_mul, pow_two]
  have he : a ^ 5 ≤ 2 ^ (h ^ 3) := by
    unfold a
    rw [← pow_mul, show h ^ 3 = h ^ 2 * h by ring]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  constructor
  · intro g
    calc
      _ ≤ (k + 2) * S.P g := S.pool_count V g
      _ ≤ a * a := Nat.mul_le_mul hn (hp g)
      _ ≤ a ^ 5 := by rw [← pow_two]; exact Nat.pow_le_pow_right ha (by decide)
      _ ≤ _ := he
  · calc
      _ ≤ (k + 1) ^ 2 * S.size * h ^ c := ok.population
      _ ≤ a ^ 2 * (a * a) * a := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hk' _) hs) hm
      _ = a ^ 5 := by ring
      _ ≤ _ := he

end System.Bounded
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Charges for matching headers and payloads

The number of records controls header overhead. Payloads instead use
the sum of the dyadic capacities. At each width a slot reserves at
most twice its own capacity in payload units.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Finset

variable {X : Type} {k H U : ℕ}

namespace Spec
variable (S : Spec X k H) (V : ℕ)

theorem site_capacity : (∑ i : S.Site V, capacity i.2) ≤ (k + 1) ^ 2 * (2 * V) := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _ : Level k, (k + 1) * (2 * V) := sum_le_sum (fun g _ => sum_capacity (S.P g) V k)
    _ = _ := by simp [pow_two, mul_assoc]

theorem payload_capacity (l : Level k) :
    Fintype.card (S.Reserved V l) * 2 ^ l.val ≤ 4 * (k + 1) ^ 2 * V := by
  rw [Fintype.card_sigma, sum_mul]
  calc
    _ ≤ ∑ i : S.Site V, 2 * capacity i.2 := by
      apply sum_le_sum
      intro i _
      rw [Fintype.card_fin]
      exact (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
    _ ≤ 2 * ((k + 1) ^ 2 * (2 * V)) := by rw [← mul_sum]; exact Nat.mul_le_mul_left 2 (S.site_capacity V)
    _ = _ := by ring

end Spec

namespace System.Bounded

variable [Fintype X] {S : Spec X k H} {D : System S U} {V h c B W : ℕ}
variable (hD : D.Bounded V h c B)

include hD

private theorem payload_cost :
    (∑ l, (1 + Fintype.card (S.Reserved V l)) * (S.body l).width) ≤ 24 * (k + 1) ^ 3 * V := by
  calc
    _ ≤ ∑ _ : Level k, 24 * (k + 1) ^ 2 * V := by
      apply sum_le_sum
      intro l _
      have hl : 2 ^ l.val ≤ 2 * V :=
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ l.isLt)).trans hD.longest
      have hv : V ≤ (k + 1) ^ 2 * V := Nat.le_mul_of_pos_left _ (by positivity)
      calc
        _ ≤ (1 + Fintype.card (S.Reserved V l)) * (4 * 2 ^ l.val) :=
          Nat.mul_le_mul_left _ (hD.payload l)
        _ = 4 * (2 ^ l.val + Fintype.card (S.Reserved V l) * 2 ^ l.val) := by ring
        _ ≤ 4 * (2 * ((k + 1) ^ 2 * V) + 4 * (k + 1) ^ 2 * V) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (hl.trans (Nat.mul_le_mul_left 2 hv))
            (S.payload_capacity V l))
        _ = _ := by ring
    _ = _ := by simp; ring

private theorem header_cost (hh : 1 ≤ h) (C : ℕ) :
    (Fintype.card (Level k) + Fintype.card (Σ l, S.Reserved V l) + 1) * (1 + h ^ C + S.key.width) ≤
      9 * (k + 1) ^ 2 * S.size * h ^ (C + c + 2) := by
  have ht : k + 1 ≤ (k + 1) ^ 2 * S.size * h ^ c := calc
    _ ≤ (k + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ (k + 1) ^ 2 * S.size := Nat.le_mul_of_pos_right _ hD.processors
    _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hp := hD.population
  have ha : Fintype.card (Level k) + Fintype.card (Σ l, S.Reserved V l) + 1 ≤
      3 * ((k + 1) ^ 2 * S.size * h ^ c) := by rw [Fintype.card_fin]; omega
  have hb : 1 + h ^ C + S.key.width ≤ 3 * h ^ (C + 2) := by
    have h₁ : 1 ≤ h ^ (C + 2) := one_le_pow₀ hh
    have h₂ : h ^ C ≤ h ^ (C + 2) := pow_le_pow_right₀ hh (by omega)
    have h₃ : S.key.width ≤ h ^ (C + 2) := hD.key.trans (pow_le_pow_right₀ hh (by omega))
    omega
  calc
    _ ≤ 3 * ((k + 1) ^ 2 * S.size * h ^ c) * (3 * h ^ (C + 2)) := Nat.mul_le_mul ha hb
    _ = _ := by rw [show C + c + 2 = c + (C + 2) by omega, pow_add h c]; ring

/-- The exponent is fixed independent of the charging parameters. -/
theorem channels_small (hh : 100 ≤ h) (hb : 100 + k + Nat.clog 2 (h + 1) + c ≤ B)
    (hw : 1 ≤ W) (C : ℕ) :
    Channels.cost S.key S.body (S.Reserved V) h C W ≤ W * B ^ 7 * (V + S.size * h ^ (C + c + 40)) := by
  have hB : 100 ≤ B := by omega
  have hh' : 1 ≤ h := by omega
  have h₂ : (k + 1) ^ 2 ≤ B ^ 3 := (Nat.pow_le_pow_left hD.height _).trans
    (pow_le_pow_right₀ (by omega) (by decide))
  have h₃ : (k + 1) ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left hD.height _
  have hp : h ^ (C + c + 2) ≤ h ^ (C + c + 40) := pow_le_pow_right₀ hh' (by omega)
  have hnum : 48000000 ≤ B ^ 4 := (show 48000000 ≤ 100 ^ 4 by decide).trans
    (Nat.pow_le_pow_left hB 4)
  have hsmall : 48000000 * B ^ 3 ≤ B ^ 7 := calc
    _ ≤ B ^ 4 * B ^ 3 := Nat.mul_le_mul_right _ hnum
    _ = B ^ 7 := by rw [← pow_add]
  unfold Channels.cost
  calc
    _ ≤ 1000000 * (2 * W) * (9 * (k + 1) ^ 2 * S.size * h ^ (C + c + 2) + 24 * (k + 1) ^ 3 * V) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (Nat.add_le_add (hD.header_cost hh' C) hD.payload_cost)
    _ ≤ 1000000 * (2 * W) * (24 * B ^ 3 * S.size * h ^ (C + c + 40) + 24 * B ^ 3 * V) := by
      gcongr
      omega
    _ = W * (48000000 * B ^ 3) * (V + S.size * h ^ (C + c + 40)) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsmall)

theorem estimate_channels (hh : 100 ≤ h) (hb : 100 + k + Nat.clog 2 (h + 1) + c ≤ B)
    (hw : 1 ≤ W) (C : ℕ) :
    Channels.cost S.key S.body (S.Reserved V) h C W ≤ W * B ^ 6000 * (V + S.size * h ^ (C + c + 40)) :=
  (hD.channels_small hh hb hw C).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (pow_le_pow_right₀ (by omega : 1 ≤ B) (by decide : 7 ≤ 6000))))

end System.Bounded
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Uniform prices for padded routing batches -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Filter

private theorem size (N k : ℕ) (hk : 1 ≤ k) (hN : N ≤ 2 ^ k) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ N ≤ 2 ^ j ∧ 2 ^ j ≤ 2 * (N + 1) := by
  by_cases hb : N ≤ 1
  · exact ⟨1, le_rfl, hk, by omega, by omega⟩
  have hj := Nat.le_pow_clog (by decide : 1 < 2) N
  have hj₁ : 1 ≤ Nat.clog 2 N := by
    by_contra! h
    rw [show Nat.clog 2 N = 0 by omega, pow_zero] at hj
    omega
  exact ⟨_, hj₁, Nat.clog_le_of_le_pow hN, hj,
    (pow_clog_le_twice (by omega : 0 < N)).trans (by omega)⟩

private theorem padded {K : Type} [Field K] (h a M : ℕ) (hh : 1 ≤ h)
    (ht : ∀ j v : ℕ, 1 ≤ j → j ≤ h ^ 3 → (h ^ 3) ^ a ≤ v →
      ∃ m ≤ M * (2 ^ j * v), Radix.Tag K j v m) :
    Prices K h (3 * a + 9) (10 * M + 2600000) := by
  intro H N t hH hN
  have hh3 : 1 ≤ h ^ 3 := one_le_pow₀ hh
  obtain ⟨j, hj, hj', hNj, hjN⟩ := size N (h ^ 3) hh3 hN
  let n := t + h ^ (3 * a + 9)
  have hH' : H ≤ h ^ 3 := hH.trans (pow_le_pow_right₀ hh (by decide))
  have h9 : h ^ 9 ≤ n :=
    (pow_le_pow_right₀ hh (by omega : 9 ≤ 3 * a + 9)).trans (Nat.le_add_left _ _)
  have h3 : h ^ 3 ≤ n := (pow_le_pow_right₀ hh (by decide : 3 ≤ 9)).trans h9
  have hv : (h ^ 3) ^ a ≤ n := by
    rw [← pow_mul]
    exact (pow_le_pow_right₀ hh (by omega : 3 * a ≤ 3 * a + 9)).trans (Nat.le_add_left _ _)
  have hdata : H + j + n + 2 ≤ 5 * n := by omega
  have hheads : (1 + H + j) * (j + 1) ^ 2 ≤ 12 * n := calc
    _ ≤ (3 * h ^ 3) * (2 * h ^ 3) ^ 2 := by gcongr <;> omega
    _ = 12 * h ^ 9 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h9
  have htotal : n + (1 + H + j) * (j + 1) ^ 2 ≤ 13 * n := by omega
  obtain ⟨m, hm, hm'⟩ := ht j (H + j + n + 2) hj hj' (by omega)
  refine ⟨j, n, m, hNj, Nat.le_add_right _ _, hm', ?_⟩
  calc
    _ ≤ M * (2 ^ j * (H + j + n + 2)) + 100000 * 2 ^ j * (n + (1 + H + j) * (j + 1) ^ 2) := Nat.add_le_add_right hm _
    _ ≤ M * ((2 * (N + 1)) * (5 * n)) + 100000 * (2 * (N + 1)) * (13 * n) := by gcongr
    _ = (10 * M + 2600000) * (N + 1) * n := by ring

private theorem small {τ ζ : ℝ} (hz : 3 * ζ < τ) (q : ℕ) (D : ℝ) :
    ∀ᶠ h : ℕ in atTop, D * (h : ℝ) ^ (3 * ζ) * (Real.log h) ^ q ≤ (h : ℝ) ^ τ := by
  have he := (isLittleO_log_rpow_rpow_atTop (q : ℝ) (sub_pos.mpr hz)).const_mul_left D
  filter_upwards [eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually he.eventuallyLE]
    with h hh hb
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  rw [Real.rpow_natCast, Real.norm_of_nonneg (Real.rpow_nonneg hh'.le _)] at hb
  calc
    _ = D * (Real.log h) ^ q * (h : ℝ) ^ (3 * ζ) := by ring
    _ ≤ (h : ℝ) ^ (τ - 3 * ζ) * (h : ℝ) ^ (3 * ζ) :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans hb) (by positivity)
    _ = _ := by rw [← Real.rpow_add hh', sub_add_cancel]

/-- The two polynomial exponents are fixed before the logarithmic loss is specified.
The same price works for every batch and every extension field. -/
theorem prices {F : Type} [Field F] (wide : Radix.WideTag F) {τ : ℝ}
    (hτ : 0 < τ) (c : ℕ) :
    ∃ C C₀ : ℕ, ∀ q : ℕ, ∀ᶠ h : ℕ in atTop, ∃ W : ℕ, 100 ≤ W ∧
      (∀ (K : Type) [Field K] [Algebra F K], Prices K h C W) ∧
      ∀ B P V : ℕ, (B : ℝ) ≤ (Real.log h) ^ q →
        (W * B ^ q * (V + P * h ^ (C + c)) : ℕ) ≤ (h : ℝ) ^ τ * V + P * (h : ℝ) ^ C₀ := by
  let ζ := min τ 1 / 4
  have hz : 0 < ζ := by unfold ζ; positivity
  have hz' : 3 * ζ < min τ 1 := by unfold ζ; linarith [lt_min hτ (by norm_num : (0 : ℝ) < 1)]
  obtain ⟨a, L, hL, ht⟩ := Assembly.wide_cost wide hz
  let C := 3 * a + 9
  let D := 10 * L + 2600010
  refine ⟨C, C + c + 1, fun q => ?_⟩
  filter_upwards [eventually_ge_atTop 1, small hz' (q * q) D] with h hh hs
  have hh' : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  let M := ⌈L * ((h ^ 3 : ℕ) : ℝ) ^ ζ⌉₊
  let W := 10 * M + 2600000
  refine ⟨W, by unfold W; omega, ?_, ?_⟩
  · intro K _ _
    apply padded h a M hh
    intro j v hj hj' hv
    obtain ⟨m, hm, htag⟩ := ht (h ^ 3) j v hj hj' hv
    exact ⟨m, hm, Assembly.tag_map htag⟩
  intro B P V hB
  have hm : (M : ℝ) ≤ L * (h : ℝ) ^ (3 * ζ) + 1 := calc
    _ ≤ L * ((h ^ 3 : ℕ) : ℝ) ^ ζ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ = _ := by rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]; norm_num
  have hw : (W : ℝ) ≤ D * (h : ℝ) ^ (3 * ζ) := by
    have hpow : 1 ≤ (h : ℝ) ^ (3 * ζ) := Real.one_le_rpow hh' (by positivity)
    simp only [W, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, D]
    linarith only [hm, hpow]
  have hB' : (B : ℝ) ^ q ≤ (Real.log h) ^ (q * q) := by rw [pow_mul]; gcongr
  have hmul : (W : ℝ) * (B : ℝ) ^ q ≤ (h : ℝ) ^ (min τ 1) :=
    (mul_le_mul hw hB' (by positivity) ((Nat.cast_nonneg _).trans hw)).trans hs
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
  calc
    _ ≤ (h : ℝ) ^ (min τ 1) * (V + (P : ℝ) * (h : ℝ) ^ (C + c)) :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    _ ≤ _ := by
      rw [mul_add, pow_succ, mul_comm ((h : ℝ) ^ (min τ 1)) ((P : ℝ) * _), mul_assoc]
      have h₁ := Real.rpow_le_rpow_of_exponent_le hh' (min_le_left τ 1)
      have h₂ := Real.rpow_le_rpow_of_exponent_le hh' (min_le_right τ 1)
      rw [Real.rpow_one] at h₂
      gcongr

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Absorbing the framing and control overhead of the bit-RAM -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Filter

def overhead (h c B : ℕ) := 100 + 2 * B + Nat.clog 2 (h + 1) + c

private theorem log_bound (h : ℕ) (hh : 1 < h) :
    (Nat.clog 2 (h + 1) : ℝ) ≤ 1 + Real.log h / Real.log 2 := by
  let j := Nat.clog 2 (h + 1)
  have ht : (2 : ℕ) ^ j.pred ≤ h :=
    Nat.le_of_lt_succ (Nat.pow_pred_clog_lt_self (b := 2) (by decide) (by omega))
  have hp : (2 : ℝ) ^ j.pred ≤ h := by exact_mod_cast ht
  have hj := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hj
  have ha := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hj
  have he : (j : ℝ) = j.pred + 1 := by
    exact_mod_cast (Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < h + 1))).symm
  change (j : ℝ) ≤ _
  linarith

theorem eventual_overhead (c q : ℕ) : ∀ᶠ h : ℕ in atTop, 100 ≤ h ∧ 1 ≤ Real.log h ∧
    ∀ B : ℕ, (B : ℝ) ≤ (Real.log h) ^ q →
      overhead h c B ≤ h ∧ (overhead h c B : ℝ) ≤ (Real.log h) ^ (q + 2) := by
  have hg := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (104 + c + 1 / Real.log 2)
  have hb := isLittleO_log_rpow_rpow_atTop ((q + 2 : ℕ) : ℝ) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop 100, hg, tendsto_natCast_atTop_atTop.eventually hb.eventuallyLE]
    with h hh hl hu
  have hpos : 0 ≤ 1 / Real.log 2 := by positivity
  let l := Real.log h
  change 104 + c + 1 / Real.log 2 ≤ l at hl
  have one : 1 ≤ l := by linarith [Nat.cast_nonneg (α := ℝ) c]
  rw [Real.rpow_natCast, Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hu
  have hv : l ^ (q + 2) ≤ h := (le_abs_self _).trans hu
  refine ⟨hh, one, fun B hB => ?_⟩
  have hbig : 1 ≤ l ^ (q + 1) := one_le_pow₀ one
  have hp : l ≤ l ^ (q + 1) := by rw [pow_succ]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ one)
  have he := log_bound h (by omega)
  have hcost : (overhead h c B : ℝ) ≤ l ^ (q + 2) := calc
    _ ≤ (101 + c) + 2 * l ^ q + (1 / Real.log 2) * l := by
      unfold overhead
      push_cast
      rw [one_div_mul_eq_div]
      linarith
    _ ≤ (104 + c + 1 / Real.log 2) * l ^ (q + 1) := by
      have h₁ := mul_le_mul_of_nonneg_left hbig (show (0 : ℝ) ≤ 101 + c by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hp hpos
      have h₃ : l ^ q ≤ l ^ (q + 1) := pow_le_pow_right₀ one (by omega)
      linarith
    _ ≤ l * l ^ (q + 1) := mul_le_mul_of_nonneg_right hl (by positivity)
    _ = _ := (pow_succ' ..).symm
  exact ⟨Nat.cast_le.mp (hcost.trans hv), hcost⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Checking private reads by matching a pool with fixed senders -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Private

open Coloring Install
open scoped Classical

variable {S : Type} {P H : ℕ} {D : Format}

private def pool (hP : P < 2 ^ H) (f : Fin P → D.obj) (g : S → (format D H).obj) :
    Fin P ⊕ S → (Match.format (.addr H) D).obj
  | .inl p => (true, false, Fin.castLE hP.le p, f p)
  | .inr s => ((g s).1, true, (g s).2)

private theorem pool_good (hP : P < 2 ^ H) (f : Fin P → D.obj) (g : S → (format D H).obj) :
    Match.good (pool hP f g) ↔ good f g := by
  constructor
  · rintro ⟨hu, hm⟩
    constructor
    · intro p
      obtain ⟨q|s, h⟩ := hm (.inl p) rfl
      · cases congrArg (fun x => x.2.1) h
      have hs : (g s).1 = true := congrArg Prod.fst h
      have hk : (g s).2.1.val = p.val := congrArg (fun x => x.2.2.1.val) h
      refine ⟨s, ⟨hs, hk⟩, fun t ht => ?_⟩
      exact Sum.inr.inj (hu (.inr t) (.inr s) ht.1 hs rfl (Fin.ext (ht.2.trans hk.symm)))
    · intro s hs
      obtain ⟨p|t, h⟩ := hm (.inr s) hs
      · exact ⟨p, congrArg (fun x => x.2.2.1.val) h.symm, congrArg (fun x => x.2.2.2) h.symm⟩
      · cases congrArg (fun x => x.2.1) h
  · rintro ⟨hu, hm⟩
    constructor
    · rintro (p|s) (q|t) hi hk hd hb
      · exact congrArg Sum.inl (Fin.ext (congrArg (fun k : B H => k.val) hb))
      · cases hd
      · cases hd
      · obtain ⟨p, hp, _⟩ := hm s hi
        exact congrArg Sum.inr ((hu p).unique ⟨hi, hp⟩ ⟨hk, (congrArg Fin.val hb).symm.trans hp⟩)
    · rintro (p|s) hi
      · obtain ⟨s, ⟨hs, hp⟩, _⟩ := hu p
        obtain ⟨q, hq, hf⟩ := hm s hs
        have : q = p := Fin.ext (hq.symm.trans hp)
        subst q
        exact ⟨.inr s, Prod.ext hs (Prod.ext rfl (Prod.ext (Fin.ext hp) hf))⟩
      · obtain ⟨p, hp, hf⟩ := hm s hi
        exact ⟨.inl p, Prod.ext rfl (Prod.ext rfl (Prod.ext (Fin.ext hp.symm) hf.symm))⟩

/-- Private reads add fixed name and direction bits to the pool before matching. -/
theorem weight {F S : Type} [Field F] [Fintype S] (D : Format) {P H j n m : ℕ}
    (hP : P < 2 ^ H) (hc : P + Fintype.card S ≤ 2 ^ j) (hn : D.width ≤ n)
    (ht : Radix.Tag F j (H + j + n + 2) m) :
    Weight F (fun x : Pins S P H D → Bool =>
      if good (fun p => D.code.symm (fun k => x (.inl (p, k))))
        (fun s => (format D H).code.symm (fun k => x (.inr (s, k)))) then 1 else 0)
      (m + 21000 * 2 ^ j * (n + (1 + H + j) * (j + 1) ^ 2)) := by
  let X := Pins S P H D
  let A := Match.format (.addr H) D
  let Y := (Fin P ⊕ S) × A.pins
  let f (x : X → Bool) (p : Fin P) := D.code.symm (fun k => x (.inl (p, k)))
  let g (x : X → Bool) (s : S) := (format D H).code.symm (fun k => x (.inr (s, k)))
  let prep (x : X → Bool) (q : Y) := A.code (pool hP (f x) (g x) q.1) q.2
  have dep : Depends prep 1 := by
    have hf (p : Fin P) (k : D.pins) (x : X → Bool) :
        D.code (f x p) k = x (.inl (p, k)) := congrFun (D.code.apply_symm_apply _) k
    have hg (s : S) (k : (format D H).pins) (x : X → Bool) :
        (format D H).code (g x s) k = x (.inr (s, k)) :=
      congrFun ((format D H).code.apply_symm_apply _) k
    rintro ⟨p|s, k⟩
    · rcases k with k|k|k|k
      · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
      · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
      · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
      · refine ⟨{.inl (p, k)}, by simp, fun x y h => ?_⟩
        exact (hf p k x).trans ((h _ (by simp)).trans (hf p k y).symm)
    · rcases k with k|k|k
      · refine ⟨{.inr (s, .inl k)}, by simp, fun x y h => ?_⟩
        exact (hg s (.inl k) x).trans ((h _ (by simp)).trans (hg s (.inl k) y).symm)
      · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
      · refine ⟨{.inr (s, .inr k)}, by simp, fun x y h => ?_⟩
        exact (hg s (.inr k) x).trans ((h _ (by simp)).trans (hg s (.inr k) y).symm)
  have hw := Match.weight (I := Fin P ⊕ S) (j := j) (F := F) (m := m) (.addr H) D
    (by simpa using hc) hn (by simpa using ht)
  have net := (dep.bnet F).weight hw
  have he (x : X → Bool) : Match.good (fun i => A.code.symm (fun k => prep x (i, k))) ↔
      good (f x) (g x) := by
    simp only [prep, Equiv.symm_apply_apply]
    exact pool_good hP _ _
  simp only [Function.comp_def, A, he, Format.width_addr] at net
  apply net.mono
  have hY : Fintype.card Y = (P + Fintype.card S) * (2 + H + D.width) := by
    rw [show Fintype.card Y = Fintype.card (Fin P ⊕ S) * A.width from Fintype.card_prod _ _,
      Fintype.card_sum, Fintype.card_fin]
    simp only [A, Match.format, Format.width_pair, Format.width_addr]
    change _ * (1 + (1 + (H + D.width))) = _
    ring
  have hv : Fintype.card X ≤ Fintype.card Y := by
    rw [hY, show Fintype.card X = Fintype.card (Fin P × D.pins) +
      Fintype.card (S × (format D H).pins) from Fintype.card_sum,
      Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    change P * D.width + Fintype.card S * (format D H).width ≤ _
    simp only [format, Format.width_pair, Format.width_addr]
    change P * D.width + Fintype.card S * (1 + (H + D.width)) ≤ _
    ring_nf
    omega
  have hz : Fintype.card Y ≤ 2 ^ j * (2 + H + n) := by
    rw [hY]
    exact Nat.mul_le_mul hc (Nat.add_le_add_left hn _)
  simp only [localCost]
  ring_nf at hz ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Private
end

section
/-! # Local tape predicates for canonical placement -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec

variable {X : Type} {k H V : ℕ} (S : Spec X k H)

/-- A tape checks private inputs, names, bucket ordering and all unused bits. -/
structure Proper (x : X → Bool) (b : S.Tape V) : Prop where
  privateMatch : ∀ g, Private.good (S.data x g) (fun i => S.badge (b g i))
  ids : ∀ g i, (S.badge (b g i)).2.1.val ≤ S.P g ∧
    (S.badge (b g i)).1 = decide ((S.badge (b g i)).2.1.val < S.P g)
  sorted : ∀ g j, Monotone (fun i => (S.badge (b g ⟨j, i⟩)).2.1)
  vacant : ∀ g i, (S.badge (b g i)).1 = false → ∀ t, S.mask g i.1 t = true → b g i t = false

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

/-! # Factors on the fixed transcript tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring
open scoped Classical

variable {X K : Type} [Field K] {k H V U : ℕ} (S : Spec X k H)

/-- Public checks are independent of the dictionary. The local factors
also enforce zero padding for vacant slots. -/
structure Spec.Public (x : X → Bool) (b : S.Tape V) : Prop where
  privateMatch : ∀ g, Private.good (S.data x g) (fun i => S.badge (b g i))
  ids : ∀ g i, (S.badge (b g i)).2.1.val ≤ S.P g ∧
    (S.badge (b g i)).1 = decide ((S.badge (b g i)).2.1.val < S.P g)
  sorted : ∀ g j, Monotone (fun i => (S.badge (b g ⟨j, i⟩)).2.1)
  messages : Channels.good (S.issued b)

variable {S} (D : System S U) (W : List Bool → K)

abbrev System.actor (g j : Level k) := activeValue W (D.output g j) (S.on g j) (S.mask g j)

def System.physical (x : X → Bool) (b : S.Tape V) : K :=
  if S.Public x b then ∏ g, ∏ i : Slot (S.P g) V k, D.actor W g i.1 (b g i) else 0

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end
