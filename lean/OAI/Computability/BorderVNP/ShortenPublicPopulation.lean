import OAI.Computability.BorderVNP.PackedLookup
import OAI.Computability.BorderVNP.ShortenSeedIntervals

/-! # Counting moved cable widths from sparse public rows

The physical row name stays fixed while its charge bit, width and moved bin are
inputs. A row contributes once even if the cable's slots are shared by several
local computations. An unused row or uncharged cable contributes zero regardless
of its address and payload. One query is made for each legal bin, including empty
bins. No query or source row is allocated for each individual cable bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Crossing ParseBatchSort PackedHistogram VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin
open scoped BigOperators

variable {U σ : Type*} {A : Type} {k w : ℕ}

/-- Pin selection from a preceding moved-row frame. Distinct fields may share wires. -/
structure Pins (U σ : Type*) (k w : ℕ) where
  /-- Set only on an occupied, charged row. -/
  active : U → σ
  /-- Numerical address of the moved bin. -/
  key : U → Fin k → σ
  /-- Binary cable width. -/
  width : U → Fin w → σ

variable (p : Pins U σ k w)

private def weight (u : U) (j : Fin w) : Expr σ :=
  .and (.input (p.active u)) (.input (p.width u j))

private theorem zeroValue : ∀ v, value (fun _ : Fin v => false) = 0
  | 0 => rfl
  | v+1 => by simp [value, zeroValue v]

private theorem weight_value (x : σ → Bool) (u : U) :
    wordValue x (weight p u) = if x (p.active u) then value (x ∘ p.width u) else 0 := by
  cases h : x (p.active u) <;> simp [weight,wordValue,StatementCircuit.Expr.eval,h,
    Function.comp_def,zeroValue]

variable [Fintype U] [Fintype A] [Fintype σ]

/-- One sparse batch of additions. Source and query rows are padded jointly. -/
noncomputable def frame (code : A ↪ Fin (2^k)) : Frame σ (A × Fin w) :=
  queries (layout U A) (fun u j => .input (p.key u j)) (weight p) (fun a => fixed (code a))

/-- Gate bound per padded lane in the two sorts and segmented addition. -/
def laneCost (b k w : ℕ) : ℕ :=
  (k+1+w)*3 + ((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) +
    w*(60*k+16*w+33) + b^2*(24*(w+b)+1)

/-- The sorting width is logarithmic in the number of real rows and legal bins.
Only the linear prefactor depends directly on that row count. -/
theorem frame_size (code : A ↪ Fin (2^k)) :
    let n := Fintype.card U + Fintype.card A
    (frame p code).size ≤ 2*(n+1)*laneCost (Nat.clog 2 n) k w := by
  intro n
  have pad : 2^(Nat.clog 2 n) ≤ 2*(n+1) := by
    by_cases hn : n = 0
    · simp [hn]
    · have := layout_size U A (Nat.pos_of_ne_zero hn)
      change 2^(Nat.clog 2 n) < 2*n at this
      omega
  exact (queries_size (layout U A) (fun u j => .input (p.key u j)) (weight p)
    (fun a => fixed (code a)) 3 (by decide) (fun _ _ => by change 1 ≤ 3; decide)
    (fun _ _ => le_rfl) (fun _ _ => by change 1 ≤ 3; decide)).trans (Nat.mul_le_mul_right _ pad)

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) (bin : N.Edge → Option A)
    (slot : N.Edge ↪ U) (code : A ↪ Fin (2^k)) (x : σ → Bool)

omit [Fintype U] [Fintype A] [Fintype σ] in
/-- The relation between the physical moved rows and the mathematical network.
Only a live row has to hold a legal address or a correct width. -/
structure Represents : Prop where
  /-- Exactly the edges assigned a bin are active in their reserved row. -/
  active : ∀ e, x (p.active (slot e)) = (bin e).isSome
  /-- The remaining reserved row names are inactive. -/
  absent : ∀ u, u ∉ Set.range slot → x (p.active u) = false
  /-- The numerical address names the bin of the moved cable. -/
  address : ∀ e a, bin e = some a → value (x ∘ p.key (slot e)) = (code a).val
  /-- The active cable's word gives its full width. -/
  width : ∀ e a, bin e = some a → value (x ∘ p.width (slot e)) = N.width e

omit [Fintype A] [Fintype σ] in
private theorem bucket_eq (h : Represents p N bin slot code x) (t : ℕ) :
    (∑ u, if wordValue x (fun j => .input (p.key u j)) = t then wordValue x (weight p u) else 0) =
      ∑ e, if (bin e).any (fun a => decide ((code a).val = t)) then N.width e else 0 := by
  classical
  let g (u : U) := if wordValue x (fun j => .input (p.key u j)) = t then wordValue x (weight p u) else 0
  change ∑ u, g u = _
  rw [← Finset.sum_subset (s₁ := Finset.univ.map slot) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := g) (by
      intro u _ hu
      have hr : u ∉ Set.range slot := by simpa using hu
      simp [g, weight_value, h.absent u hr])]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  cases hb : bin e with
  | none => simp [g,weight_value,h.active,hb]
  | some a =>
    have hk : wordValue x (fun j => .input (p.key (slot e) j)) = (code a).val := h.address e a hb
    simp [g,weight_value,h.active,hb,hk,h.width e a hb]

/-- Every output word equals the bin's integral population in the interval allocator.
The word-fit hypothesis only concerns legal bins. It permits unused numerical keys
and arbitrary stale data at every inactive slot. -/
theorem frame_count (h : Represents p N bin slot code x)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (a : A) :
    value (fun j => (frame p code).eval x (a,j)) = SeedIntervals.count N bin a := by
  classical
  let ks (u : U) (j : Fin k) : Expr σ := .input (p.key u j)
  have atCode (b : A) :
      (∑ u, if wordValue x (ks u) = (code b).val then wordValue x (weight p u) else 0) =
        SeedIntervals.count N bin b := by
    rw [SeedIntervals.count_eq_sum, bucket_eq p N bin slot code x h]
    apply Finset.sum_congr rfl
    intro e _
    cases he : bin e <;> simp [Fin.val_inj, code.injective.eq_iff]
  have hf (t : ℕ) : (∑ u, if wordValue x (ks u) = t then wordValue x (weight p u) else 0) < 2^w := by
    by_cases ht : ∃ b, (code b).val = t
    · obtain ⟨b,rfl⟩ := ht
      exact (atCode b).trans_lt (fits b)
    · rw [bucket_eq p N bin slot code x h]
      have hz (e : N.Edge) : (bin e).any (fun a => decide ((code a).val = t)) = false := by
        cases bin e with
        | none => rfl
        | some a => simp [show (code a).val ≠ t from fun eq => ht ⟨a,eq⟩]
      simp [hz]
  rw [frame, queries_value _ _ _ _ _ hf, fixed_value]
  exact atCode a

/-- One expanded-size bound supplies all required per-bin word capacities. -/
theorem frame_count_of_total (h : Represents p N bin slot code x)
    (fits : (∑ e, N.width e) < 2^w) (a : A) :
    value (fun j => (frame p code).eval x (a,j)) = SeedIntervals.count N bin a := by
  classical
  apply frame_count p N bin slot code x h _ a
  intro b
  rw [SeedIntervals.count_eq_sum]
  apply lt_of_le_of_lt _ fits
  exact Finset.sum_le_sum fun _ _ => by split <;> omega

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
