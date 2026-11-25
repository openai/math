import OAI.Computability.BorderVNP.PackedStableCableOffset
import OAI.Computability.BorderVNP.ShortenPublicPopulation

/-! # Restored offsets for active and inactive sparse public slots

Inactive slots have zero weight in the scan regardless of the contents of their
address and width registers. A separate retained input wire can still read a
frozen cable's physical width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Crossing PackedHistogram Packing.Names ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical
open private weight weight_value from OAI.Computability.BorderVNP.ShortenPublicPopulation

variable {m k w : ℕ} {σ : Type*} [Fintype σ] (p : Pins (Fin m) σ k w)

/-- The real row's unchanged ordinal inside the padded power-of-two batch. -/
def paddedSlot (m : ℕ) : Fin m ↪ Fin (2^Nat.clog 2 m) := Fin.castLEEmb (Nat.le_pow_clog (by decide) _)

private def rawExpr (a : Stable.Input (Nat.clog 2 m) k w) : Expr σ :=
  if h : a.1.val < m then
    a.2.elim (fun j => .input (p.key ⟨a.1.val,h⟩ j)) (fun j => weight p ⟨a.1.val,h⟩ j)
  else .const false

private noncomputable def rawFrame : Frame σ (Stable.Input (Nat.clog 2 m) k w) :=
  (Frame.initial id).step (rawExpr p)

/-- The exact same-bin offsets, returned at each real source row in its original order. -/
noncomputable def offsets : Frame σ (Fin m × Fin w) :=
  ((Stable.frame (Nat.clog 2 m) k w).subst (rawFrame p)).select (fun uj => (paddedSlot m uj.1,uj.2))

/-- Gate cost for the active mask, two padded sorts, and the exclusive arithmetic scan. -/
theorem offsets_size : let b := Nat.clog 2 m
    (offsets p).size ≤ 1 + 2^b * ((k+w)*3 + ((w+b)+1+k) +
      b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) + b^2*(24*(w+b)+1)) := by
  intro b
  have he (q : Stable.Input (Nat.clog 2 m) k w) : (rawExpr p q).size ≤ 3 := by
    rcases q with ⟨u,j|j⟩ <;> simp only [rawExpr] <;> split <;> simp [weight, StatementCircuit.Expr.size]
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (rawExpr p) 3 he
  simp only [Stable.Input,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Frame.initial_size,zero_add] at h
  change (rawFrame p).size ≤ 2^b*(k+w)*3 at h
  rw [offsets, Frame.select_size, Frame.subst_size]
  exact (Nat.add_le_add h (Stable.frame_size b k w)).trans (by ring_nf; rfl)

private theorem raw_eval (x : σ → Bool) (q : Stable.Input (Nat.clog 2 m) k w) :
    (rawFrame p).eval x q = (rawExpr p q).eval x := by
  have he : (Frame.initial (id : σ → σ)).eval x = x := funext (Frame.initial_eval id x)
  simp only [rawFrame, Frame.step_eval, he]

private theorem raw_key (x : σ → Bool) (i : Fin m) :
    Stable.key ((rawFrame p).eval x) (paddedSlot m i) = value (x ∘ p.key i) := by
  simp [Stable.key, raw_eval, rawExpr, paddedSlot, i.isLt, StatementCircuit.Expr.eval, Function.comp_def]

private theorem raw_weight (x : σ → Bool) (i : Fin m) :
    Stable.weight ((rawFrame p).eval x) (paddedSlot m i) =
      if x (p.active i) then value (x ∘ p.width i) else 0 := by
  simpa [Stable.weight, raw_eval, rawExpr, paddedSlot, i.isLt, wordValue] using weight_value p x i

private theorem padding_zero (x : σ → Bool) (u : Fin (2^Nat.clog 2 m)) (hu : ¬ u.val < m) :
    Stable.weight ((rawFrame p).eval x) u = 0 := by
  have zero : ∀ n, value (fun _ : Fin n => false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [value] using ih
  simp [Stable.weight, raw_eval, rawExpr, hu, StatementCircuit.Expr.eval, zero]

variable {A : Type} {D : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) (bin : N.Edge → Option A) (slot : N.Edge ↪ Fin m) (code : A ↪ Fin (2^k))

/-- The populated sparse input describes the same bin totals before and after power-of-two padding.
The predicate selects either all rows or the rows strictly before one cable. -/
private theorem selected_sum (x : σ → Bool) (h : Represents p N bin slot code x) (t : ℕ)
    (pick : Fin (2^Nat.clog 2 m) → Bool) :
    let y := (rawFrame p).eval x
    (∑ u, if Stable.key y u = t ∧ pick u = true then Stable.weight y u else 0) =
      ∑ e, if (bin e).any (fun a => decide ((code a).val = t)) && pick (paddedSlot m (slot e)) then N.width e else 0 := by
  intro y
  symm
  let r := slot.trans (paddedSlot m)
  apply Fintype.sum_of_injective r r.injective
  · intro u hu
    by_cases hr : u.val < m
    · let v : Fin m := ⟨u.val,hr⟩
      have he : paddedSlot m v = u := Fin.ext rfl
      have hv : v ∉ Set.range slot := fun ⟨e,hh⟩ => hu ⟨e, (congrArg (paddedSlot m) hh).trans he⟩
      rw [← he, raw_weight p x v, h.absent v hv]
      simp
    · rw [padding_zero p x u hr]
      simp
  · intro e
    change _ = if Stable.key y (paddedSlot m (slot e)) = t ∧ pick (paddedSlot m (slot e)) = true
      then Stable.weight y (paddedSlot m (slot e)) else 0
    rw [raw_key, raw_weight, h.active]
    cases hb : bin e with
    | none => simp
    | some a => simp [h.address e a hb, h.width e a hb]

/-- The active masked source gives exactly the dense allocator's offset. Unused rows and
frozen uncharged widths may contain arbitrary stale bits. Only legal bin totals must fit. -/
theorem offsets_dense (x : σ → Bool) (h : Represents p N bin slot code x)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (e : N.Edge) (a : A) (he : bin e = some a) :
    value (fun j => (offsets p).eval x (slot e,j)) =
      SeedIntervals.cableOffset (denseLayout N slot) (bin ∘ (denseSlot N slot).symm) a (denseSlot N slot e) := by
  let y := (rawFrame p).eval x
  have hb (t : ℕ) : bucket (Stable.key y) (Stable.weight y) t =
      ∑ e, if (bin e).any (fun a => decide ((code a).val = t)) then N.width e else 0 := by
    simpa only [y,bucket,and_true,Bool.and_true] using selected_sum p N bin slot code x h t (fun _ => true)
  have hf (t : ℕ) : bucket (Stable.key y) (Stable.weight y) t < 2^w := by
    rw [hb]
    by_cases ha : ∃ a, (code a).val = t
    · obtain ⟨v,rfl⟩ := ha
      have hsame (g : N.Edge) : (bin g).any (fun a => decide ((code a).val = (code v).val)) = decide (bin g = some v) := by
        cases hh : bin g <;> simp [Fin.val_inj, code.injective.eq_iff]
      simpa only [SeedIntervals.count_eq_sum, hsame, decide_eq_true_eq] using fits v
    · have hn (g : N.Edge) : (bin g).any (fun a => decide ((code a).val = t)) = false := by
        cases bin g with
        | none => rfl
        | some a => simp [show (code a).val ≠ t from fun hv => ha ⟨a,hv⟩]
      simp [hn]
  simp only [offsets, Frame.select_eval, Frame.subst_eval]
  rw [Stable.frame_value y hf, denseOffset]
  have hkey : Stable.key y (paddedSlot m (slot e)) = (code a).val := (raw_key p x _).trans (h.address e a he)
  rw [hkey]
  have hh := selected_sum p N bin slot code x h (code a).val (fun u => decide (u < paddedSlot m (slot e)))
  simp only [decide_eq_true_eq] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro g _
  cases hg : bin g <;> simp [Fin.val_inj, code.injective.eq_iff, paddedSlot]

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
