import OAI.Computability.BorderVNP.PackedDeckScoreSum
import OAI.Computability.BorderVNP.PackedDeckScoreMath

/-! # Exact conditional-expectation score circuits at one deck refinement

The shifted addresses for a candidate are supplied by the deck multiplier on
the earlier shared frame. All tile rows are accessed through batched weighted
queries. Each relative bin and each of the boundedly many children costs one
pair of histogram batches and a linear number of binary multiplications.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckScore

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork CoverDeck
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {B G H : Type*} [Fintype B] [Fintype G] [Fintype H] [DecidableEq H]
variable {m k w : ℕ}

/-- Nonnegative prior and candidate counts, plus all translated residue addresses. -/
abbrev Input (B G H : Type*) (m k w : ℕ) :=
  (Bool × B × G × Fin w) ⊕ (Fin m × H × Fin k)

/-- Physical count in a bin before the translation is applied. -/
def counts (x : Input B G H m k w → Bool) (side : Bool) (t : B) (g : G) : ℕ :=
  value fun j => x (.inl (side,t,g,j))

/-- Numerical label of a translated residue, supplied by the deck multiplier. -/
def translated (x : Input B G H m k w → Bool) (i : Fin m) (v : H) : ℕ :=
  value fun j => x (.inr (i,v,j))

/-- Sufficient accumulator width for all translated dot products in a score. -/
abbrev scoreBits (B H : Type*) [Fintype B] [Fintype H] (w : ℕ) := sumBits (B × H) (2*w)

private noncomputable def queryWord (index : H ↪ Fin (2^k)) (side : Bool) (i : Fin m) (v : H) :
    Fin k → Expr (Input B G H m k w) :=
  if side then fun j => .input (.inr (i,v,j)) else fixed (index v)

/-- The source labels and all unshifted query labels are hardwired. Shifted query labels
are input wires, so a variable candidate does not require a quadratic translation table. -/
noncomputable def part (π : G → H) (index : H ↪ Fin (2^k)) (side : Bool) (i : Fin m) (t : B) :
    Frame (Input B G H m k w) (H × Fin w) :=
  queries (layout G H) (fun g => fixed (index (π g))) (fun g j => .input (.inl (side,t,g,j))) (queryWord index side i)

omit [DecidableEq H] in
theorem part_size (π : G → H) (index : H ↪ Fin (2^k)) (side : Bool) (i : Fin m) (t : B) :
    (part (w := w) π index side i t).size ≤ queryCost (batchBits G H) k w := by
  apply (queries_size _ _ _ _ 1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_).trans
  · simp [queryCost, batchBits]
  · intro h j
    cases side <;> exact le_rfl

/-- One translated or unshifted histogram, in the shared physical residue order. -/
theorem part_value [Mul H] (π : G → H) (index : H ↪ Fin (2^k)) (side : Bool) (i : Fin m) (t : B)
    (x : Input B G H m k w → Bool) (c : H)
    (haddr : ∀ v, translated x i v = (index (c*v)).val)
    (fits : ∀ v, histogram π (counts x side t) v < 2^w) (v : H) :
    value (fun j => (part π index side i t).eval x (v,j)) =
      histogram π (counts x side t) (if side then c*v else v) := by
  let vs (g : G) (j : Fin w) : Expr (Input B G H m k w) := .input (.inl (side,t,g,j))
  have src g : wordValue x (vs g) = counts x side t g := rfl
  have eq (h : H) : (∑ g, if (index (π g)).val = (index h).val then wordValue x (vs g) else 0) =
      histogram π (counts x side t) h := by
    simp [histogram, fiber, Finset.sum_filter, src, Fin.val_inj, index.injective.eq_iff]
  have hf (a : ℕ) : (∑ g, if wordValue x (fixed (index (π g))) = a then wordValue x (vs g) else 0) < 2^w := by
    simp only [fixed_value]
    by_cases h : ∃ v, (index v).val = a
    · obtain ⟨u,rfl⟩ := h
      exact (eq u).trans_lt (fits u)
    · have hn (g) : (index (π g)).val ≠ a := fun he => h ⟨π g,he⟩
      simp [hn]
  change value (fun j => (queries (layout G H) _ vs (queryWord index side i)).eval x (v,j)) = _
  rw [queries_value _ _ _ _ _ hf]
  have hq : wordValue x (queryWord index side i v) = (index (if side then c*v else v)).val := by
    cases side with
    | false => exact fixed_value x _
    | true => exact haddr v
  simp only [hq, fixed_value]
  exact eq _

/-- Explicit cost of one child: two histogram batches per relative bin, one binary
multiplication per residue and bin, and one wide shared sum. -/
def childCost (B G H : Type*) [Fintype B] [Fintype G] [Fintype H] (k w C e : ℕ) :=
  1 + (2*Fintype.card B)*queryCost (batchBits G H) k w +
    (1 + Fintype.card (B × H)*(C*(w+1)^e) + queryCost (batchBits (B × H) Unit) 0 (scoreBits B H w))

variable [Group G] [Group H]

/-- For all input-dependent children, compute their integer numerators in independent output
words. Child and residue address wires from an earlier frame can be spliced in once. -/
theorem exists_scores_uniform :
    ∃ C e : ℕ, ∀ (B : Type*) (G : Type*) (H : Type*)
      [Fintype B] [Fintype G] [Fintype H] [DecidableEq H] [Group G] [Group H] (m k w : ℕ) (π : G →* H) (index : H ↪ Fin (2^k)),
      ∃ f : Frame (Input B G H m k w) (Fin m × Fin (scoreBits B H w)),
        f.size ≤ 1 + m * childCost B G H k w C e ∧
        ∀ (x : Input B G H m k w → Bool) (child : Fin m → H),
          (∀ i v, translated x i v = (index (child i * v)).val) →
          (∀ side t v, histogram π (counts x side t) v < 2^w) →
          ∀ i, value (fun j => f.eval x (i,j)) = numerator π (counts x false) (counts x true) (child i) := by
  obtain ⟨C,e,dot⟩ := dotFrames
  refine ⟨C,e,?_⟩
  intro B G H instB instG instH decH groupG groupH m k w π index
  obtain ⟨d,hd,he⟩ := dot (B × H) w
  let hist (i : Fin m) (p : Bool × B) := part (w := w) (⇑π) index p.1 i p.2
  have hb (i : Fin m) := Crossing.exists_parallelFrames (out := fun _ : Bool × B => H × Fin w) (hist i)
  choose both hsize heval using hb
  let pick (p : (B × H) × (Fin w ⊕ Fin w)) : Σ _ : Bool × B, H × Fin w :=
    p.2.elim (fun j => ⟨(true,p.1.1),p.1.2,j⟩) (fun j => ⟨(false,p.1.1),p.1.2,j⟩)
  let one (i : Fin m) := d.subst ((both i).select pick)
  obtain ⟨all,hs,hv⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin m => Fin (scoreBits B H w)) one
  refine ⟨all.select (fun p => ⟨p.1,p.2⟩), ?_, ?_⟩
  · have per (i : Fin m) : (one i).size ≤ childCost B G H k w C e := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun (p : Bool × B) _ => part_size (w := w) (⇑π) index p.1 i p.2)
      change (∑ p : Bool × B, (hist i p).size) ≤ _ at h
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, Nat.cast_id] at h
      simp only [one, Frame.subst_size, Frame.select_size, childCost]
      exact Nat.add_le_add ((hsize i).trans (Nat.add_le_add_left h _)) hd
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => per i)
    simpa only [Frame.select_size, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      hs.trans (Nat.add_le_add_left ht 1)
  · intro x child haddr fits i
    let z := ((both i).select pick).eval x
    have zout (j : Fin (scoreBits B H w)) : (all.select (fun p : Fin m × Fin (scoreBits B H w) => ⟨p.1,p.2⟩)).eval x (i,j) =
        d.eval z j := by simp only [Frame.select_eval, hv, one, Frame.subst_eval, z]
    simp only [zout, he, numerator, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro v _
    have left := part_value (⇑π) index true i t x (child i) (haddr i) (fits true t) v
    have right := part_value (⇑π) index false i t x (child i) (haddr i) (fits false t) v
    simp only [z, Frame.select_eval, pick, Sum.elim_inl, Sum.elim_inr, heval, hist]
    exact congrArg₂ Nat.mul left right

/-- Specialization of the universal cost constants to one tower level. -/
theorem exists_scores :
    ∃ C e : ℕ, ∀ (m k w : ℕ) (π : G →* H) (index : H ↪ Fin (2^k)),
      ∃ f : Frame (Input B G H m k w) (Fin m × Fin (scoreBits B H w)),
        f.size ≤ 1 + m * childCost B G H k w C e ∧
        ∀ (x : Input B G H m k w → Bool) (child : Fin m → H),
          (∀ i v, translated x i v = (index (child i * v)).val) →
          (∀ side t v, histogram π (counts x side t) v < 2^w) →
          ∀ i, value (fun j => f.eval x (i,j)) = numerator π (counts x false) (counts x true) (child i) := by
  obtain ⟨C,e,h⟩ := exists_scores_uniform
  exact ⟨C,e,h B G H⟩

end PackedDeckScore

end BorderVNP
end Computability
end OAI
