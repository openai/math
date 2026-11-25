import OAI.Computability.BorderVNP.PackedHistogram

/-! # Stable weighted offsets restored to public row order

All source tags are zero. The expanded sort word therefore orders the address,
then the original ordinal, then the weight. Equal-address rows are strictly
ordered by the public ordinal. The exclusive scan is returned by a second sort.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram
open private restore from OAI.Computability.BorderVNP.PackedHistogram

namespace Stable

open ParseBatchLookup ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork

variable {b k w : ℕ}

/-- Public rows of address and weight bits, including zero-width unused rows. -/
abbrev Input (b k w : ℕ) := Fin (2^b) × (Fin k ⊕ Fin w)

/-- Read one unsorted address word. -/
def key (x : Input b k w → Bool) (i : Fin (2^b)) := value fun j => x (i,.inl j)

/-- Read one unsorted weight word. -/
def weight (x : Input b k w → Bool) (i : Fin (2^b)) := value fun j => x (i,.inr j)

private def tagPin (p : Raw b k w) : Input b k w ⊕ Unit := match p.2 with
  | .inl j => .inl (p.1,.inl j)
  | .inr (.inl _) => .inr ()
  | .inr (.inr j) => .inl (p.1,.inr j)

private noncomputable def source (b k w : ℕ) : Frame (Input b k w) (Raw b k w) :=
  (((Frame.initial id).step (fun _ : Unit => .const false)).withInput).select tagPin

private theorem source_size (b k w : ℕ) : (source b k w).size ≤ 1 := by
  have hs := Frame.step_size_le (Frame.initial (id : Input b k w → _)) (fun _ : Unit => .const false) 1 (fun _ => le_rfl)
  simpa [source] using hs

private noncomputable def first (b k w : ℕ) : Frame (Input b k w) (Expanded b k w) :=
  (phases b le_rfl (expanded b k w)).subst (source b k w)

private noncomputable def totals (b k w : ℕ) : Frame (Expanded b k w) (Pins b w) :=
  PackedScan.offsetScan (addressWires b k w) (weightWires b k w) (2^b)

private noncomputable def ret (b k w : ℕ) : Frame (Input b k w) (Pins b (w+b)) :=
  ((totals b k w).withInput.select (fun ij : Pins b (w+b) =>
    prepend (fun j => Sum.inl (ij.1,ordinalPin k w j)) (fun j => Sum.inr (ij.1,j)) ij.2)).subst (first b k w)

/-- The exclusive same-bin wire offsets, in the original ordinal order. -/
noncomputable def frame (b k w : ℕ) : Frame (Input b k w) (Pins b w) :=
  (phases b le_rfl (ret b k w)).select fun ij => (ij.1,lowPin b ij.2)

/-- Two shared Batcher sorts and one segmented scan. -/
theorem frame_size (b k w : ℕ) : (frame b k w).size ≤ 1 + 2^b *
    (((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) + b^2*(24*(w+b)+1)) := by
  have h₁ := expanded_size b k w
  have h₂ := phases_size b le_rfl (expanded b k w)
  have h₃ := PackedScan.offsetScan_size (addressWires b k w) (weightWires b k w) (2^b)
  have h₄ := phases_size b le_rfl (ret b k w)
  have h₅ := source_size b k w
  change (totals b k w).size ≤ _ at h₃
  simp only [ret, first, Frame.subst_size, Frame.select_size, Frame.withInput_size] at h₄
  simp only [frame, ret, first, Frame.select_size]
  nlinarith only [h₁,h₂,h₃,h₄,h₅]

private noncomputable def code (x : Input b k w → Bool) (i : Fin (2^b)) :=
  record (fun j => x (i,.inl j)) false ((numberWords b).symm i) (fun j => x (i,.inr j))

private theorem source_word (x : Input b k w → Bool) (i : Fin (2^b)) :
    rawWord ((source b k w).eval x) i = code x i := by
  simp [rawWord, source, code, isQuery, tagPin, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]

private theorem code_rank (x : Input b k w → Bool) (i : Fin (2^b)) :
    value (code x i) / 2^w = 2*key x i*2^b+i.val := by
  have h : value (code x i) = 2^w * (2*key x i*2^b+i.val) + weight x i := by
    simp only [code, record, bits, value_prepend, value, Fin.cons_zero, Fin.cons_succ,
      Bool.toNat_false, zero_mul, zero_add, value_encode, key, weight, pow_succ, pow_add]
    ring
  have hw : weight x i < 2^w := value_lt _
  rw [h, Nat.mul_add_div (Nat.two_pow_pos w), Nat.div_eq_of_lt hw, Nat.add_zero]

private theorem prefix_univ {n j : ℕ} (hj : j < n) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range j, f i) = ∑ i : Fin n, if i.val < j then f i.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then f i else 0), ← Finset.sum_filter]
  have he : (Finset.range n).filter (· < j) = Finset.range j := by ext k; simp; omega
  rw [he]

/-- All earlier rows with the same input-dependent key contribute their width, with multiplicity.
Rows of width zero may occupy arbitrary holes in the public ordinal table. -/
theorem frame_value (x : Input b k w → Bool)
    (fits : ∀ a, bucket (key x) (weight x) a < 2^w) (i : Fin (2^b)) :
    value (fun j => (frame b k w).eval x (i,j)) =
      ∑ u : Fin (2^b), if key x u = key x i ∧ u < i then weight x u else 0 := by
  let s := (first b k w).eval x
  let y := (source b k w).eval x
  obtain ⟨π,hπ⟩ := phases_order (expanded b k w) y
  have wire (u j) : s (u,j) = code x (π u) j := by
    rw [show s (u,j) = (phases b le_rfl (expanded b k w)).eval y (u,j) from Frame.subst_eval _ _ _ _,
      hπ, expanded_eval, source_word]
  let ks := PackedScan.read s (addressWires b k w)
  let ws := PackedScan.read s (weightWires b k w)
  have hk (u : Fin (2^b)) : ks u.val = key x (π u) := by
    simp [ks, PackedScan.read, addressWires, Function.comp_def, wire, code, key]
  have hw (u : Fin (2^b)) : ws u.val = weight x (π u) := by
    simp [ws, PackedScan.read, weightWires, Function.comp_def, wire, code, weight]
  have rank : Monotone fun u => 2*key x (π u)*2^b+(π u).val := by
    intro u v huv
    have hn := Nat.div_le_div_right (c := 2^w) (phases_monotone (expanded b k w) y huv)
    simpa only [hπ, expanded_eval, y, source_word, code_rank] using hn
  have mono : Monotone (fun u : Fin (2^b) => ks u.val) := by
    intro u v huv
    change ks u.val ≤ ks v.val
    rw [hk,hk]
    have h := rank huv
    change 2*key x (π u)*2^b+(π u).val ≤ 2*key x (π v)*2^b+(π v).val at h
    by_contra! hn
    have h' := Nat.mul_le_mul_right (2^b) (show 2*key x (π v)+1 ≤ 2*key x (π u) by omega)
    rw [Nat.succ_mul] at h'
    have := (π v).isLt
    omega
  have stable (u v : Fin (2^b)) (he : key x (π u) = key x (π v)) : u < v ↔ π u < π v := by
    have weak (l r : Fin (2^b)) (hl : l ≤ r) (eq : key x (π l) = key x (π r)) : π l ≤ π r := by
      have h := rank hl
      change 2*key x (π l)*2^b+(π l).val ≤ 2*key x (π r)*2^b+(π r).val at h
      rw [eq, Nat.add_le_add_iff_left] at h
      exact h
    exact ⟨fun h => lt_of_le_of_ne (weak u v h.le he) (π.injective.ne h.ne),
      fun h => lt_of_not_ge (fun h' => h.not_ge (weak v u h' he.symm))⟩
  have hfit (l : ℕ) (hl : l < 2^b) : PackedScan.segmentTotal ks ws l < 2^w := by
    let u : Fin (2^b) := ⟨l,hl⟩
    have h := segment_le_bucket ks ws mono u
    have bins (a : ℕ) : bucket (fun v : Fin (2^b) => ks v.val) (fun v => ws v.val) a =
        bucket (key x) (weight x) a := by simpa only [hk,hw,Function.comp_def] using bucket_perm (key x) (weight x) π a
    exact h.trans_lt ((bins _).trans_lt (fits _))
  let vals := fun l : Fin (2^b) => fun d : Fin w => (totals b k w).eval s (l,d)
  have retBits (l j) : (ret b k w).eval x (l,j) = prepend ((numberWords b).symm (π l)) (vals l) j := by
    simp only [ret, Frame.subst_eval, Frame.select_eval]
    have h := congrFun (prepend_map ((totals b k w).withInput.eval s)
      (fun d : Fin b => Sum.inl (l,ordinalPin k w d)) (fun d : Fin w => Sum.inr (l,d))) j
    simpa only [Function.comp_def, Frame.withInput_eval_inl, Frame.withInput_eval_inr, wire, code, record_ordinal] using h
  have returned j : (frame b k w).eval x (i,j) = vals (π.symm i) j := by
    rw [frame, Frame.select_eval]
    exact restore _ x π vals retBits i j
  simp only [returned]
  have hsrt (u v : ℕ) (hu : u ≤ v) (hv : v < 2^b) : ks u ≤ ks v :=
    mono (show (⟨u,by omega⟩ : Fin (2^b)) ≤ ⟨v,hv⟩ from hu)
  let l := π.symm i
  change value (fun d => (PackedScan.offsetScan _ _ _).eval s (l,d)) = _
  rw [PackedScan.offsetScan_value _ _ _ s hfit hsrt l]
  change (∑ j ∈ Finset.range l.val, if ks j = ks l.val then ws j else 0) = _
  rw [prefix_univ l.isLt, ← Equiv.sum_comp π (fun u => if key x u = key x i ∧ u < i then weight x u else 0)]
  apply Finset.sum_congr rfl
  intro u _
  have hl : π l = i := π.apply_symm_apply _
  simp only [hk, hw, ← hl]
  by_cases eq : key x (π u) = key x (π l)
  · simp [eq, show (u.val < l.val) ↔ π u < π l from stable u l eq]
  · simp [eq]

end Stable
end PackedHistogram

end BorderVNP
end Computability
end OAI
