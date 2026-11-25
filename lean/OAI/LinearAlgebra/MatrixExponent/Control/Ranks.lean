import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort

section
/-!
# Histograms and occurrence ranks for fixed alphabets

Run one prefix counter per symbol. At each position select the counter
for its own symbol. The alphabet and its bit encoding enter only the
constant in the bound.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control
open Install

def letters {I A : Type} {n : ℕ} (D : (I → Bool) → A) (x : Fin n × I → Bool) (i : Fin n) : A :=
  D (fun j => x (i, j))

def ranks {I A : Type} [DecidableEq A] (D : (I → Bool) → A) (h : ℕ)
    (x : Fin (2 ^ h) × I → Bool) (ij : (A ⊕ Fin (2 ^ h)) × slots (word (h + 1))) : Bool :=
  bits (word (h + 1)) (Lookup.bits (h + 1) (Sum.elim
    (fun z => histogram (letters D x) z none) (rank (letters D x)) ij.1)) ij.2

def rankCost (I A : Type) [Fintype I] [Fintype A] :=
  7 * Fintype.card I + 2 ^ (Nat.clog 2 (Fintype.card A)) *
    (4 * Fintype.card I + localCost (Fintype.card I) + 1002) +
    localCost (1 + Fintype.card A + Fintype.card I) * (Fintype.card A + 1)

theorem predicate_bnet (F I : Type) [Field F] [Fintype I] (P : (I → Bool) → Bool) (n : ℕ) :
    BNet F (letters (n := n) P) (n * Fintype.card I + localCost (Fintype.card I) * n) := by
  classical
  have h : Depends (letters (n := n) P) (Fintype.card I) := by
    intro i
    refine ⟨Finset.univ.image (i, ·), Finset.card_image_le, fun x y h => ?_⟩
    exact congrArg P (funext fun j => h (i, j) (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  simpa using h.bnet F

variable {I A : Type} {h t : ℕ}

private abbrev Source (I : Type) (h t : ℕ) :=
  (Fin (2 ^ h) × I) ⊕ (Fin (2 ^ t) × Option (Fin (2 ^ h)) × slots (word (h + 1)))

private def pick (D : (I → Bool) → A) (e : A ↪ Fin (2 ^ t)) (x : Source I h t → Bool)
    (ij : (A ⊕ Fin (2 ^ h)) × slots (word (h + 1))) : Bool :=
  match ij.1 with
  | .inl z => x (.inr (e z, none, ij.2))
  | .inr i => x (.inr (e (letters D (x ∘ Sum.inl) i), some i, ij.2))

private theorem pick_depends [Fintype I] [Fintype A] (D : (I → Bool) → A) (e : A ↪ Fin (2 ^ t)) :
    Depends (pick (h := h) D e) (1 + Fintype.card A + Fintype.card I) := by
  classical
  rintro ⟨z | i, k⟩
  · exact ⟨{.inr (e z, none, k)}, by simp; omega, fun x y h => h _ (by simp)⟩
  · let s : Finset (Source I h t) := Finset.univ.image (fun z => Sum.inr (e z, some i, k))
    let r : Finset (Source I h t) := Finset.univ.image (fun j => Sum.inl (i, j))
    refine ⟨s ∪ r, ?_, fun x y H => ?_⟩
    · have hs : s.card ≤ Fintype.card A := Finset.card_image_le
      have hr : r.card ≤ Fintype.card I := Finset.card_image_le
      exact (Finset.card_union_le s r).trans (by omega)
    · have he : letters D (x ∘ Sum.inl) i = letters D (y ∘ Sum.inl) i :=
        congrArg D (funext fun j => H (.inl (i, j))
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
      simp only [pick, he]
      exact H _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))

private theorem cost_bound (N R T I A L M : ℕ) (hN : 0 < N) (hR : 0 < R) :
    5 * (N * I) + N * I + T * (3 * (N * I) + (N * I + L * N + 1000 * N * R)) +
      (N * I + T * ((N + 1) * R) + M * ((A + N) * R)) ≤
      (7 * I + T * (4 * I + L + 1002) + M * (A + 1)) * N * R := by
  have h : A + N ≤ (A + 1) * N := by nlinarith
  calc
    _ ≤ 5 * (N * I * R) + N * I * R + T * (3 * (N * I * R) + (N * I * R + L * N * R + 1000 * N * R)) +
        (N * I * R + T * ((2 * N) * R) + M * (((A + 1) * N) * R)) := by
      have hi := Nat.le_mul_of_pos_right (N * I) hR
      have hl := Nat.le_mul_of_pos_right (L * N) hR
      gcongr
      omega
    _ = _ := by ring

theorem ranks_bnet (F I A : Type) [Field F] [Fintype I] [Fintype A] [DecidableEq A]
    (D : (I → Bool) → A) (h : ℕ) :
    BNet F (ranks D h) (rankCost I A * 2 ^ h * (h + 1)) := by
  let t := Nat.clog 2 (Fintype.card A)
  have he : Fintype.card A ≤ Fintype.card (Fin (2 ^ t)) := by
    rw [Fintype.card_fin]
    exact Nat.le_pow_clog (by decide) _
  let e := Classical.choice (Function.Embedding.nonempty_of_card_le he)
  let P (z : Fin (2 ^ t)) (x : I → Bool) := decide (e (D x) = z)
  have hc := BNet.share t _ (fun z => (predicate_bnet F I (P z) (2 ^ h)).comp (prefix_bnet F h))
  have hh := ((BNet.id F (Fin (2 ^ h) × I)).pair hc).comp ((pick_depends (h := h) D e).bnet F)
  have ht := hh.mono (n := rankCost I A * 2 ^ h * (h + 1)) (by
    simp only [Source, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
      card_slots, wd_word, rankCost, show Fintype.card (slots .bit) = 1 from rfl, Nat.add_comm 1 h]
    exact cost_bound (2 ^ h) (h + 1) (2 ^ t) _ _ _ _ (by positivity) (by omega))
  convert ht using 1
  funext x p
  have hz (z : A) (j : Option (Fin (2 ^ h))) :
      histogram (letters (P (e z)) x) true j = histogram (letters D x) z j := by
    unfold histogram
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [letters, P, decide_eq_true_eq, e.injective.eq_iff]
  rcases p with ⟨z | i, k⟩
  · change _ = bits (word (h + 1)) (Lookup.bits _ (histogram (letters (P (e z)) x) true none)) k
    rw [hz]; rfl
  · change _ = bits (word (h + 1))
      (Lookup.bits _ (histogram (letters (P (e (letters D x i))) x) true (some i))) k
    rw [hz]; rfl

end OAI.LinearAlgebra.MatrixExponent.Control
end

section
/-! # Comparing an encoded count to fixed thresholds -/

namespace OAI.LinearAlgebra.MatrixExponent.Control
open Install

variable (F : Type) [Field F]

private theorem threshold_test (h n : ℕ) :
    DNet F (word h) .bit (fun x => decide (Lookup.value h x ≤ n)) (1000 * (h + 1)) := by
  by_cases hn : n + 1 < 2 ^ h
  · have k := ((DNet.id F (word h)).par (Lookup.const_net F (word h) (Lookup.bits h (n + 1)))).pre
      (.unit' _)
    have t := k.comp (Coloring.lt_net F h)
    simpa only [Lookup.value_bits hn, Nat.lt_succ_iff] using t.mono (n := 1000 * (h + 1))
      (by simp; omega)
  · have e (x) : Lookup.value h x ≤ n := by have := value_lt h x; omega
    have t := (DNet.discard F (word h)).comp (Lookup.const_net F .bit true)
    simpa only [e, decide_true] using t.mono (n := 1000 * (h + 1)) (by simp [wd])

theorem threshold_one (h n : ℕ) :
    BNet F (fun (x : slots (word h) → Bool) (_ : Unit) => decide ((decode h x).val ≤ n))
      (1000 * (h + 1)) := by
  apply BNet.of_layout (a := word h) (b := .bit) (.refl _) (.refl _)
  convert threshold_test F h n using 1
  funext x
  change decide (Lookup.value h ((bits (word h)).symm (bits (word h) x)) ≤ n) = _
  rw [Equiv.symm_apply_apply]

theorem threshold_bnet (h : ℕ) :
    BNet F (fun (x : slots (word h) → Bool) (i : Fin (2 ^ h)) => decide ((decode h x).val ≤ i.val))
      (2000 * 2 ^ h * (h + 1)) := by
  have t := BNet.share h _ fun i => threshold_one F h i.val
  apply (t.rename (.refl _) (Equiv.prodUnique _ Unit)).mono
  rw [card_slots, wd_word]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Control
end
