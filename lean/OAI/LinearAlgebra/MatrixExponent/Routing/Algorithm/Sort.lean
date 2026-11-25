import OAI.LinearAlgebra.MatrixExponent.BitonicMerge
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import Mathlib.Tactic.Ring
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort

/-! # A RAM realization of Batcher's comparator network -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM

open Coloring

private abbrev T (α : Type) : ℕ → Type
  | 0 => α
  | n + 1 => T α n × T α n

variable {α : Type} {a : Wire}

private def build : (n : ℕ) → (ℕ → α) → T α n
  | 0, x => x 0
  | n + 1, x => (build n x, build n (fun i => x (2 ^ n + i)))

private def peek : (n : ℕ) → T α n → ℕ → α
  | 0, x, _ => x
  | n + 1, x, i => if i < 2 ^ n then peek n x.1 i else peek n x.2 (i - 2 ^ n)

private theorem read_build (n : ℕ) (x : ℕ → α) (i : ℕ) (hi : i < 2 ^ n) :
    peek n (build n x) i = x i := by
  induction n generalizing x i with
  | zero => have : i = 0 := by simpa using hi
            subst i
            rfl
  | succ n ih =>
    simp only [build, peek]
    rw [pow_succ] at hi
    split
    · exact ih x i (by assumption)
    · rw [ih _ _ (by omega), show 2 ^ n + (i - 2 ^ n) = i by omega]

/-- The equivalence is only used to transfer the network correctness proof. -/
private def decode (e : Val a ≃ α) : (n : ℕ) → Val (tree n a) ≃ T α n
  | 0 => e
  | n + 1 => (decode e n).prodCongr (decode e n)

private theorem read_decode (e : Val a ≃ α) (n : ℕ) (x : Val (tree n a)) :
    List.ofFn (fun i : Fin (2 ^ n) => peek n (decode e n x) i) =
      (flatten n x).map e := by
  induction n with
  | zero =>
    change List.ofFn (fun _ : Fin 1 => e x) = [e x]
    simp
  | succ n ih =>
    rw [pow_succ, mul_two, List.ofFn_add, flatten, List.map_append, ← ih, ← ih]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · change (if i.val < 2 ^ n then _ else _) = _
      rw [ite_eq_left i.isLt]
      rfl
    · change (if 2 ^ n + i.val < 2 ^ n then _ else peek n _ (2 ^ n + i.val - 2 ^ n)) = _
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rfl

variable {w m r h k : ℕ}

private theorem enter (hh : h ≤ w) (n : ℕ) (idx : ℕ → B h) :
    RAM w (fun x : B h → α => build n (x ∘ idx)) (2 ^ n * (1 + n)) := by
  induction n generalizing idx with
  | zero => exact .at hh (idx 0)
  | succ n ih =>
    refine ((ih idx).pair (ih (fun i => idx (2 ^ n + i)))).mono ?_
    have : 0 < 2 ^ n := by positivity
    ring_nf
    omega

private theorem exitEntry (n i : ℕ) : RAM w (fun x : T α n => peek n x i) (1 + n) := by
  induction n generalizing i with
  | zero => exact .id
  | succ n ih =>
    by_cases h : i < 2 ^ n
    · simp only [peek, ite_eq_left h]
      exact (fst.comp (ih i)).mono (by omega)
    · simp only [peek, ite_eq_right h]
      exact (snd.comp (ih (i - 2 ^ n))).mono (by omega)

private theorem both {β γ δ : Type} {f : α → β} {g : γ → δ} (hf : RAM w f m)
    (hg : RAM w g r) : RAM w (Prod.map f g) (m + r + 3) :=
  ((fst.comp hf).pair (snd.comp hg)).mono (by omega)

private theorem middle :
    RAM w (fun x : (α × α) × (α × α) => ((x.1.1, x.2.1), (x.1.2, x.2.2))) 11 :=
  ((fst.comp fst).pair (snd.comp fst)).pair ((fst.comp snd).pair (snd.comp snd))

private def Models (e : Val a ≃ α) (n : ℕ) (f : Val (tree n a) → Val (tree n a))
    (w cost : ℕ) : Prop :=
  ∃ g : T α n → T α n, RAM w g cost ∧ ∀ x, g (decode e n x) = decode e n (f x)

private theorem revModels (e : Val a ≃ α) (n : ℕ) :
    Models e n (reverseTree n) w (2 ^ n * (4 * (1 + n))) := by
  induction n with
  | zero => exact ⟨_, RAM.id.mono (by decide), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    refine ⟨_, ((snd.comp hf).pair (fst.comp hf)).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · exact congrArg₂ Prod.mk (ef x.2) (ef x.1)

section
variable [LinearOrder (Val a)]

private theorem splitModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e (n + 1) (splitTree n) w (2 ^ n * (m + 100 * n)) := by
  induction n with
  | zero => simpa using he
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    have hp := middle (α := T α n) (w := w)
    refine ⟨_, ((hp.comp (both hf hf)).comp hp).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · let y : Val (tree (n + 1) a) := (x.1.1, x.2.1)
      let z : Val (tree (n + 1) a) := (x.1.2, x.2.2)
      exact congrArg₂ (fun (p q : T α (n + 1)) => ((p.1, q.1), (p.2, q.2))) (ef y) (ef z)

private theorem mergeModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e n (mergeTree n) w (2 ^ n * (1 + n) ^ 2 * (m + 100)) := by
  induction n with
  | zero => exact ⟨_, RAM.id.mono (by simp), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    obtain ⟨g, hg, eg⟩ := splitModels he n
    refine ⟨_, (hg.comp (both hf hf)).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · rw [Function.comp_apply, eg]
      exact congrArg₂ Prod.mk (ef (splitTree n x).1) (ef (splitTree n x).2)

private theorem sortModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e n (sortTree n) w (2 ^ n * (1 + n) ^ 3 * (m + 200)) := by
  induction n with
  | zero => exact ⟨_, RAM.id.mono (by simp), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    obtain ⟨g, hg, eg⟩ := mergeModels he (n + 1)
    obtain ⟨v, hv, ev⟩ := revModels (w := w) e n
    refine ⟨_, ((both hf (hf.comp hv)).comp hg).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · change g (f (decode e n x.1), v (f (decode e n x.2))) = _
      rw [ef, ef, ev]
      exact eg (sortTree n x.1, reverseTree n (sortTree n x.2))

end

section
variable [LinearOrder α]

private theorem exchange (cmp : RAM w (fun x : α × α => decide (x.1 < x.2)) m) :
    RAM w (fun x : α × α => (min x.1 x.2, max x.1 x.2)) (m + 7) := by
  have sw : RAM w (fun x : α × α => (x.2, x.1)) 3 := snd.pair fst
  have p := (cmp.pair (RAM.id.pair sw)).comp select
  convert p.mono (n := m + 7) (by omega) using 1
  funext ⟨x, y⟩
  by_cases h : x < y
  · simp [h, min_eq_left h.le, max_eq_right h.le]
  · simp [h, min_eq_right (le_of_not_gt h), max_eq_left (le_of_not_gt h)]

/-- The code equivalence transfers correctness on single records. No encoding or
decoding takes place in the program, which compares and moves whole records. -/
theorem sort (e : Val a ≃ α) (cmp : RAM w (fun x : α × α => decide (x.1 < x.2)) m)
    (hh : h ≤ w) :
    RAM w (fun x : B h → α => x ∘ Tuple.sort x) (2 ^ h * (100 + h) ^ 6 * (m + 1)) := by
  let ord := LinearOrder.lift' e e.injective
  have he : Models e 1 (splitTree 0) w (m + 7) := by
    refine ⟨_, exchange cmp, fun x => ?_⟩
    change (min (e x.1) (e x.2), max (e x.1) (e x.2)) =
      (e (min x.1 x.2), e (max x.1 x.2))
    rcases le_total x.1 x.2 with j | j
    · have j' : e x.1 ≤ e x.2 := j
      rw [min_eq_left j', max_eq_right j', min_eq_left j, max_eq_right j]
    · have j' : e x.2 ≤ e x.1 := j
      rw [min_eq_right j', max_eq_left j', min_eq_right j, max_eq_left j]
  obtain ⟨g, hg, eg⟩ := sortModels he h
  let idx := Fin.ofNat (2 ^ h)
  let fetch (v : T α h) (i : B h) := peek h v i
  have hout : RAM w fetch (2 ^ h * ((1 + h) + 1)) := .tab hh _ (fun i => exitEntry h i.val)
  have p := ((enter hh h idx).comp hg).comp hout
  have ok (x : B h → α) : fetch (g (build h (x ∘ idx))) = x ∘ Tuple.sort x := by
    obtain ⟨z, hz⟩ := (decode e h).surjective (build h (x ∘ idx))
    have src : fetch (decode e h z) = x := by
      funext i
      unfold fetch
      rw [hz, read_build _ _ _ i.isLt]
      simp [idx]
    rw [← hz, eg]
    apply List.ofFn_injective
    have ep (v : Val (tree h a)) : List.ofFn (fetch (decode e h v)) =
        (flatten h v).map e := read_decode e h v
    rw [ep]
    refine List.Perm.eq_of_pairwise' ?_ (Tuple.monotone_sort _).sortedLE_ofFn.pairwise ?_
    · exact List.pairwise_map.mpr (sortTree_sorted h z)
    · rw [← src]
      exact ((sortTree_perm h z).map e).trans
        ((ep z).symm ▸ (Equiv.Perm.ofFn_comp_perm ..).symm)
  change RAM w (fun x => fetch (g (build h (x ∘ idx)))) _ at p
  simp only [ok] at p
  exact p.mono (by ring_nf; omega)

end

private theorem lexLt {β : Type} [LinearOrder α] [LinearOrder β] {t : ℕ}
    (p : RAM w (fun x : α × α => decide (x.1 < x.2)) m)
    (q : RAM w (fun x : α × α => decide (x.1 = x.2)) r)
    (s : RAM w (fun x : β × β => decide (x.1 < x.2)) t) :
    RAM w (fun x : (α ×ₗ β) × (α ×ₗ β) => decide (x.1 < x.2)) (m + r + t + 19) := by
  let L := α ×ₗ β
  have a : RAM w (fun x : L × L => ((ofLex x.1).1, (ofLex x.2).1)) 5 :=
    (fst.comp fst).pair (snd.comp fst)
  have b : RAM w (fun x : L × L => ((ofLex x.1).2, (ofLex x.2).2)) 5 :=
    (fst.comp snd).pair (snd.comp snd)
  have u := ((a.comp q).pair (b.comp s)).comp (gate (fun x => x.1 && x.2))
  have v := ((a.comp p).pair u).comp (gate (fun x => x.1 || x.2))
  convert v.mono (n := m + r + t + 19) (by omega) using 1
  funext ⟨x, y⟩
  let i := ofLex x
  let j := ofLex y
  change decide (toLex i < toLex j) =
    (decide (i.1 < j.1) || decide (i.1 = j.1) && decide (i.2 < j.2))
  apply Bool.eq_iff_iff.mpr
  simp [Prod.Lex.toLex_lt_toLex]

/-- Record indices break ties in the key and recover the forward permutation. -/
theorem permutation (hh : h ≤ w) (hk : k ≤ w) :
    RAM w (fun x : (B h → B k) × (B h → Bool) => ⇑(Coloring.permutation x.1 x.2))
      (2 ^ h * (100 + w) ^ 20) := by
  let A := Bool ×ₗ (B k ×ₗ B h)
  let e : Val (.pair .bit (.pair (word k) (word h))) ≃ A :=
    (Equiv.refl Bool).prodCongr ((MatrixExponent.Control.index k).prodCongr (MatrixExponent.Control.index h))
  have cmp : RAM w (fun x : A × A => decide (x.1 < x.2)) 43 :=
    lexLt (.gate _) (.gate _) (lexLt (.lt hk) (.eq hk) (.lt hh))
  have key : RAM w (fun (x : (B h → B k) × (B h → Bool)) i =>
      toLex (!x.2 i, toLex (x.1 i, i))) (2 ^ h * 12) := by
    refine .tab (m := 11) hh _ (fun i => ?_)
    have neg : RAM w (fun x : Bool => !x) 4 := (RAM.id.pair RAM.id).comp (gate (fun p => !p.1))
    exact ((snd.comp (.at hh i)).comp neg).pair ((fst.comp (.at hh i)).pair (lit hh i))
  have out : RAM w (fun (x : B h → A) i => (ofLex (ofLex (x i)).2).2) (2 ^ h * 4) :=
    .tab hh _ (fun i => ((RAM.at hh i).comp snd).comp snd)
  refine ((key.comp (sort e cmp hh)).comp out).mono ?_
  calc
    _ ≤ 2 ^ h * (12 + (100 + w) ^ 6 * 44 + 4) := by
      rw [show 43 + 1 = 44 by decide, mul_add, mul_add, ← mul_assoc]
      gcongr
    _ ≤ 2 ^ h * (100 + w) ^ 7 := by
      apply Nat.mul_le_mul_left
      ring_nf
      omega
    _ ≤ _ := by gcongr; omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
