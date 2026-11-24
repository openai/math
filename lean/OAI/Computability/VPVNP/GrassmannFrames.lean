import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Logic.Relation

/-!
# Column moves for Grassmannian rigidity

In the equality case of Lemma 5.3 of *VP and VNP differ over every field*,
a column may be replaced by any vector outside the span of the entire tuple.
We show that these moves connect all ordered independent tuples with a fixed
initial segment when there is at least one unused ambient dimension.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace GrassmannFrames

open Function Set Relation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A free column is replaced by a vector outside the current span. Independence
of the extended tuple records both the original independence and the span condition. -/
def OutsideStep (K : Type*) [Field K] [Module K V] (k : ℕ) {n : ℕ}
    (v w : Fin n → V) : Prop :=
  ∃ (i : Fin n) (x : V), k ≤ i.val ∧
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) ∧ w = update v i x

private theorem exchange_last {n : ℕ} {v : Fin n → V} {x : V} (i : Fin n)
    (h : LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V)) :
    LinearIndependent K (Fin.snoc (update v i x) (v i) : Fin (n + 1) → V) := by
  let e := Equiv.swap i.castSucc (Fin.last n)
  have he : (Fin.snoc (update v i x) (v i) : Fin (n + 1) → V) = Fin.snoc v x ∘ e := by
    funext j
    cases j using Fin.lastCases with
    | last => simp [e]
    | cast j =>
      by_cases hji : j = i
      · subst j
        simp [e]
      · have h₁ : j.castSucc ≠ i.castSucc := by simpa using hji
        have h₂ : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
        simp [e, Equiv.swap_apply_of_ne_of_ne h₁ h₂, hji]
  rw [he]
  exact h.comp e e.injective

theorem OutsideStep.symm {k n : ℕ} {v w : Fin n → V} (h : OutsideStep K k v w) :
    OutsideStep K k w v := by
  rcases h with ⟨i, x, hi, hx, rfl⟩
  exact ⟨i, v i, hi, exchange_last i hx, by simp⟩

theorem OutsideStep.source_independent {k n : ℕ} {v w : Fin n → V} (h : OutsideStep K k v w) :
    LinearIndependent K v := by
  rcases h with ⟨_, _, _, hx, _⟩
  exact (linearIndependent_finSnoc.mp hx).1

private theorem span_ne_top {n : ℕ} (h : n < Module.finrank K V) (v : Fin n → V) :
    Submodule.span K (range v) ≠ ⊤ := by
  intro heq
  have := finrank_le_of_span_eq_top heq
  simp only [Fintype.card_fin] at this
  omega

/-- Two partial tuples of length less than the dimension admit a common new
column outside both spans, including over the binary field. -/
theorem exists_outside_both {n : ℕ} (h : n < Module.finrank K V) (v w : Fin n → V) :
    ∃ x, x ∉ Submodule.span K (range v) ∧ x ∉ Submodule.span K (range w) := by
  by_contra! hem
  have hs : ((⊤ : Submodule K V) : Set V) ⊆
      (Submodule.span K (range v) : Set V) ∪ Submodule.span K (range w) := by
    intro x _
    by_cases hx : x ∈ Submodule.span K (range v)
    · exact Or.inl hx
    · exact Or.inr (hem x hx)
  rcases AddSubgroupClass.subset_union.mp hs with hv | hw
  · exact span_ne_top h v (top_le_iff.mp hv)
  · exact span_ne_top h w (top_le_iff.mp hw)

private theorem connect_last {n k : ℕ} (hk : k ≤ n) (hd : n + 1 < Module.finrank K V)
    {v : Fin n → V} {a b : V}
    (ha : LinearIndependent K (Fin.snoc v a : Fin (n + 1) → V))
    (hb : LinearIndependent K (Fin.snoc v b : Fin (n + 1) → V)) :
    ReflTransGen (OutsideStep K k) (Fin.snoc v a) (Fin.snoc v b) := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_outside_both hd (Fin.snoc v a) (Fin.snoc v b)
  have hac : OutsideStep K k (Fin.snoc v a) (Fin.snoc v c) :=
    ⟨Fin.last n, c, hk, ha.finSnoc hc₁, (Fin.update_snoc_last ..).symm⟩
  have hbc : OutsideStep K k (Fin.snoc v b) (Fin.snoc v c) :=
    ⟨Fin.last n, c, hk, hb.finSnoc hc₂, (Fin.update_snoc_last ..).symm⟩
  exact (ReflTransGen.single hac).tail hbc.symm

private theorem lift_step {n k : ℕ} (hk : k ≤ n) (hd : n + 1 < Module.finrank K V)
    {v w : Fin n → V} (step : OutsideStep K k v w) {a b : V}
    (ha : LinearIndependent K (Fin.snoc v a : Fin (n + 1) → V))
    (hb : LinearIndependent K (Fin.snoc w b : Fin (n + 1) → V)) :
    ReflTransGen (OutsideStep K k) (Fin.snoc v a) (Fin.snoc w b) := by
  rcases step with ⟨i, x, hi, hx, rfl⟩
  obtain ⟨c, hc, _⟩ := exists_outside_both hd (Fin.snoc v x) (Fin.snoc v x)
  have hxc := hx.finSnoc hc
  have hcx : LinearIndependent K (Fin.snoc (Fin.snoc v c) x : Fin (n + 2) → V) := by
    simpa only [Fin.update_snoc_last, Fin.snoc_last] using exchange_last (Fin.last n) hxc
  have mid : OutsideStep K k (Fin.snoc v c) (Fin.snoc (update v i x) c) :=
    ⟨i.castSucc, x, hi, hcx, Fin.snoc_update ..⟩
  exact ((connect_last hk hd ha mid.source_independent).tail mid).trans
    (connect_last hk hd mid.symm.source_independent hb)

private theorem lift_path {n k : ℕ} (hk : k ≤ n) (hd : n + 1 < Module.finrank K V)
    {v w : Fin n → V} (path : ReflTransGen (OutsideStep K k) v w) {a b : V}
    (ha : LinearIndependent K (Fin.snoc v a : Fin (n + 1) → V))
    (hb : LinearIndependent K (Fin.snoc w b : Fin (n + 1) → V)) :
    ReflTransGen (OutsideStep K k) (Fin.snoc v a) (Fin.snoc w b) := by
  induction path generalizing b with
  | refl => exact connect_last hk hd ha hb
  | @tail u w _ step ih =>
    obtain ⟨c, hc, _⟩ := exists_outside_both (Nat.lt_trans (Nat.lt_succ_self n) hd) u u
    have hu := step.source_independent.finSnoc hc
    exact (ih hu).trans (lift_step hk hd step hu hb)

/-- All independent tuples with a prescribed initial segment are connected by
moves that leave this segment fixed and insert a column outside the current span. -/
theorem connected {k n : ℕ} (hd : k + n < Module.finrank K V) {v w : Fin (k + n) → V}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hfixed : ∀ i, i.val < k → v i = w i) : ReflTransGen (OutsideStep K k) v w := by
  induction n with
  | zero =>
    have : v = w := funext fun i => hfixed i i.isLt
    rw [this]
  | succ n ih =>
    have hv' := (linearIndependent_finSucc'.mp hv).1
    have hw' := (linearIndependent_finSucc'.mp hw).1
    have path := ih (by omega) hv' hw' (fun i hi => hfixed i.castSucc hi)
    have ha := (Fin.snoc_init_self v).symm ▸ hv
    have hb := (Fin.snoc_init_self w).symm ▸ hw
    have hp := lift_path (Nat.le_add_right k n) hd path ha hb
    exact (Fin.snoc_init_self v) ▸ (Fin.snoc_init_self w) ▸ hp

/-- A length-indexed version of connectivity for a prescribed prefix. -/
theorem connected_of_prefix {k l : ℕ} (hk : k ≤ l) (hd : l < Module.finrank K V)
    {v w : Fin l → V} (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hfixed : ∀ i, i.val < k → v i = w i) : ReflTransGen (OutsideStep K k) v w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact connected hd hv hw hfixed

/-- Any quantity preserved by outside-column replacements is constant on the
independent completions of a fixed tuple. -/
theorem invariant {Y : Type*} {k n : ℕ} {f : (Fin (k + n) → V) → Y}
    (hstep : ∀ {v w}, OutsideStep K k v w → f v = f w)
    (hd : k + n < Module.finrank K V) {v w : Fin (k + n) → V}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hfixed : ∀ i, i.val < k → v i = w i) : f v = f w := by
  have along : ∀ {u t : Fin (k + n) → V}, ReflTransGen (OutsideStep K k) u t → f u = f t := by
    intro u t path
    induction path with
    | refl => rfl
    | tail _ step ih => exact ih.trans (hstep step)
  exact along (connected hd hv hw hfixed)

end GrassmannFrames

end VPVNP
end Computability
end OAI
