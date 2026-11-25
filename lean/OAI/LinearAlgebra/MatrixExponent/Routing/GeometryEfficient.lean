import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Near-linear controllers on packed addresses

An input permutation and each output permutation are extended by
the identity outside the label set. Circuits may depend on the
height and the fixed address format. Their cost exponent is uniform.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open scoped Classical
open Equiv

variable {F J : Type} [Field F] {X : J → Type} {h : J → ℕ} {e : ∀ j, X j ↪ B (h j)}

abbrev Family (X : J → Type) := ∀ j, Equiv.Perm (X j) → Equiv.Perm (X j)

abbrev pack {T : Type} {h : ℕ} (i : T ↪ B h) (g : Equiv.Perm T) : (Perm h).obj :=
  ⇑(Equiv.Perm.viaEmbeddingHom i g)

def Efficient (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j)) (g : Family X) : Prop :=
  ∃ c : ℕ, ∀ j, ∃ f, Cheap F (h j) (h j) (Perm (h j)) (Perm (h j)) f c ∧
    ∀ p, f (pack (e j) p) = pack (e j) (g j p)

private theorem perm_width (h : ℕ) : (Perm h).width ≤ 2 ^ h * (100 + h) ^ 1 := by
  simp [Perm]

theorem efficient_fixed (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j))
    (g : ∀ j, Equiv.Perm (X j)) : Efficient F e (fun j _ => g j) :=
  ⟨2, fun j => ⟨_, Cheap.const F (perm_width _) (perm_width _) (pack (e j) (g j)), fun _ => rfl⟩⟩

theorem efficient_target (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j)) :
    Efficient F e (fun _ p => p) :=
  ⟨2, fun _ => ⟨_, Cheap.id F (perm_width _), fun _ => rfl⟩⟩

variable {g g' : Family X}

theorem Efficient.mul (hg : Efficient F e g) (hg' : Efficient F e g') : Efficient F e (g * g') := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hg'
  refine ⟨max (max c d + 1) 8 + 1, fun j => ?_⟩
  obtain ⟨u, hu, he⟩ := hc j
  obtain ⟨v, hv, hf⟩ := hd j
  refine ⟨_, (hu.pair hv).comp (Cheap.lookup F (h j) (h j) (.addr (h j)) le_rfl (by simp)), ?_⟩
  intro p
  simp only [Function.comp_apply, he, hf, Pi.mul_apply, pack, map_mul]
  rfl

private def clean {T : Type} {n : ℕ} (i : T ↪ B n) (x : (Perm n).obj) (a : B n) :=
  if a ∈ Set.range i then x a else a

private theorem cheap_clean {T : Type} {n : ℕ} (i : T ↪ B n) :
    Cheap F n n (Perm n) (Perm n) (clean i) 2 := by
  have he (x : (Perm n).pins → Bool) (a : B n) (b : slots (word n)) :
      ((Perm n).code ∘ clean i ∘ (Perm n).code.symm) x (a, b) =
        if a ∈ Set.range i then x (a, b) else (Format.addr n).code a b := by
    change (Format.addr n).code (clean i ((Perm n).code.symm x) a) b = _
    unfold clean
    split
    · exact congrFun ((Perm n).code.apply_symm_apply x) (a, b)
    · rfl
  have hc : Install.Depends ((Perm n).code ∘ clean i ∘ (Perm n).code.symm) 1 := by
    rintro ⟨a, b⟩
    refine ⟨{(a, b)}, by simp, fun x y h => ?_⟩
    rw [he, he, h (a, b) (Finset.mem_singleton_self _)]
  refine ⟨_, hc.bnet F, ?_⟩
  change (Perm n).width + (Perm n).width + ((Perm n).width + 34 * (Perm n).width) ≤ _
  simp only [Perm, Format.width_vec, Format.width_addr]
  calc
    _ = 2 ^ n * (37 * n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

theorem efficient_of_on
    {c : ℕ} (hh : ∀ j, ∃ f, Cheap F (h j) (h j) (Perm (h j)) (Perm (h j)) f c ∧
      ∀ p a, f (pack (e j) p) (e j a) = e j (g j p a)) : Efficient F e g := by
  refine ⟨max c 2 + 1, fun j => ?_⟩
  obtain ⟨f, hf, he⟩ := hh j
  refine ⟨_, hf.comp (cheap_clean (e j)), fun p => ?_⟩
  funext a
  change clean (e j) _ a = (g j p).viaEmbedding (e j) a
  unfold clean
  split
  · rename_i ha
    obtain ⟨b, rfl⟩ := ha
    rw [Equiv.Perm.viaEmbedding_apply]
    exact he _ _
  · exact (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ‹_›).symm

variable [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]

/-- A single output circuit for all valid inputs induces three
permutation families, each with a uniform polynomial overhead. -/
theorem Efficient.factor {C A D : J → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (D j)]
    (s : ∀ j, X j ≃ C j × (A j × D j)) {c : ℕ} (H : Factors F c) (hg : Efficient F e g)
    (hf : ∀ j p x, (s j (g j p x)).1 = (s j x).1) :
    ∃ u v w : Family X, Efficient F e u ∧ Efficient F e v ∧ Efficient F e w ∧ g = u * v * w ∧
      (∀ j p x, (s j (u j p x)).1 = (s j x).1 ∧ (s j (u j p x)).2.1 = (s j x).2.1) ∧
      (∀ j p x, (s j (v j p x)).1 = (s j x).1 ∧ (s j (v j p x)).2.2 = (s j x).2.2) ∧
      (∀ j p x, (s j (w j p x)).1 = (s j x).1 ∧ (s j (w j p x)).2.1 = (s j x).2.1) := by
  have (j : J) : Finite (C j) := Finite.of_surjective (fun x => (s j x).1) (by
    intro a
    exact ⟨(s j).symm (a, (s j (Classical.arbitrary _)).2), by simp⟩)
  let (j : J) : Fintype (C j) := Fintype.ofFinite _
  choose f hc he using fun j => H (h j) _ _ _ _ (s j) (e j)
  obtain ⟨d, hd⟩ := hg
  choose f' hc' he' using hd
  have hy (j) (p : Equiv.Perm (X j)) (x : X j) :
      f' j (pack (e j) p) (e j x) = e j (g j p x) := by
    rw [he']
    exact Equiv.Perm.viaEmbedding_apply _ _ _
  choose u v w heq hu hv hw hu' hv' hw' using
    fun j p => he j (g j p) (hf j p) _ (hy j p)
  have hb (j) := (hc' j).comp (hc j)
  refine ⟨u, v, w, ?_, ?_, ?_, funext (fun j => funext (heq j)), hu, hv, hw⟩
  · exact efficient_of_on (fun j => ⟨_, (hb j).fst, hu' j⟩)
  · exact efficient_of_on (fun j => ⟨_, (hb j).snd.fst, hv' j⟩)
  · exact efficient_of_on (fun j => ⟨_, (hb j).snd.snd, hw' j⟩)

end OAI.LinearAlgebra.MatrixExponent.Coloring
