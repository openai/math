import OAI.Computability.MultitapeWeakETH.Tables
import OAI.Computability.MultitapeWeakETH.Relations

namespace OAI.Computability.MultitapeWeakETH.Network

variable {n b : ℕ} (G : Network n b)

abbrev View (v : Fin G.vertices) :=
  ((e : { e // G.src e = v ∨ G.dst e = v }) → Word (G.width e.val)) ×
  (G.localBits G.input v → Bool) × (G.localBits G.output v → Bool)

abbrev Labels := (e : Fin G.edges) → Word (G.width e)

def view (ext : Word n × Word n) (labels : G.Labels) (v : Fin G.vertices) : G.View v :=
  ⟨fun e => labels e.val, fun i => ext.1 i.val, fun i => ext.2 i.val⟩

theorem view_injective (ext : Word n × Word n) : Function.Injective (G.view ext) := by
  intro a b same
  funext e
  exact congrArg (fun views => (views (G.src e)).1 ⟨e,Or.inl rfl⟩) same

noncomputable def contract {K : Type*} [CommSemiring K] (table : (v : Fin G.vertices) → G.View v → K)
    (x z : Word n) : K := ∑ s, ∏ v, table v (G.view (x,z) s v)

theorem exists_field_tables {K : Type*} [Field K] [Infinite K] (relation : G.Relation) :
    ∃ table : (v : Fin G.vertices) → G.View v → K, ∀ x z,
      G.contract table x z ≠ 0 ↔ G.Attains relation x z := by
  obtain ⟨table,ht⟩ := realize_relations (K := K) G.view G.view_injective
    (fun v localView => relation v localView.1 localView.2.1 localView.2.2)
  exact ⟨table, fun x z => ht (x,z)⟩

/-- Every singleton attainable support becomes a nonzero multiple of the
same basis vector, simultaneously over all inputs on the fixed graph. -/
theorem returns_of_unique {K : Type*} [Field K] [Infinite K] (relation : G.Relation) :
    ∃ table : (v : Fin G.vertices) → G.View v → K, ∀ x z, G.Attains relation x z →
      (∀ other, G.Attains relation x other → other = z) →
      ∃ c : K, c ≠ 0 ∧ ∀ out, G.contract table x out = if out = z then c else 0 := by
  obtain ⟨table,ht⟩ := G.exists_field_tables (K := K) relation
  refine ⟨table, fun x z hz unique => ⟨_,(ht x z).mpr hz,fun out => ?_⟩⟩
  by_cases eq : out = z
  · simp [eq]
  · simp only [eq, ↓reduceIte]
    by_contra nonzero
    exact eq (unique out ((ht x out).mp nonzero))

end OAI.Computability.MultitapeWeakETH.Network

namespace OAI.Computability.MultitapeWeakETH

/-- Singleton nonzero output support for one fixed input. -/
def Network.FieldGood {n b : ℕ} (G : Network n b) {K : Type*} [Field K]
    (tables : Word n → (v : Fin G.vertices) → G.View v → K) (x y : Word n) : Prop :=
  ∃ out, (∃ c : K, c ≠ 0 ∧ ∀ z, G.contract (tables y) x z = if z = out then c else 0) ∧
    100 * errors out (lowProduct x y) ≤ n

/-- The field-valued multiplication case at the numerical parameters used
by the tape lower bound. Its graph and terminal order are common to all columns. -/
def FieldTableBound (K : Type*) [Field K] : Prop := ∀ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ,
  ∀ n b, 0 < b → m₀ ≤ n ⌈/⌉ b → ∀ G : Network n b, G.Bounded D →
    ∀ tables : Word n → (v : Fin G.vertices) → G.View v → K,
      (2 : ℝ)^(-(11/1000 : ℝ) * n) ≤ density (G.FieldGood tables) →
        c * scale (n ⌈/⌉ b) ≤ G.vertices

theorem partialTableBound_of_field {K : Type*} [Field K] [Infinite K]
    (fieldBound : FieldTableBound K) : PartialTableBound := by
  classical
  intro D
  obtain ⟨c,hc,m₀,lower⟩ := fieldBound D
  refine ⟨c,hc,m₀,?_⟩
  intro n b hb hm G bounded relations densityBound
  choose tables repr using fun y => G.returns_of_unique (K := K) (relations y)
  apply lower n b hb hm G bounded tables
  apply densityBound.trans
  unfold density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨out,att,unique,err⟩ := (Finset.mem_filter.mp hp).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,out,repr p.2 p.1 out att unique,err⟩

end OAI.Computability.MultitapeWeakETH
