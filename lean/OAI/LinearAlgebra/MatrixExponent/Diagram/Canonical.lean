import OAI.LinearAlgebra.MatrixExponent.Diagram.Normalize
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement

/-!
# Canonical port shapes

Replace each local bundle by a word of the same length. A fixed port
order for each shape is essential because distinct nestings of pairs
and units can represent arbitrarily many trivalent table labels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Finset
open scoped Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b)

private def order (a : Wire) : slots (word (wd a)) ≃ slots a :=
  Fintype.equivOfCardEq (by rw [card_slots, wd_word, card_slots])

private abbrev relabel (T : Table F) : Table F :=
  ⟨word (wd T.1), word (wd T.2.1),
    fun x y => T.2.2 (reindex (order T.1).symm x) (reindex (order T.2.1).symm y)⟩

abbrev canonical : Diagram F a b where
  V := G.V
  E := G.E
  table v := relabel (G.table v)
  src := (Equiv.sigmaCongrRight fun v => order (G.table v).1).trans G.src
  dst := (Equiv.sigmaCongrRight fun v => order (G.table v).2.1).trans G.dst

theorem source_canonical (e : G.E) : G.canonical.source e = G.source e := rfl
theorem target_canonical (e : G.E) : G.canonical.target e = G.target e := rfl

@[simp] theorem arity_canonical (v : G.V) : G.canonical.arity v = G.arity v := by
  simp only [arity, wd_word]

@[simp] theorem cost_canonical : G.canonical.cost = G.cost := by
  unfold cost
  exact sum_congr rfl fun v _ => congrArg (1 + ·) (G.arity_canonical v)

private theorem recover (a : Wire) (f : slots a → Bool) :
    reindex (order a).symm ((bits (word (wd a))).symm (f ∘ order a)) = (bits a).symm f := by
  apply (bits a).injective
  funext j
  simp [Function.comp_def]

@[simp] theorem vertex_canonical (x : Val a) (y : Val b) (z : G.E → Bool) (v : G.V) :
    G.canonical.vertex x y z v = G.vertex x y z v := by
  apply congrArg₂ (G.table v).2.2
  · exact recover _ (fun i => Sum.elim (bits a x) z (G.src ⟨v, i⟩))
  · exact recover _ (fun i => Sum.elim (bits b y) z (G.dst ⟨v, i⟩))

@[simp] theorem eval_canonical [Field F] : G.canonical.eval = G.eval := by
  funext x y
  unfold eval
  exact sum_congr rfl fun z _ => prod_congr rfl fun v _ => G.vertex_canonical x y z v

variable [Field F] [Fintype F]

private abbrev Shape := {p : Fin 4 × Fin 4 // p.1.val + p.2.val ≤ 3}

private def small (p : Shape) : Finset (Table F) :=
  univ.image (fun f : Val (word p.val.1) → Val (word p.val.2) → F =>
    ⟨word p.val.1, word p.val.2, f⟩)

private theorem small_bound (p : Shape) : (small (F := F) p).card ≤ Fintype.card F ^ 8 := by
  have hv (a : Wire) : Fintype.card (Val a) = 2 ^ wd a := by
    rw [Fintype.card_congr (bits a), Fintype.card_fun, Fintype.card_bool, card_slots]
  refine card_image_le.trans ?_
  simp only [card_univ, Fintype.card_fun, hv, wd_word, ←pow_mul, ←pow_add]
  apply Nat.pow_le_pow_right Fintype.card_pos
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : p.val.2.val + p.val.1.val ≤ 3)

/-- All trivalent tables fit in a finite dictionary. Every prescribed
wide table contributes at most one additional entry. -/
theorem canonical_palette {u : ℕ} {L : Finset (Table F)} (h : G.Admits u ↑L) :
    (univ.image G.canonical.table).card ≤ L.card + 16 * Fintype.card F ^ 8 := by
  have sub : univ.image G.canonical.table ⊆ L.image relabel ∪ univ.biUnion small := by
    rintro _ hq
    obtain ⟨v, _, rfl⟩ := mem_image.mp hq
    rcases (h v).2 with hs | hl
    · let i := wd (G.table v).1
      let j := wd (G.table v).2.1
      change i + j ≤ 3 at hs
      let p : Shape := ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hs⟩
      refine mem_union_right _ (mem_biUnion.mpr ⟨p, mem_univ _, ?_⟩)
      exact mem_image.mpr ⟨(G.canonical.table v).2.2, mem_univ _, rfl⟩
    · exact mem_union_left _ (mem_image_of_mem _ hl)
  have hc : Fintype.card Shape ≤ 16 := by
    simpa using Fintype.card_subtype_le (fun p : Fin 4 × Fin 4 => p.1.val + p.2.val ≤ 3)
  refine (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add card_image_le ?_))
  calc
    _ ≤ ∑ p, (small (F := F) p).card := card_biUnion_le
    _ ≤ ∑ _ : Shape, Fintype.card F ^ 8 := sum_le_sum fun p _ => small_bound p
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (Fintype.card F ^ 8) hc

/-- Subdivide edges and relabel the resulting diagram, including the
new equality tables. The exterior positions remain unchanged. -/
theorem canonical_normalized {u : ℕ} {L : Finset (Table F)} (h : G.Admits u ↑L) :
    let H := G.normalized.canonical
    H.eval = G.eval ∧ H.cost ≤ 4 * G.cost ∧ (∀ v, H.arity v ≤ max 2 u) ∧
      (∀ e, H.source e ≠ H.target e) ∧
      (univ.image H.table).card ≤ L.card + 16 * Fintype.card F ^ 8 := by
  have hn : G.normalized.Admits (max 2 u) ↑L := G.admits_normalized (le_max_left ..)
    (fun v => ⟨(h v).1.trans (le_max_right ..), (h v).2⟩)
  exact ⟨G.normalized.eval_canonical.trans (funext fun x => funext fun y => G.eval_normalized x y),
    G.normalized.cost_canonical.le.trans G.cost_normalized,
    fun v => (G.normalized.arity_canonical v).le.trans (hn v).1,
    G.normalized_loopless, G.normalized.canonical_palette hn⟩

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-!
# Replacing each station by a diagram

Every old wire end is attached to the corresponding exterior position
of a replacement. Internal wires of different replacements are disjoint.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)
  (q : ∀ v, Diagram F (G.table v).1 (G.table v).2.1)

private def splice {V A E : Type} {P Q : V → Type} (e : (Σ v, P v) ≃ A ⊕ E) :
    (Σ v, P v ⊕ Q v) ≃ A ⊕ E ⊕ (Σ v, Q v) :=
  (Equiv.sigmaSumDistrib _ _).trans ((e.sumCongr (.refl _)).trans (Equiv.sumAssoc _ _ _))

abbrev plug : Diagram F a b where
  V := Σ v, (q v).V
  E := G.E ⊕ (Σ v, (q v).E)
  table t := (q t.1).table t.2
  src := (Equiv.sigmaAssoc (fun v w => slots ((q v).table w).1)).trans
    ((Equiv.sigmaCongrRight (fun v => (q v).src)).trans (splice G.src))
  dst := (Equiv.sigmaAssoc (fun v w => slots ((q v).table w).2.1)).trans
    ((Equiv.sigmaCongrRight (fun v => (q v).dst)).trans (splice G.dst))

def plugEnd : (Σ v, (q v).End) ≃ (G.plug q).End :=
  (Equiv.sigmaSumDistrib _ _).trans ((splice G.src).sumCongr (splice G.dst))

theorem plugEnd_port (v : G.V) (p : Σ w, (q v).Port w) :
    G.plugEnd q ⟨v, (q v).portEquiv p⟩ = (G.plug q).portEquiv ⟨⟨v, p.1⟩, p.2⟩ := by
  rcases p with ⟨w, i|j⟩ <;> rfl

theorem station_plugEnd (v : G.V) (e : (q v).End) :
    (G.plug q).station (G.plugEnd q ⟨v, e⟩) = ⟨v, (q v).station e⟩ := by
  obtain ⟨p, rfl⟩ := (q v).portEquiv.surjective e
  rw [plugEnd_port, station_port, station_port]

private theorem splice_eval {V A E : Type} {P Q : V → Type} (e : (Σ v, P v) ≃ A ⊕ E)
    (x : A → Bool) (z : E → Bool) (t : ∀ v, Q v → Bool) (v : V) (i : P v ⊕ Q v) :
    Sum.elim x (Sum.elim z (fun p => t p.1 p.2)) (splice e ⟨v, i⟩) =
      Sum.elim (fun j => Sum.elim x z (e ⟨v, j⟩)) (t v) i := by
  cases i with
  | inr _ => rfl
  | inl j =>
    change Sum.elim _ _ (Equiv.sumAssoc _ _ _ (.inl (e ⟨v, j⟩))) = Sum.elim x z (e ⟨v, j⟩)
    cases e ⟨v, j⟩ <;> rfl

private def inputAt (x : Val a) (z : G.E → Bool) (v : G.V) :=
  (bits (G.table v).1).symm (fun i => Sum.elim (bits a x) z (G.src ⟨v, i⟩))

private def outputAt (y : Val b) (z : G.E → Bool) (v : G.V) :=
  (bits (G.table v).2.1).symm (fun i => Sum.elim (bits b y) z (G.dst ⟨v, i⟩))

private def assignments : (G.E → Bool) × (∀ v, (q v).E → Bool) ≃ ((G.plug q).E → Bool) :=
  ((Equiv.refl _).prodCongr (Equiv.piCurry (fun v (_ : (q v).E) => Bool)).symm).trans
    (Equiv.sumArrowEquivProdArrow _ _ _).symm

private theorem vertex_plug (x : Val a) (y : Val b) (z : G.E → Bool) (t : ∀ v, (q v).E → Bool)
    (v : G.V) (w : (q v).V) :
    (G.plug q).vertex x y (assignments G q (z, t)) ⟨v, w⟩ =
      (q v).vertex (G.inputAt x z v) (G.outputAt y z v) (t v) w := by
  unfold vertex inputAt outputAt
  simp only [Equiv.apply_symm_apply]
  apply congrArg₂ ((q v).table w).2.2
  · exact congrArg (bits ((q v).table w).1).symm
      (funext fun i => splice_eval G.src (bits a x) z t v ((q v).src ⟨w, i⟩))
  · exact congrArg (bits ((q v).table w).2.1).symm
      (funext fun i => splice_eval G.dst (bits b y) z t v ((q v).dst ⟨w, i⟩))

/-- After fixing the old wire bits, all local contractions are independent. -/
theorem eval_plug [Field F] (hf : ∀ v, (q v).eval = (G.table v).2.2) :
    (G.plug q).eval = G.eval := by
  classical
  funext x y
  unfold eval
  trans ∑ u, ∏ v, (G.plug q).vertex x y (assignments G q u) v
  · symm
    refine ((assignments G q).sum_comp (fun z => ∏ v, (G.plug q).vertex x y z v)).trans ?_
    exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  have he (v : G.V) : G.vertex x y z v =
      ∑ t, ∏ w, (q v).vertex (G.inputAt x z v) (G.outputAt y z v) t w :=
    congrFun (congrFun (hf v).symm _) _
  simp only [he, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun w _ => vertex_plug G q x y z t v w

end OAI.LinearAlgebra.MatrixExponent.Diagram
end
