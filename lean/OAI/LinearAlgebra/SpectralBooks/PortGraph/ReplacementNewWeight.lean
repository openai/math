import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementNewWeightPadding
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSmall
import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementClosure

/-! # Factoring the accepted forward replacement weight along its paired stubs -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph.ReplacementTemplate

open UniformDecorations

variable {O J I A : Type} {T : J → ReplacementTemplate.{0,0,0}}
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] {s : ℕ}

/-- The single role table, reading internal and exterior incidences separately. -/
def roleTable (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A) (j : J) :
    (T j).graph.StubTable (T j).attach (Bits s) A :=
  fun v y b => C ⟨j,v⟩ (Sum.elim y b ∘ localPortEquiv T ⟨j,v⟩)

/-- Lift local internal/stub tables to the uniform tagged-port address used
by the smaller tensor table. -/
def roleCoefficient (U : (j : J) → (T j).graph.StubTable (T j).attach (Bits s) A) :
    (a : RoleLabel T) → (RolePort T a → Bits s) → A :=
  fun a x => U a.1 a.2 (fun p => x ((localPortEquiv T a).symm (.inl p)))
    (fun b => x ((localPortEquiv T a).symm (.inr b)))

omit [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] in
@[simp] theorem roleTable_roleCoefficient
    (U : (j : J) → (T j).graph.StubTable (T j).attach (Bits s) A) (j : J) :
    roleTable (roleCoefficient U) j = U j := by
  funext v y b
  simp only [roleTable, roleCoefficient, Function.comp_apply, Equiv.apply_symm_apply,
    Sum.elim_inl, Sum.elim_inr]

namespace Forward

variable (tag : O ↪ J) (P : StubPairing (fun i => (T (tag i)).Stub))
local notation "G" => graph tag P
local notation "L" => label (T := T) tag

private def insidePort (i : O) {v : (T (tag i)).Role} (p : (T (tag i)).graph.Port v) :
    (G).Port ⟨i,v⟩ :=
  ⟨(.inr ⟨i,p.1.1⟩,p.1.2), (P.vertex_internal (pieces (T := T) tag) i p.1.1 p.1.2).trans
    (congrArg (Sigma.mk i) p.2)⟩

private def outsidePort (i : O) {v : (T (tag i)).Role} (b : {s // (T (tag i)).attach s = v}) :
    (G).Port ⟨i,v⟩ :=
  let d := P.ends.symm ⟨i,b.1⟩
  ⟨(.inl d.1,d.2), by
    rw [StubPairing.vertex_exterior]
    unfold StubPairing.outside
    change (fun s : Σ j, (T (tag j)).Stub => (⟨s.1,(T (tag s.1)).attach s.2⟩ :
      StubPairing.Vertex (pieces (T := T) tag))) (P.ends (P.ends.symm ⟨i,b.1⟩)) = _
    rw [Equiv.apply_symm_apply]
    exact congrArg (Sigma.mk i) b.2⟩

private theorem read_outsidePort (i : O) {v : (T (tag i)).Role} (b : {s // (T (tag i)).attach s = v}) :
    portRole tag P ⟨i,v⟩ (outsidePort tag P i b) = tagPort T (tag i) v (.inr b) := by
  apply Subtype.ext
  change Sum.inr (liftTag tag (fun j => (T j).Stub) (P.ends (P.ends.symm ⟨i,b.1⟩))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private def splitWireValues (D : Type) :
    (P.Edge (pieces (T := T) tag) → D) ≃ ((P.Wire → D) × ((i : O) → (T (tag i)).Wire → D)) :=
  (Equiv.sumArrowEquivProdArrow _ _ D).trans
    ((Equiv.refl _).prodCongr (Equiv.piCurry (fun _ _ => D)))

/-- The exact product of open weights on a forward assembly. An entry of an
exterior wire is shared by the two saved stub endpoints. -/
theorem contraction_eq_openValues [Fintype O] [CommSemiring A]
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
    (read : (v : StubPairing.Vertex (pieces (T := T) tag)) → (G).Port v ≃ RolePort T (L v))
    (hread : ∀ v p, read v p = portRole tag P v p) :
    (G).contraction (A := fun _ => Bits s) (fun v a => C (L v) (a ∘ (read v).symm)) =
      ∑ x : P.Wire → Bits s, ∏ i : O, (T (tag i)).graph.openValue (T (tag i)).attach
        (roleTable C (tag i)) (fun b => x (P.ends.symm ⟨i,b⟩).1) := by
  unfold contraction openValue
  simp_rw [Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  let eqv := splitWireValues tag P (Bits s)
  refine Finset.sum_nbij' eqv eqv.symm (fun _ _ => by simp) (fun _ _ => by simp)
    (fun a _ => eqv.symm_apply_apply a) (fun x _ => eqv.apply_symm_apply x) ?_
  intro a _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (C ⟨tag i,v⟩)
  funext p
  obtain ⟨p,rfl⟩ := (localPortEquiv T ⟨tag i,v⟩).symm.surjective p
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  cases p with
  | inl d =>
    have he : (read ⟨i,v⟩).symm (tagPort T (tag i) v (.inl d)) = insidePort tag P i d :=
      (read ⟨i,v⟩).symm_apply_eq.mpr (hread ⟨i,v⟩ (insidePort tag P i d)).symm
    exact congrArg ((G).atVertex a ⟨i,v⟩) he
  | inr b =>
    have he : (read ⟨i,v⟩).symm (tagPort T (tag i) v (.inr b)) = outsidePort tag P i b :=
      (read ⟨i,v⟩).symm_apply_eq.mpr
        ((hread ⟨i,v⟩ _).trans (read_outsidePort tag P i b)).symm
    exact congrArg ((G).atVertex a ⟨i,v⟩) he

variable [Fintype O] [DecidableEq (StubPairing.Vertex (pieces (T := T) tag))]

/-- Read the accepted uniform-table weight on the actual rooted map assembled
from these pieces. The sole condition on its port order says that its numbering
is the one transported from the catalogue templates. -/
theorem roleContraction_eq_openValues [CommSemiring A] (R : LocalRules (I := I) T)
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
    (root : StubPairing.Vertex (pieces (T := T) tag)) (num : (G).Numbering)
    (degree : ∀ v, Fintype.card ((G).Port v) ≤ 4) (connected : (G).ConnectedFrom root)
    (slot : ∀ v p, (num v p).val = (R.slot _ (portRole tag P v p)).val) :
    let M : RootedMap _ _ := ⟨G,root,num,degree,connected⟩
    ∀ hz : R.Accepts M L, R.roleContraction M C ⟨L,hz⟩ =
      ∑ x : P.Wire → Bits s, ∏ i : O, (T (tag i)).graph.openValue (T (tag i)).attach
        (roleTable C (tag i)) (fun b => x (P.ends.symm ⟨i,b⟩).1) := by
  intro M hz
  let hv := hz.2.2.choose
  apply contraction_eq_openValues tag P C (fun v => Equiv.ofBijective _ (readPort_bijective hv v))
  intro v p
  apply (R.slot (L v)).injective
  exact (readPort_spec hv p).1.trans (Fin.ext (slot v p))

omit [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] in
private theorem slot_eq_endNumber (slot : Numbering T) {a : RoleLabel T} (p : RolePort T a) :
    slot a p = endNumber slot p.val := by rcases p with ⟨p,rfl⟩; rfl

/-- In terms of a named representative, its incidence and the recorded numbers
of the paired ends are sufficient to identify the open-factor expansion. -/
theorem mapWeight_eq_openValues [CommSemiring A] (R : LocalRules (I := I) T)
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
    (M : RootedMap (StubPairing.Vertex (pieces (T := T) tag)) (P.Edge (pieces (T := T) tag)))
    (src : M.graph = G)
    (ports : ∀ e b, M.portNumber e b = (endNumber R.slot (namedEnd tag P (e,b))).val)
    (hz : R.Accepts M L) : R.roleContraction M C ⟨L,hz⟩ =
      ∑ x : P.Wire → Bits s, ∏ i : O, (T (tag i)).graph.openValue (T (tag i)).attach
        (roleTable C (tag i)) (fun b => x (P.ends.symm ⟨i,b⟩).1) := by
  obtain ⟨g,root,num,degree,connected⟩ := M
  change g = G at src
  subst g
  refine roleContraction_eq_openValues tag P R C root num degree connected ?_ hz
  rintro _ ⟨⟨e,b⟩,rfl⟩
  rw [slot_eq_endNumber]
  exact ports e b

/-- The same weight over the original alphabet, using the actual zero support
and the actual open tensors computed by the selected tree terms. -/
theorem mapWeight_eq_oldWidthValues [CommSemiring A] (R : LocalRules (I := I) T)
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
    (M : RootedMap (StubPairing.Vertex (pieces (T := T) tag)) (P.Edge (pieces (T := T) tag)))
    (src : M.graph = G)
    (ports : ∀ e b, M.portNumber e b = (endNumber R.slot (namedEnd tag P (e,b))).val)
    (hz : R.Accepts M L) {q : ℕ} (hq : q ≤ 2^s)
    (term : (i : O) → ((T (tag i)).Stub → Fin q) → A)
    (hzero : ∀ i y b, q ≤ (y b).val → (T (tag i)).graph.openValue (T (tag i)).attach
      (roleTable C (tag i)) y = 0)
    (hlegal : ∀ i x, (T (tag i)).graph.openValue (T (tag i)).attach (roleTable C (tag i))
      (fun b => (x b).castLE hq) = term i x) :
    R.roleContraction M C ⟨L,hz⟩ =
      ∑ x : P.Wire → Fin q, ∏ i, term i (fun b => x (P.ends.symm ⟨i,b⟩).1) :=
  (mapWeight_eq_openValues tag P R C M src ports hz).trans
    (P.sum_boundary_eq_original hq _ term hzero hlegal)

/-- Apply the padding identity supplied by every record term's
`openValue_all`. The result is indexed by the old exterior wire states. -/
theorem mapWeight_of_paddedTerms [CommSemiring A] (R : LocalRules (I := I) T)
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
    (M : RootedMap (StubPairing.Vertex (pieces (T := T) tag)) (P.Edge (pieces (T := T) tag)))
    (src : M.graph = G)
    (ports : ∀ e b, M.portNumber e b = (endNumber R.slot (namedEnd tag P (e,b))).val)
    (hz : R.Accepts M L) {q : ℕ} (hq : q ≤ 2^s)
    (term : (i : O) → ((T (tag i)).Stub → Fin q) → A)
    (hpad : ∀ i y, (T (tag i)).graph.openValue (T (tag i)).attach (roleTable C (tag i)) y =
      padStubs (term i) y) :
    R.roleContraction M C ⟨L,hz⟩ =
      ∑ x : P.Wire → Fin q, ∏ i, term i (fun b => x (P.ends.symm ⟨i,b⟩).1) := by
  apply mapWeight_eq_oldWidthValues tag P R C M src ports hz hq term
  · intro i y b hb
    rw [hpad]
    exact dite_eq_right (fun h => (h b).not_ge hb)
  · intro i x
    rw [hpad, padStubs_castLE]

end Forward
end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
