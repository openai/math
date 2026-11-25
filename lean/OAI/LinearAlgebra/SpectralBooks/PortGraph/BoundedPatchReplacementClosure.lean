import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchRootCost
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass

/-! # Closing the named stubs of a patch

Each stub acquires its own polygon vertex carrying an identity matrix. The
old vertices and the stub vertices can occupy any prescribed polygon sites.
Closing the stubs this way does not change the value for any boundary indices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical BigOperators
noncomputable section

namespace PortGraph

open PlanarPatch

variable {V E B J : Type*} (G : PortGraph V E) (attach : B → V) (order : V ⊕ B ≃ J)

/-- The closed incidence graph, with a new wire leading to each named stub. -/
def closeStubs : PortGraph J (E ⊕ B) where
  tail := Sum.elim (fun e => order (.inl (G.tail e))) (fun b => order (.inl (attach b)))
  head := Sum.elim (fun e => order (.inl (G.head e))) (fun b => order (.inr b))

@[simp] theorem closeStubs_vertex_inl (e : E) (b : Bool) :
    (G.closeStubs attach order).vertex (.inl e) b = order (.inl (G.vertex e b)) := by cases b <;> rfl

/-- Local ports of the closed graph correspond exactly to the old internal ports and stubs. -/
def closeOriginalPorts (v : V) : G.Port v ⊕ {b // attach b = v} ≃
    (G.closeStubs attach order).Port (order (.inl v)) where
  toFun
    | .inl p => ⟨(.inl p.1.1, p.1.2), by simp [p.2]⟩
    | .inr b => ⟨(.inr b.1, false), congrArg (fun t => order (.inl t)) b.2⟩
  invFun p := by
    obtain ⟨⟨e,b⟩,h⟩ := p
    rcases e with e | s
    · exact .inl ⟨(e,b), by simpa using h⟩
    · cases b with
      | false => exact .inr ⟨s, Sum.inl.inj (order.injective h)⟩
      | true => cases order.injective h
  left_inv p := by rcases p with ⟨⟨e,b⟩,h⟩ | ⟨s,h⟩ <;> rfl
  right_inv p := by
    obtain ⟨⟨e,b⟩,h⟩ := p
    rcases e with e | s
    · rfl
    · cases b with
      | false => rfl
      | true => cases order.injective h

def closeStubPort (b : B) : (G.closeStubs attach order).Port (order (.inr b)) :=
  ⟨(.inr b, true),rfl⟩

theorem eq_closeStubPort (b : B) (p : (G.closeStubs attach order).Port (order (.inr b))) :
    p = G.closeStubPort attach order b := by
  obtain ⟨⟨e,t⟩,h⟩ := p
  rcases e with e | s
  · simp at h
  · cases t with
    | false => cases order.injective h
    | true =>
      have := Sum.inr.inj (order.injective h)
      subst s
      rfl

/-- Tables with homogeneous internal and free indices. -/
abbrev StubTable (D R : Type*) :=
  (v : V) → (G.Port v → D) → ({b : B // attach b = v} → D) → R

/-- Sum the internal indices of a patch, holding its named exterior indices fixed. -/
def openValue {D R : Type*} [Fintype E] [Fintype V] [Fintype D] [CommSemiring R]
    (u : G.StubTable attach D R) (x : B → D) : R :=
  ∑ y : E → D, ∏ v, u v (G.atVertex y v) (fun b => x b.1)

def closedCorners {R : Type*} [CommSemiring R] {q : ℕ} (u : G.StubTable attach (Fin q) R)
    (i : J) : CornerTable R (fun _ : B => q) ((G.closeStubs attach order).Port i → Fin q) :=
  Equiv.piCongrLeft (fun i => CornerTable R (fun _ : B => q)
    ((G.closeStubs attach order).Port i → Fin q)) order
    (fun vb => match vb with
      | .inl v => .scalar (fun a => u v (fun p => a (G.closeOriginalPorts attach order v (.inl p)))
          (fun b => a (G.closeOriginalPorts attach order v (.inr b))))
      | .inr b => .stub b (fun a c => if a (G.closeStubPort attach order b) = c then 1 else 0)) i

@[simp] theorem closedCorners_inl {R : Type*} [CommSemiring R] {q : ℕ}
    (u : G.StubTable attach (Fin q) R) (v : V) :
    G.closedCorners attach order u (order (.inl v)) =
    .scalar (fun a => u v (fun p => a (G.closeOriginalPorts attach order v (.inl p)))
      (fun b => a (G.closeOriginalPorts attach order v (.inr b)))) := by
  apply Equiv.piCongrLeft_apply_apply

@[simp] theorem closedCorners_inr {R : Type*} [CommSemiring R] {q : ℕ}
    (u : G.StubTable attach (Fin q) R) (b : B) :
    G.closedCorners attach order u (order (.inr b)) =
    .stub b (fun a c => if a (G.closeStubPort attach order b) = c then 1 else 0) := by
  apply Equiv.piCongrLeft_apply_apply

/-- The identity at each new vertex pins exactly one wire. This applies to loops
and parallel edges in the original graph without changing their multiplicity. -/
theorem openValue_eq_closed {R : Type*} [CommSemiring R] [Fintype E] [Fintype V] [Fintype B]
    [Fintype J] {q : ℕ} (u : G.StubTable attach (Fin q) R) (x : B → Fin q) :
    G.openValue attach u x = (G.closeStubs attach order).contraction (A := fun _ => Fin q)
      (fun i => (G.closedCorners attach order u i).value x) := by
  unfold openValue contraction
  symm
  let T (a : E ⊕ B → Fin q) := ∏ i, (G.closedCorners attach order u i).value x
    ((G.closeStubs attach order).atVertex a i)
  trans ∑ a, T a
  · exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
  trans ∑ yz : (E → Fin q) × (B → Fin q), T (Sum.elim yz.1 yz.2)
  · exact Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow E B (Fin q)) _ _ (fun a => by
      congr 1
      funext i
      cases i <;> rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have split (z : B → Fin q) :
      (∏ v, (G.closedCorners attach order u v).value x
        ((G.closeStubs attach order).atVertex (Sum.elim y z) v)) =
      (∏ v, u v (G.atVertex y v) (fun b => z b.1)) *
      ∏ b, (if z b = x b then (1:R) else 0) := by
    rw [← order.prod_comp (fun v => (G.closedCorners attach order u v).value x
      ((G.closeStubs attach order).atVertex (Sum.elim y z) v)), Fintype.prod_sum_type]
    simp only [closedCorners_inl, closedCorners_inr, CornerTable.value]
    rfl
  change ∑ z : B → Fin q, (∏ v, (G.closedCorners attach order u v).value x
      ((G.closeStubs attach order).atVertex (Sum.elim y z) v)) = _
  simp_rw [split, Fintype.prod_boole, ← funext_iff]
  simp

/-- The cyclic polygon order lists precisely the named stubs, skipping ordinary vertices. -/
def stubLabel (order : V ⊕ B ≃ J) (i : J) : Option B :=
  (order.symm i).elim (fun _ => none) some

theorem closedCorners_label {R : Type*} [CommSemiring R] {q : ℕ}
    (u : G.StubTable attach (Fin q) R) (i : J) :
    (G.closedCorners attach order u i).label = stubLabel order i := by
  obtain ⟨v,rfl⟩ := order.surjective i
  cases v <;> simp [stubLabel, CornerTable.label]

theorem closedCorners_formula {F I : Type*} [Field F] {q : ℕ}
    (u : G.StubTable attach (Fin q) (MvPolynomial I F))
    (hu : ∀ v a s, HasFormula 1 (u v a s)) (i : J) :
    (G.closedCorners attach order u i).FormulaBound 1 := by
  obtain ⟨v,rfl⟩ := order.surjective i
  cases v with
  | inl v => rw [closedCorners_inl]; exact fun a => hu _ _ _
  | inr b =>
    rw [closedCorners_inr]
    intro a c
    dsimp only
    split
    · simpa using HasFormula.const (I := I) (1 : F)
    · simpa using HasFormula.const (I := I) (0 : F)

variable [Fintype V] [Fintype B] [Fintype E]

/-- All original ports, including two per loop and one per boundary stub. -/
theorem total_ports_with_stubs :
    ∑ v, (Fintype.card (G.Port v) + Fintype.card {b // attach b = v}) =
      Fintype.card E * 2 + Fintype.card B := by
  rw [Finset.sum_add_distrib, ← Fintype.card_sigma, ← Fintype.card_sigma,
    Fintype.card_congr (Equiv.sigmaFiberEquiv fun t : E × Bool => G.vertex t.1 t.2),
    Fintype.card_congr (Equiv.sigmaFiberEquiv attach), Fintype.card_prod, Fintype.card_bool]

theorem closed_size_bounds {K : ℕ} (hK : Fintype.card V ≤ K)
    (hdeg : ∀ v, Fintype.card (G.Port v) + Fintype.card {b // attach b = v} ≤ 4) :
    Fintype.card (V ⊕ B) ≤ 5*K ∧ Fintype.card (E ⊕ B) ≤ 4*K := by
  have hp := G.total_ports_with_stubs attach
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
  rw [hp] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  change Fintype.card E * 2 + Fintype.card B ≤ Fintype.card V * 4 at h
  simp only [Fintype.card_sum]
  omega

omit [Fintype V] in
theorem closed_degree_le (hdeg : ∀ v, Fintype.card (G.Port v) + Fintype.card {b // attach b = v} ≤ 4)
    (i : J) : Fintype.card ((G.closeStubs attach order).Port i) ≤ 4 := by
  obtain ⟨v,rfl⟩ := order.surjective i
  cases v with
  | inl v =>
    rw [← Fintype.card_congr (G.closeOriginalPorts attach order v), Fintype.card_sum]
    exact hdeg v
  | inr b =>
    let : Unique ((G.closeStubs attach order).Port (order (.inr b))) :=
      { default := G.closeStubPort attach order b, uniq := G.eq_closeStubPort attach order b }
    rw [Fintype.card_unique]
    decide

omit [Fintype V] [Fintype E] in
/-- Reading once around the polygon sees every stub exactly once. -/
theorem stubOrder_complete {n : ℕ} (order : V ⊕ B ≃ Fin n) :
    let l := (List.finRange n).filterMap (stubLabel order)
    l.Nodup ∧ (∀ b, b ∈ l) ∧ l.length = Fintype.card B := by
  intro l
  have inv {i : Fin n} {b : B} (h : b ∈ stubLabel order i) : i = order (.inr b) := by
    obtain ⟨v,rfl⟩ := order.surjective i
    cases v with
    | inl a => simp [stubLabel] at h
    | inr c =>
      have : c = b := by simpa [stubLabel, eq_comm] using h
      rw [this]
  have hn : l.Nodup := (List.nodup_finRange n).filterMap
    (fun i j b hi hj => (inv hi).trans (inv hj).symm)
  have hmem (b : B) : b ∈ l := List.mem_filterMap.mpr
    ⟨order (.inr b), List.mem_finRange _, by simp [stubLabel]⟩
  refine ⟨hn,hmem,?_⟩
  rw [← List.toFinset_card_of_nodup hn, show l.toFinset = Finset.univ by ext b; simp [hmem], Finset.card_univ]

omit [Fintype V] [Fintype E] in
theorem nonroot_stub_count {n : ℕ} (order : V ⊕ B ≃ Fin (n+1)) {b : B}
    (hb : order (.inr b) = Fin.last n) :
    ((List.finRange n).filterMap (fun i => stubLabel order i.castSucc)).length + 1 = Fintype.card B := by
  have h := (stubOrder_complete order).2.2
  rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map] at h
  have hlabel : stubLabel order (Fin.last n) = some b := by simp [← hb,stubLabel]
  simpa only [List.filterMap_cons, hlabel, Function.comp_def,
    List.filterMap_nil, List.length_append, List.length_cons, List.length_nil] using h

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
