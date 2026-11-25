import OAI.Hierarchy.ProbeColumnWires

namespace OAI
/-! # Paths inside the induced finite core of a radius test -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical
noncomputable section

variable {V : Type*} [DecidableEq V] (next : V → Finset V) (root : V) (radius : ℕ)

private theorem grow {r s : ℕ} (hrs : r ≤ s) : neighborhood next root r ⊆ neighborhood next root s := by
  induction hrs with
  | refl => exact fun _ h => h
  | step _ prev => exact fun y mem => (mem_neighborhood_step next root y _).mpr ⟨_,prev mem,Or.inl rfl⟩

abbrev TestColumns := ↥(neighborhood next root radius)

def testBase : TestColumns next root radius := ⟨root,grow next root (Nat.zero_le radius) (Finset.mem_singleton_self _)⟩

def testNext (x : TestColumns next root radius) : Finset (TestColumns next root radius) :=
  (next x.val).subtype (· ∈ neighborhood next root radius)

/-- A shortest path to an r-ball stays inside it. This is an induced-graph statement:
its output walks through genuine local socket ordinals, all of whose intermediate sites
belong to this one finite test. -/
theorem inside_test {r : ℕ} (le : r≤radius) {v : V} (inside : v∈neighborhood next root r) :
    (⟨v,grow next root le inside⟩ : TestColumns next root radius) ∈
    neighborhood (testNext next root radius) (testBase next root radius) r := by
  induction r generalizing v with
  | zero =>
    have h := Finset.mem_singleton.mp inside
    subst v; exact Finset.mem_singleton_self _
  | succ r ih =>
    obtain ⟨u,hu,step⟩ := (mem_neighborhood_step next root v r).mp inside
    have room : r≤radius := by omega
    apply (mem_neighborhood_step _ _ _ _).mpr
    refine ⟨⟨u,grow next root room hu⟩,ih room hu,?_⟩
    exact step.imp Subtype.ext (fun edge => Finset.mem_subtype.mpr edge)

theorem each_in_test (v : TestColumns next root radius) :
    v ∈ neighborhood (testNext next root radius) (testBase next root radius) radius :=
  inside_test next root radius le_rfl v.property

/-- Restricting a socket bank to a ball cannot increase degree. -/
theorem test_degree (D : ℕ) (deg : ∀ x, (next x).card ≤ D) (v : TestColumns next root radius) :
    (testNext next root radius v).card ≤ D := by
  rw [testNext,Finset.card_subtype]
  exact (Finset.card_filter_le ..).trans (deg _)

/-- Every vertex is genuinely joined to the root, as witnessed by the nonempty induced
horizontal menu. Multiple incidences between the same pair are allowed. -/
theorem test_connects {H : Type*} (hor : H → DistinctPair (TestColumns next root radius))
    (hosts : ∀ x y, y∈testNext next root radius x → ∃ e, ((hor e).left=x ∧ (hor e).right=y) ∨
      ((hor e).left=y ∧ (hor e).right=x)) (v : TestColumns next root radius) :
    Relation.EqvGen (fun x y => ∃ e, (hor e).left=x ∧ (hor e).right=y) (testBase next root radius) v := by
  let P := fun (i j : TestColumns next root radius) (_ : ℕ) => Relation.EqvGen
    (fun x y => ∃ e, (hor e).left=x ∧ (hor e).right=y) i j
  apply ball_path_bound (P:=P) _ _ _ _ _ (each_in_test next root radius v)
  · exact fun i => .refl i
  · intro i j link
    obtain ⟨e,fwd|rev⟩ := hosts i j link
    · exact .rel _ _ ⟨e,fwd⟩
    · exact .symm _ _ (.rel _ _ ⟨e,rev⟩)
  · exact fun _ _ _ _ _ a b => .trans _ _ _ a b
  · exact fun _ _ _ h => h

/-- The operative K in the local flattening statement is twice the radius, at every
signed layer, for every actual pair of vertices in one tested socket neighborhood. -/
theorem test_diameter {H E : Type*} {k : ℕ} [SiteNaming (ColumnSite (TestColumns next root radius) k)] (hor : H → DistinctPair (TestColumns next root radius))
    (extra : E → DistinctPair (ColumnSite (TestColumns next root radius) k))
    (M : ℝ) (len : H → ℝ) (price : E → ℝ) (hosts : ∀ x y, y∈testNext next root radius x →
      ∃ e, len e ≤ 1 ∧ (((hor e).left=x ∧ (hor e).right=y) ∨ ((hor e).left=y ∧ (hor e).right=x)))
    (i j : TestColumns next root radius) (layer : ColumnLayer k) :
    WireBound (ColumnWires.wires hor extra) (ColumnWires.quote M len price)
      (ColumnWires.site i layer) (ColumnWires.site j layer) (2*radius) := by
  have bound (v : TestColumns next root radius) := ColumnWires.bounded_ball (horizontal:=hor) (extra:=extra)
    M len price (testNext next root radius) hosts (each_in_test next root radius v) layer
  simpa only [two_mul] using (bound i).symm.append (bound j)

end
end Hierarchy.AdaptiveProbe

end OAI
