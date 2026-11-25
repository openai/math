import OAI.Hierarchy.DescentDatedNodeMetadataSeed
import OAI.Hierarchy.DescentBundleSeed
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # The exact flattened arity in each initialized node metadata cell -/
namespace Hierarchy.DescentDatedNodeMetadata.Seed
open DescentPackedSeed DescentInitialHost DescentSeedRoot DescentKernelHistory DescentBundleHistory DescentSixParty
open DescentSIMDLookup Computability.BorderVNP.Crossing Catalyst
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k n R s p H : ℕ} (X : Approximation F k n)

def arities (host : Vertex X↪Fin H) (N : ℕ) (h : Fin H) :=
  (DescentSeedInitialTable.rack X host h).map (fun v=>legArity X v*N)

private theorem uniform_arity {Tag A : Type} {width : A → ℕ} {r : BitRecipe Tag A width}
    (hp : 0 < p) (shape : DescentBundleHistory.Shape p r) (u : r.Node) (groups : ℕ)
    (size : ∀ i, shape.groups u i = groups)
    (units : ∀ i g, (shape.chunk u i g).count = 1) :
    (shape.recipe hp).arity u = r.arity u * groups := by
  refine (Shape.recipe_refs hp shape u).trans ?_
  calc
    _ = ∑ _ : Fin (r.arity u), groups := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [units, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Nat.mul_one] using size i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem original (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X) (hp : 0<p) (multiple : p∣s)
    (node : (initialRecipe X R s c ⟨j,v⟩).Node) :
    (((initialShape X R s c ⟨j,v⟩ hp multiple).recipe hp).arity node)=legArity X v*(s/p) :=by
  have count := uniform_arity hp (initialShape X R s c ⟨j,v⟩ hp multiple) node (s / p)
    (initial_groups X R s c ⟨j,v⟩ hp multiple node) (fun _ _ => rfl)
  have arity : (initialRecipe X R s c ⟨j,v⟩).arity node = legArity X v := by
    cases v with
    | inl site =>
      exact @Fintype.card_congr _ _ _ _ (Equiv.refl (LocalBoundary X (.inl site)))
    | inr pin => rfl
  exact count.trans (congrArg (fun n : ℕ => n * (s / p)) arity)

theorem live (host : Vertex X↪Fin H) (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X)
    (hp : 0<p) (multiple : p∣s) (node : (initialRecipe X R s c ⟨j,v⟩).Node) :
    arities X host (s/p) (host v)=some (((initialShape X R s c ⟨j,v⟩ hp multiple).recipe hp).arity node) :=by
  rw [original X c j v hp multiple node]
  simp only [arities,DescentSeedInitialTable.rack_real,Option.map_some]

omit [Field F] in
theorem empty (host : Vertex X↪Fin H) (h : Fin H) (N : ℕ) (unused : ¬∃v,host v=h) : arities X host N h=none:=by
  have vacant : DescentSeedInitialTable.rack X host h = none := dite_eq_right unused
  exact congrArg (Option.map (fun v : Vertex X => legArity X v * N)) vacant

end
end Hierarchy.DescentDatedNodeMetadata.Seed

end OAI
