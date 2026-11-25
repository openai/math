import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackTable
import OAI.Optimization.LinearProgramming.PriceGame.MarketGrid

/-! The deployed bit-stack Bellman table serializes precisely the finite-quiver witnesses
of the rational market proof, including tie order and the identifiers of each chosen arc. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Table
open ExactQuantumFactoring.BitStackProgram
open Potentials Quiver

variable {V : Type*} [Quiver V] {n : ℕ}
variable (index : V ≃ Fin n) (w : ∀ {a b : V}, (a ⟶ b) → ℚ) (r : V → ℚ)
variable (out : (a : V) → List (Σ b : V, a ⟶ b))
variable (ident : ∀ {a b : V}, (a ⟶ b) → ℕ)

def pathIds {a : V} : {b : V} → Path a b → List ℕ
  | _, .nil => []
  | _, .cons p e => pathIds p ++ [ident e]

theorem pathIds_comp {a b c : V} (p : Path a b) (q : Path b c) :
    pathIds ident (p.comp q) = pathIds ident p ++ pathIds ident q := by
  induction q with
  | nil => simp [pathIds]
  | cons q e ih => simp [Path.comp, pathIds, ih, List.append_assoc]

def serializePlan (D : ℕ) {a : V} (p : Plan w r a) : Item :=
  ((Grid.coordinate D p.total, p.steps), pathIds ident p.path)

def serializeValues (D : ℕ) (p : (a : V) → Plan w r a) : List Item :=
  (List.finRange n).map (fun j => serializePlan w r ident D (p (index.symm j)))

def serializeArc (D : ℕ) {a : V} (je : Σ b : V, a ⟶ b) : Arc :=
  (((index je.1).val, Grid.scaleInput D (w je.2)), ident je.2)

def serializeRow (D : ℕ) (a : V) : Row :=
  (Grid.scaleInput D (r a), (out a).map (serializeArc index w ident D))

def serializeGraph (D : ℕ) : Graph :=
  (List.finRange n).map fun j => serializeRow index w r out ident D (index.symm j)

private def refkey {a : V} (p : Plan w r a) : ℚ ×ₗ OrderDual ℕ := toLex (p.total, p.steps)

private def pref {a : V} (p q : Plan w r a) := if refkey w r p < refkey w r q then q else p

private theorem pick_eq_fold {a : V} (p : Plan w r a) (qs : List (Plan w r a)) :
    Plan.pick p qs = qs.foldl (pref w r) p := by
  let cmp := fun x y : Plan w r a => refkey w r y < refkey w r x
  have aux (l : List (Plan w r a)) (x : Plan w r a) :
      l.foldl (List.argAux cmp) (some x) = some (l.foldl (pref w r) x) := by
    induction l generalizing x with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.foldl_cons]
      by_cases h : refkey w r x < refkey w r y
      · simpa [List.argAux, cmp, pref, h] using ih y
      · simpa [List.argAux, cmp, pref, h] using ih x
  change (((p::qs).argmax (refkey w r)).getD p) = _
  change (qs.foldl (List.argAux cmp) (some p)).getD p = _
  rw [aux]; rfl

variable (D : ℕ) (hD : 0 < D)
variable (edgegrid : ∀ {a b : V} (e : a ⟶ b), NumberBounds.OnGrid D (w e))
variable (endgrid : ∀ a, NumberBounds.OnGrid D (r a))

include edgegrid endgrid in
private theorem plan_grid {a : V} (p : Plan w r a) : NumberBounds.OnGrid D p.total := by
  rw [p.total_spec]
  exact NumberBounds.OnGrid.add (weight_denominator w D edgegrid p.path) (endgrid p.finish)

include hD edgegrid endgrid in
private theorem winner_serializes {a : V} (p q : Plan w r a) :
    winner (serializePlan w r ident D p,serializePlan w r ident D q) =
      serializePlan w r ident D (pref w r p q) := by
  have hpos : (0 : ℚ) < D := by exact_mod_cast hD
  have hP := Grid.coordinate_cast (plan_grid w r D edgegrid endgrid p)
  have hQ := Grid.coordinate_cast (plan_grid w r D edgegrid endgrid q)
  have hlt : Grid.coordinate D p.total < Grid.coordinate D q.total ↔ p.total < q.total := by
    rw [← Int.cast_lt (R := ℚ), hP, hQ, mul_lt_mul_iff_of_pos_left hpos]
  have heq : Grid.coordinate D p.total = Grid.coordinate D q.total ↔ p.total = q.total := by
    rw [← Int.cast_inj (α := ℚ), hP, hQ, mul_right_inj' hpos.ne']
  have href : refkey w r p < refkey w r q ↔
      p.total < q.total ∨ p.total = q.total ∧ q.steps < p.steps := Prod.Lex.toLex_lt_toLex
  by_cases h : refkey w r p < refkey w r q
  · rw [pref, ite_eq_left h]
    have h' := href.mp h
    simp [winner, improves, serializePlan, hlt, heq, h']
  · rw [pref, ite_eq_right h]
    have h' := mt href.mpr h
    simp [winner, improves, serializePlan, hlt, heq, h']

include hD edgegrid endgrid in
private theorem fold_serializes {a : V} (p : Plan w r a) (xs : List (Plan w r a)) :
    (xs.map (serializePlan w r ident D)).foldl (fun b a => winner (b,a)) (serializePlan w r ident D p) =
    serializePlan w r ident D (Plan.pick p xs) := by
  rw [pick_eq_fold]
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, winner_serializes w r ident D hD edgegrid endgrid]
    exact ih _

theorem neighbor_serializes (p : (a : V) → Plan w r a) {a : V} (e : Σ b : V, a ⟶ b) :
    neighbor (serializeValues index w r ident D p) (serializeArc index w ident D e) =
      serializePlan w r ident D (p e.1) := by
  have hi : (index e.1).val < (List.finRange n).length := by simp
  have he : (List.finRange n)[(index e.1).val]? = some (index e.1) := by
    rw [List.getElem?_eq_getElem hi]
    simp only [List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [neighbor, serializeValues, serializeArc, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_map, he, Option.map_some, Option.getD_some]
  exact congrArg (fun v => serializePlan w r ident D (p v)) (index.symm_apply_apply e.1)

include hD edgegrid endgrid in
private theorem extend_serializes (p : (a : V) → Plan w r a) {a : V} (e : Σ b : V, a ⟶ b) :
    extend (serializeValues index w r ident D p, serializeArc index w ident D e) =
      serializePlan w r ident D (Plan.prepend e.2 (p e.1)) := by
  simp only [extend,neighbor_serializes]
  simp [serializePlan, serializeArc, nextKey, Plan.prepend, pathIds_comp, Quiver.Hom.toPath, pathIds,
    Grid.scaleInput_eq hD (edgegrid e.2), Grid.coordinate_add (edgegrid e.2)
      (plan_grid w r D edgegrid endgrid (p e.1)), add_comm]

include hD edgegrid endgrid in
theorem serialize_layer (k : ℕ) :
    layer (serializeGraph index w r out ident D,
      serializeValues index w r ident D fun v => Layer.lookup index (plans index w r out k) v) =
      serializeValues index w r ident D fun v => Layer.lookup index (plans index w r out (k+1)) v := by
  let current (v : V) := Layer.lookup index (plans index w r out k) v
  simp only [layer, serializeGraph,serializeValues,List.map_map]
  apply List.map_congr_left
  intro j _
  let a := index.symm j
  change rowResult (serializeValues index w r ident D current,serializeRow index w r out ident D a) = _
  let proposals := (out a).map fun e => Plan.prepend e.2 (current e.1)
  have hm : (((out a).map (serializeArc index w ident D)).map fun e =>
      extend (serializeValues index w r ident D current,e)) = proposals.map (serializePlan w r ident D) := by
    simp only [proposals, List.map_map]
    apply List.map_congr_left
    intro e _
    exact extend_serializes index w r ident D hD edgegrid endgrid current e
  have hs : start (serializeRow index w r out ident D a) = serializePlan w r ident D (Plan.stop w r a) := by
    simp [start,serializeRow,serializePlan,Plan.stop,pathIds,Grid.scaleInput_eq hD (endgrid a)]
  change (((out a).map _).map _).foldl _ (start (serializeRow index w r out ident D a)) = _
  rw [hm, hs, fold_serializes w r ident D hD edgegrid endgrid]
  simp only [plans, Layer.lookup_tabulate]
  rfl

include hD edgegrid endgrid in
theorem solve_serializes (k : ℕ) :
    solve (k, serializeGraph index w r out ident D) =
      serializeValues index w r ident D fun v => Layer.lookup index (plans index w r out k) v := by
  let G := serializeGraph index w r out ident D
  suffices h : (update^[k]) (G,G.map start) = (G,serializeValues index w r ident D
      fun v => Layer.lookup index (plans index w r out k) v) from congrArg Prod.snd h
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Prod.mk.injEq, true_and]
    simp only [G, serializeGraph, serializeValues, List.map_map]
    apply List.map_congr_left
    intro j _
    change start (serializeRow index w r out ident D (index.symm j)) =
      serializePlan w r ident D (Layer.lookup index (plans index w r out 0) (index.symm j))
    rw [plans, Layer.lookup_tabulate]
    simp [start, serializeRow, serializePlan, Plan.stop, pathIds,
      Grid.scaleInput_eq hD (endgrid (index.symm j))]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    exact congrArg (fun t => (G,t)) (serialize_layer index w r out ident D hD edgegrid endgrid k)

include hD edgegrid endgrid in
theorem deploy_exact (o : OracleSpec.WordOracle) (k : ℕ) :
    let data := prodCode (fun h : ℕ => List.replicate h true) graphCode (k, serializeGraph index w r out ident D)
    (OracleSpec.BitCode.deploy solveProgram).ComputesWithin o data
      (3*solveProgram.bound.eval data.length+2*data.length+2)
      (fun history bits => history = [] ∧ bits = valuesCode (serializeValues index w r ident D
        fun v => Layer.lookup index (plans index w r out k) v)) := by
  have h := solve_deploy o (k, serializeGraph index w r out ident D)
  dsimp only at h ⊢
  rwa [solve_serializes index w r out ident D hD edgegrid endgrid] at h

end Table
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
