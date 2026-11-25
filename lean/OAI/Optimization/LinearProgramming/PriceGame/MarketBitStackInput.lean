import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackBridge
import OAI.Optimization.LinearProgramming.PriceGame.MarketInputsMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost

/-! Rational input for the serialized Bellman computation. The bit machine collects every
edge cost and terminal reward, computes a common positive denominator, scales signed entries,
and returns this denominator with the table. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Table
namespace Input
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Quiver Potentials

abbrev RationalArc := (ℕ × ℚ) × ℕ
abbrev RationalRow := ℚ × List RationalArc
abbrev RationalGraph := List RationalRow

def rationalArcCode := prodCode (prodCode Nat.bits ratCode) Nat.bits
def rationalRowCode := prodCode ratCode (listCode rationalArcCode)
def rationalGraphCode := listCode rationalRowCode

def valuesOfRow (row : RationalRow) := row.1 :: row.2.map (fun a => a.1.2)
def coefficients (g : RationalGraph) := g.flatMap valuesOfRow
def denominator (g : RationalGraph) := (coefficients g).foldl (fun n q => n*q.den) 1

def scaledArc (D : ℕ) (arc : RationalArc) : Arc := ((arc.1.1, Grid.scaleInput D arc.1.2),arc.2)
def scaledRow (D : ℕ) (row : RationalRow) : Row := (Grid.scaleInput D row.1,row.2.map (scaledArc D))
def scaledGraph (D : ℕ) (g : RationalGraph) : Graph := g.map (scaledRow D)

/-- Signed numerator times the exact natural quotient of denominators. -/
noncomputable def scaleProgram : Procedure (prodCode Nat.bits ratCode) intCode
    (fun x => Grid.scaleInput x.1 x.2) := by
  let D := first Nat.bits ratCode
  let q := second Nat.bits ratCode
  let factor := natToInt.comp (binaryDiv.comp (D.pair (ratDen.comp q)))
  exact intMul.comp ((ratNum.comp q).pair factor)

noncomputable def scaleArcProgram : Procedure (prodCode Nat.bits rationalArcCode) arcCode
    (fun x => scaledArc x.1 x.2) := by
  let D := first Nat.bits rationalArcCode
  let arc := second Nat.bits rationalArcCode
  let data := (first (prodCode Nat.bits ratCode) Nat.bits).comp arc
  let ident := (second (prodCode Nat.bits ratCode) Nat.bits).comp arc
  let dest := (first Nat.bits ratCode).comp data
  let cost := (second Nat.bits ratCode).comp data
  exact ((dest.pair (scaleProgram.comp (D.pair cost))).pair ident).congrFun (fun _ => rfl)

noncomputable def scaleRowProgram : Procedure (prodCode Nat.bits rationalRowCode) rowCode
    (fun x => scaledRow x.1 x.2) := by
  let D := first Nat.bits rationalRowCode
  let row := second Nat.bits rationalRowCode
  let terminal := (first ratCode (listCode rationalArcCode)).comp row
  let arcs := (second ratCode (listCode rationalArcCode)).comp row
  let scaled := (mapWithContext (((0,0),0) : RationalArc) zeroArc scaleArcProgram).comp (arcs.pair D)
  exact ((scaleProgram.comp (D.pair terminal)).pair scaled).congrFun (fun _ => rfl)

noncomputable def scaleGraphProgram : Procedure (prodCode rationalGraphCode Nat.bits) graphCode
    (fun x => scaledGraph x.2 x.1) :=
  (mapWithContext ((0,[]) : RationalRow) zeroRow scaleRowProgram).congrFun (fun _ => rfl)

private noncomputable def rowCoefficientsProgram : Procedure rationalRowCode (listCode ratCode) valuesOfRow := by
  let weight := (second Nat.bits ratCode).comp (first (prodCode Nat.bits ratCode) Nat.bits)
  let list := (listMap (((0,0),0) : RationalArc) (0 : ℚ) weight).comp
    (second ratCode (listCode rationalArcCode))
  exact ((listCons ratCode).comp ((first ratCode (listCode rationalArcCode)).pair list)).congrFun
    (fun _ => rfl)

noncomputable def denominatorProgram : Procedure rationalGraphCode Nat.bits denominator := by
  let vals := listMap ((0,[]) : RationalRow) ([] : List ℚ) rowCoefficientsProgram
  exact (InputMachine.denominatorP.comp ((Learning.GenerationCost.flattenP ratCode 0).comp vals)).congrFun (fun _ => rfl)

def rationalSolve (x : ℕ × RationalGraph) : ℕ × List Item :=
  let D := denominator x.2
  (D, solve (x.1,scaledGraph D x.2))

noncomputable def rationalSolveProgram : Procedure (prodCode (fun k : ℕ => List.replicate k true) rationalGraphCode)
    (prodCode Nat.bits valuesCode) rationalSolve := by
  let uc := fun k : ℕ => List.replicate k true
  let rounds := first uc rationalGraphCode
  let graph := second uc rationalGraphCode
  let den := denominatorProgram.comp graph
  let converted := scaleGraphProgram.comp (graph.pair den)
  exact (den.pair (solveProgram.comp (rounds.pair converted))).congrFun (fun _ => rfl)

private theorem den_product (xs : List ℚ) (a : ℕ) :
    xs.foldl (fun m q => m*q.den) a = a*(xs.map Rat.den).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons q xs ih => simp [ih, mul_assoc]

theorem denominator_pos (g : RationalGraph) : 0 < denominator g := by
  rw [denominator,den_product,one_mul]
  induction coefficients g with
  | nil => simp
  | cons q xs ih => simpa using Nat.mul_pos q.den_pos ih

theorem denominator_grid (g : RationalGraph) {q : ℚ} (hq : q ∈ coefficients g) :
    NumberBounds.OnGrid (denominator g) q := by
  apply (NumberBounds.grid_iff_den_dvd (denominator_pos g) q).2
  rw [denominator,den_product,one_mul]
  exact List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)


/-- Obtain the dimension-bounded horizon directly by reading the input row list. -/
private noncomputable def listUnaryLength {α : Type} (ec : α → List Bool) (d : α) :
    Procedure (listCode ec) unaryCode List.length := by
  let advance := unarySuccessor.comp (second ec unaryCode)
  let fold := foldList d advance Polynomial.X (by
    intro xs b i
    change (unaryCode ((xs.take i).foldl (fun n _ => n+1) b)).length ≤ _
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have h := list_length_le_code ec xs
    omega)
  exact (fold.comp ((identity (listCode ec)).pair (constant (listCode ec) unaryCode 0))).congrFun
    (by intro xs; simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)

noncomputable def graphProgram : Procedure rationalGraphCode (prodCode Nat.bits valuesCode)
    (fun g => rationalSolve (g.length-1,g)) :=
  rationalSolveProgram.comp ((unaryPred.comp (listUnaryLength rationalRowCode ((0,[]) : RationalRow))).pair
    (identity rationalGraphCode))

variable {V : Type*} [Quiver V] {n : ℕ} (index : V ≃ Fin n)
variable (w : ∀ {a b : V}, (a ⟶ b) → ℚ) (r : V → ℚ)
variable (out : (a : V) → List (Σ b : V, a ⟶ b)) (ident : ∀ {a b : V}, (a ⟶ b) → ℕ)

def rawArc {a : V} (e : Σ b : V, a ⟶ b) : RationalArc :=
  (((index e.1).val,w e.2),ident e.2)
def rawRow (a : V) : RationalRow := (r a,(out a).map (rawArc index w ident))
def rawGraph : RationalGraph :=
  (List.finRange n).map (fun j => rawRow index w r out ident (index.symm j))

theorem scale_raw (D : ℕ) :
    scaledGraph D (rawGraph index w r out ident) = serializeGraph index w r out ident D := by
  simp [scaledGraph,rawGraph,serializeGraph,scaledRow,rawRow,serializeRow,scaledArc,rawArc,
    serializeArc,List.map_map,Function.comp_def]

private theorem row_mem (a : V) : rawRow index w r out ident a ∈ rawGraph index w r out ident := by
  exact List.mem_map.mpr ⟨index a,List.mem_finRange _, by rw [index.symm_apply_apply]⟩

theorem terminal_mem (a : V) : r a ∈ coefficients (rawGraph index w r out ident) := by
  apply List.mem_flatMap.mpr
  exact ⟨rawRow index w r out ident a,row_mem index w r out ident a,List.mem_cons_self⟩

theorem cost_mem (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ j : V, a ⟶ j) ∈ out a)
    {a b : V} (e : a ⟶ b) : w e ∈ coefficients (rawGraph index w r out ident) := by
  apply List.mem_flatMap.mpr
  refine ⟨rawRow index w r out ident a,row_mem index w r out ident a, List.mem_cons_of_mem _ ?_⟩
  exact List.mem_map.mpr ⟨rawArc index w ident ⟨b,e⟩,
    List.mem_map.mpr ⟨⟨b,e⟩,hout e,rfl⟩,rfl⟩

theorem rationalSolve_exact
    (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ j : V, a ⟶ j) ∈ out a) :
    let g := rawGraph index w r out ident
    let D := denominator g
    rationalSolve (g.length-1,g) = (D,serializeValues index w r ident D
      fun v => Layer.lookup index (plans index w r out (n-1)) v) := by
  let g := rawGraph index w r out ident
  let D := denominator g
  have gd : 0 < D := denominator_pos g
  have ge : ∀ {a b : V} (e : a ⟶ b), NumberBounds.OnGrid D (w e) :=
    fun e => denominator_grid g (cost_mem index w r out ident hout e)
  have gt : ∀ a, NumberBounds.OnGrid D (r a) :=
    fun a => denominator_grid g (terminal_mem index w r out ident a)
  have hl : g.length = n := by simp [g,rawGraph]
  have ref := solve_serializes index w r out ident D gd ge gt (n-1)
  change (D,solve (g.length-1, scaledGraph D g)) = _
  have hs : scaledGraph D g = serializeGraph index w r out ident D := scale_raw index w r out ident D
  rw [hl, hs, ref]

/-- One deterministic polynomial-time bit program, on the rational graph itself, produces all
scaled optima and their shortest maximizing paths. It obtains its denominator and number of
rounds from its input. -/
theorem graph_deploy_exact (o : OracleSpec.WordOracle)
    (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ j : V, a ⟶ j) ∈ out a) :
    let g := rawGraph index w r out ident
    let D := denominator g
    let data := rationalGraphCode g
    (OracleSpec.BitCode.deploy graphProgram).ComputesWithin o data
      (3*graphProgram.bound.eval data.length+2*data.length+2)
      (fun history bits => history = [] ∧ bits = prodCode Nat.bits valuesCode
        (D, serializeValues index w r ident D fun v => Layer.lookup index (plans index w r out (n-1)) v)) := by
  let g := rawGraph index w r out ident
  obtain ⟨t,c,hRun,hBound,hHalt,hHistory,hOut⟩ := OracleSpec.BitCode.deploy_correct graphProgram o g
  refine ⟨t,c,hRun,hBound,hHalt,hHistory,hOut.trans ?_⟩
  exact congrArg (prodCode Nat.bits valuesCode) (rationalSolve_exact index w r out ident hout)


/-- Rescale a table entry back to the exact rational score and retain the full arc-ID route. -/
def report (x : ℕ × Item) : ℚ × List ℕ := (mkRat x.2.1.1 x.1,x.2.2)
def reportCode := prodCode ratCode routeCode

noncomputable def reportProgram : Procedure (prodCode Nat.bits itemCode) reportCode report := by
  let D := first Nat.bits itemCode
  let item := second Nat.bits itemCode
  let key := (first keyCode routeCode).comp item
  let score := (first intCode intCode).comp key
  let path := (second keyCode routeCode).comp item
  exact ((makeRat.comp (score.pair D)).pair path).congrFun (fun _ => rfl)

def reports (z : ℕ × List Item) := z.2.map (fun x => report (z.1,x))
noncomputable def reportsProgram : Procedure (prodCode Nat.bits valuesCode) (listCode reportCode) reports :=
  ((mapWithContext zeroItem ((0 : ℚ),([] : List ℕ)) reportProgram).comp
    (swap Nat.bits valuesCode)).congrFun (fun _ => rfl)

noncomputable def rationalReportsProgram : Procedure rationalGraphCode (listCode reportCode)
    (fun g => reports (rationalSolve (g.length-1,g))) :=
  reportsProgram.comp graphProgram

theorem report_serializes {D : ℕ} (hd : 0 < D)
    (edgegrid : ∀ {a b : V} (e : a ⟶ b), NumberBounds.OnGrid D (w e))
    (terminalgrid : ∀ i, NumberBounds.OnGrid D (r i)) {v : V} (p : Plan w r v) :
    report (D,serializePlan w r ident D p) = (p.total,pathIds ident p.path) := by
  have hp : NumberBounds.OnGrid D p.total := p.total_spec ▸ NumberBounds.OnGrid.add
    (weight_denominator w D edgegrid p.path) (terminalgrid _)
  have hdq : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change (mkRat (Grid.coordinate D p.total) D,_) = _
  rw [Rat.mkRat_eq_div, Grid.coordinate_cast hp, mul_comm, mul_div_cancel_right₀ _ hdq]
  rfl

/-- Each vertex receives an attained maximal walk score and the corresponding arc identifiers
in traversal order. Every selected route is simple under the residual graph's
nonpositive-circuit hypothesis (`plans_simple`). -/
theorem reports_deploy_exact (o : OracleSpec.WordOracle)
    (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ j : V, a ⟶ j) ∈ out a) :
    let g := rawGraph index w r out ident
    let values := (List.finRange n).map fun j =>
      let p := Layer.lookup index (plans index w r out (n-1)) (index.symm j)
      (p.total,pathIds ident p.path)
    (OracleSpec.BitCode.deploy rationalReportsProgram).ComputesWithin o (rationalGraphCode g)
      (3*rationalReportsProgram.bound.eval (rationalGraphCode g).length+2*(rationalGraphCode g).length+2)
      (fun history bits => history = [] ∧ bits = listCode reportCode values) := by
  let g := rawGraph index w r out ident
  let D := denominator g
  have gd : 0 < D := denominator_pos g
  have ge : ∀ {a b : V} (e : a ⟶ b), NumberBounds.OnGrid D (w e) :=
    fun e => denominator_grid g (cost_mem index w r out ident hout e)
  have gt : ∀ a, NumberBounds.OnGrid D (r a) :=
    fun a => denominator_grid g (terminal_mem index w r out ident a)
  have hs := rationalSolve_exact index w r out ident hout
  change rationalSolve (g.length-1,g) = (D, _) at hs
  obtain ⟨t,c,hRun,hBound,hHalt,hHistory,hOut⟩ := OracleSpec.BitCode.deploy_correct rationalReportsProgram o g
  refine ⟨t,c,hRun,hBound,hHalt,hHistory,hOut.trans ?_⟩
  apply congrArg (listCode reportCode)
  change reports (rationalSolve (g.length-1,g)) = _
  rw [hs]
  simp only [reports,serializeValues,List.map_map]
  apply List.map_congr_left
  intro j _
  exact report_serializes w r ident gd ge gt _



/-- The decoded machine values satisfy the residual inequalities. Every returned path is simple
and attains the greatest score over all finite walks. -/
theorem report_optimality [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]
    (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ j : V, a ⟶ j) ∈ out a)
    (hc : NonpositiveSimpleCircuits w) :
    let p := fun v => Layer.lookup index (plans index w r out (n-1)) v
    (∀ {a b : V} (e : a ⟶ b), w e ≤ (p a).total-(p b).total) ∧
      ∀ a, (p a).path.vertices.Nodup ∧ (p a).total = (p a).path.addWeight w + r (p a).finish ∧
      ∀ {b : V} (q : Path a b), q.addWeight w+r b ≤ (p a).total := by
  let p (v : V) := Layer.lookup index (plans index w r out (n-1)) v
  have hn : Fintype.card V = n := (Fintype.card_congr index).trans (Fintype.card_fin _)
  have hp (v : V) : (p v).total = potential w r v := by
    simpa only [potential, hn, p] using plans_total_eq_value index w r out hout (n-1) v
  refine ⟨fun {a b} e => ?_, fun a => ⟨plans_simple index w r out hout hc _ a, (p a).total_spec, ?_⟩⟩
  · change w e ≤ (p a).total-(p b).total
    rw [hp,hp]
    exact arc_le_potential_sub w r hc e
  · intro b q
    change q.addWeight w+r b ≤ (p a).total
    rw [hp]
    exact walk_score_le_potential w r hc q


end Input
end Table
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
