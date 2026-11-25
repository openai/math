import OAI.Computability.MultitapeWeakETH.LocalResidue
import OAI.Computability.MultitapeWeakETH.PrivateEnumeration

/-! # The complete tape evaluation of a sparse formula with an explicit candidate pool -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP PairSimulation LocalHistory TerminalWords TerminalGatherGeometry
open TemplateArithmetic ReaderEnumeration
open scoped Classical
noncomputable section

/-- The parameters contain the encoded formula, common modulus width,
private search depth, terminal site ordinals and the binary candidate pool. -/
abbrev Sweep := (LeafSyntax.Query × (Tally × Tally)) × (List Tally × List Bits.Word)

namespace Sweep

abbrev formula (q : Sweep) := q.1.1
abbrev width (q : Sweep) := q.1.2.1
abbrev budget (q : Sweep) := q.1.2.2
abbrev sites (q : Sweep) := q.2.1
abbrev pool (q : Sweep) := q.2.2

variable {R : Type} [CommRing R] {m : ℕ} {basis : Module.Basis (Fin m) ℤ R} (ops : ResidueOps basis)
    (factor : LocalSumQuery SiteQuery → Rep) (shared : SharedQuery → Option SharedData)

def vertex (x : (Sweep × SharedData) × Tally) :=
  factor ((x.1.1.1.2,(x.1.1.formula,x.1.2),x.2),x.1.1.pool)

theorem vertex_poly (cost : Poly factor) : Poly (vertex factor) :=
  (show Poly (fun x : (Sweep × SharedData) × Tally => ((x.1.1.1.2,(x.1.1.1.1,x.1.2),x.2),x.1.1.2.2)) by fun_prop).compose cost

def wires (q : Sweep × SharedData) := prodReps ops (q.1.width,q.1.sites.map (fun i => vertex factor (q,i)))

theorem wires_poly (cost : Poly factor) : Poly (wires ops factor) := by
  have list := ((Poly.identity.pair (show Poly (fun q : Sweep × SharedData => q.1.2.1) by fun_prop))).compose
    (Poly.push default [] (vertex_poly factor cost))
  exact ((show Poly (fun q : Sweep × SharedData => q.1.1.2.1) by fun_prop).pair list).compose (prodReps_poly ops)

def term (q : (Sweep × Bits.Word) × Bits.Word) :=
  (shared ((q.1.1.formula.1,q.1.2),q.2)).elim (constant basis 0) fun data => wires ops factor (q.1.1,data)

theorem term_poly (cost : Poly factor) (run : Poly shared) : Poly (term ops factor shared) := by
  let X := (Sweep × Bits.Word) × Bits.Word
  have lookup := (show Poly (fun q : X => ((q.1.1.1.1.1,q.1.2),q.2)) by dsimp only [X]; fun_prop).compose run
  let ok := lookup.compose (NearSquareRoot.PhaseTable.easyOption false (fun _ => true) (Easy.const true)).poly
  let get := lookup.compose (NearSquareRoot.PhaseTable.easyOption (default : SharedData) id Easy.identity).poly
  let args := ((show Poly (fun q : X => q.1.1) by dsimp only [X]; fun_prop).pair get)
  convert Poly.choose ok (args.compose (wires_poly ops factor cost)) (Code.Poly.const (constant basis 0)) using 1
  funext q
  cases e : shared ((q.1.1.formula.1,q.1.2),q.2) <;> simp [term,e]

def inner (q : Sweep × Bits.Word) :=
  sumReps ops (q.1.width,q.1.pool.map (fun b => term ops factor shared (q,b)))

theorem inner_poly (cost : Poly factor) (run : Poly shared) : Poly (inner ops factor shared) := by
  have terms := (Poly.identity.pair (show Poly (fun q : Sweep × Bits.Word => q.1.2.2) by fun_prop)).compose
    (Poly.push default [] (term_poly ops factor shared cost run))
  exact ((show Poly (fun q : Sweep × Bits.Word => q.1.1.2.1) by fun_prop).pair terms).compose (sumReps_poly ops)

def total (q : Sweep) :=
  sumReps ops (q.width,q.pool.map (fun a => inner ops factor shared (q,a)))

theorem total_poly (cost : Poly factor) (run : Poly shared) : Poly (total ops factor shared) := by
  have terms := (Poly.identity.pair (show Poly (fun q : Sweep => q.2.2) by fun_prop)).compose
    (Poly.push default [] (inner_poly ops factor shared cost run))
  exact ((show Poly (fun q : Sweep => q.1.2.1) by fun_prop).pair terms).compose (sumReps_poly ops)

/-- The returned residue executes the two outer sums of the values obtained
from the shared directories. All searches reuse the same candidate pool. -/
theorem total_eq (q : Sweep) (w L hint : ℕ) (modSize : q.width=tally w)
    (pool : q.pool=candidates (tally L,tally hint)) (fit : 2^L ≤ 2*hint) :
    residue basis w (total ops factor shared q) =
      Ideal.Quotient.mk (modulus R w) (treeSum (fun a => treeSum (fun b =>
        (shared ((q.formula.1,a),b)).elim 0 (fun data => decodeCoordinates basis (wires ops factor (q,data)))) L []) L []) := by
  let φ := Ideal.Quotient.mk (modulus R w)
  let weight := fun data => decodeCoordinates basis (wires ops factor (q,data))
  let val (a b : Bits.Word) := (shared ((q.formula.1,a),b)).elim 0 weight
  have one (a b : Bits.Word) : residue basis w (term ops factor shared ((q,a),b)) = φ (val a b) := by
    cases e : shared ((q.formula.1,a),b) <;> simp [term,residue,val,weight,e,constant_eq,φ]
  have mapped (g : Bits.Word → R) : treeSum (fun b => φ (g b)) L [] = φ (treeSum g L []) := by
    simp only [treeSum_eq,map_sum]
  have row (a : Bits.Word) : residue basis w (inner ops factor shared (q,a)) = φ (treeSum (val a) L []) := by
    unfold inner
    rw [modSize,sumReps_eq,pool,List.map_map]
    simp only [Function.comp_def,one]
    rw [sum_candidates _ _ _ fit,mapped]
  unfold total
  rw [modSize,sumReps_eq,pool,List.map_map]
  simp only [Function.comp_def,row]
  rw [sum_candidates _ _ _ fit,mapped]

end Sweep
end
end OAI.Computability.MultitapeWeakETH.NativeGrid
