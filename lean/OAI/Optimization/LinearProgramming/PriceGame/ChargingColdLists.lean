import OAI.Optimization.LinearProgramming.PriceGame.ControlWire
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.PriceGame.Skeletons

/-! # Actual stack programs for cold-start expert records

The tuple arity is a compile-time constant. All vertex, depth and pivot lists,
including their framing and copies, are constructed by finite bit-stack programs.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Cold

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost

/-- A depth together with the ordered addresses of its vertices. -/
abbrev Row := ℕ × List ℕ
abbrev rowCode := prodCode Nat.bits (listCode Nat.bits)
abbrev emptyRow : Row := (0,[])
abbrev ChoicePivot := Option (ℕ × ℕ)

/-- Flat-map a framed list using a common context, charging the output concatenation. -/
noncomputable def flatContextP {A B C : Type} {ea : A → List Bool} {eb : B → List Bool}
    {ec : C → List Bool} (da : A) (db : B) {f : A × C → List B}
    (p : Procedure (prodCode ea ec) (listCode eb) f) :
    Procedure (prodCode (listCode ea) ec) (listCode eb) (fun z => z.1.flatMap fun a => f (a,z.2)) :=
  ((flattenP eb db).comp (mapContextP da [] p)).congrFun fun _ => rfl

/-- Ordered products with repetitions, putting the first coordinate in the outermost loop. -/
def tupleWords {A : Type} : ℕ → List A → List (List A)
  | 0, _ => [[]]
  | d+1, xs => cross xs (tupleWords d xs)

noncomputable def tupleWordsP {A : Type} (ea : A → List Bool) (da : A) :
    (d : ℕ) → Procedure (listCode ea) (listCode (listCode ea)) (tupleWords d)
  | 0 => constant _ _ [[]]
  | d+1 => (crossP ea da).comp ((identity (listCode ea)).pair (tupleWordsP ea da d))

theorem tupleWords_eq_map {A B : Type} (f : A → B) (xs : List A) (d : ℕ) :
    (Skeleton.tuples xs d).map (fun t => List.ofFn (fun j => f (t j))) = tupleWords d (xs.map f) := by
  induction d with
  | zero => simp [Skeleton.tuples,tupleWords]
  | succ d ih =>
    rw [Skeleton.tuples,tupleWords,cross, List.map_flatMap,List.flatMap_map]
    apply List.flatMap_congr
    intro a _
    rw [← ih,List.map_map,List.map_map]
    apply List.map_congr_left
    intro t _
    simp [List.ofFn_succ]

/-- All valid descriptors at a given destination, in the paper's enumeration order. -/
def pivotWords (rows : List Row) (k : ℕ) : List ChoicePivot :=
  none :: rows.flatMap (fun r => if r.1 < k then r.2.map (fun i => some (r.1,i)) else [])

noncomputable def pivotWordsP : Procedure (prodCode (listCode rowCode) Nat.bits)
    (listCode Wire.pivotCode) (fun z => pivotWords z.1 z.2) := by
  let localCode := prodCode rowCode Nat.bits
  let row := first rowCode Nat.bits
  let l := (first Nat.bits (listCode Nat.bits)).comp row
  let k := second rowCode Nat.bits
  let verts := (second Nat.bits (listCode Nat.bits)).comp row
  let pairPivot := (Learning.BitMachine.someP (prodCode Nat.bits Nat.bits)).comp (swap Nat.bits Nat.bits)
  let yes := (mapContextP 0 (none : ChoicePivot) pairPivot).comp (verts.pair l)
  let each := conditional (binaryLt.comp (l.pair k)) yes (constant localCode (listCode Wire.pivotCode) [])
  let all := flatContextP emptyRow (none : ChoicePivot) each
  let result := (listCons Wire.pivotCode).comp ((constant _ Wire.pivotCode none).pair all)
  apply result.congrFun
  intro z
  simp [pivotWords]

/-- Skeletons have empty raw data at cold start; the historical learner later fills it. -/
def packShape {N : ℕ} (s : Skeleton N) : PackedExpert :=
  { level := s.level, positive := s.positive,
    tuple := List.ofFn (fun j => (States.Mass.vertexEquivFin N s.level (s.tuple j)).val),
    pivot := s.pivot.map (fun p => (p.1.val, (States.Mass.vertexEquivFin N p.1 p.2).val)), raw := [] }

/-- The general row combinator accepts only an ordinary list of addresses and their
ancestor table. Its runtime is polynomial even for an arbitrary, inconsistent table. -/
def rowExperts (rows : List Row) (r : Row) : List PackedExpert :=
  [false,true].flatMap fun h => (tupleWords 64 r.2).flatMap fun t =>
    (pivotWords rows r.1).map fun p => ⟨r.1,h,t,p,[]⟩

private abbrev Frame := ℕ × Bool × List ℕ
private abbrev frameCode := prodCode Nat.bits (prodCode boolCode (listCode Nat.bits))

private noncomputable def entryP : Procedure (prodCode Wire.pivotCode frameCode) Wire.packedExpertCode
    (fun z : ChoicePivot × Frame => ⟨z.2.1,z.2.2.1,z.2.2.2,z.1,[]⟩) := by
  let ep := prodCode Wire.pivotCode frameCode
  let p := first Wire.pivotCode frameCode
  let fr := second Wire.pivotCode frameCode
  let l := (first Nat.bits (prodCode boolCode (listCode Nat.bits))).comp fr
  let rest := (second Nat.bits (prodCode boolCode (listCode Nat.bits))).comp fr
  let h := (first boolCode (listCode Nat.bits)).comp rest
  let t := (second boolCode (listCode Nat.bits)).comp rest
  let raw := constant ep (listCode ratCode) ([] : List ℚ)
  exact (l.pair (h.pair (t.pair (p.pair raw)))).result fun _ => rfl

private abbrev signDataCode := prodCode (prodCode Nat.bits boolCode) (listCode Wire.pivotCode)

private noncomputable def tupleEntriesP :
    Procedure (prodCode (listCode Nat.bits) signDataCode) (listCode Wire.packedExpertCode)
      (fun z : List ℕ × ((ℕ × Bool) × List ChoicePivot) =>
        z.2.2.map fun p => ⟨z.2.1.1,z.2.1.2,z.1,p,[]⟩) := by
  let tuple := first (listCode Nat.bits) signDataCode
  let d := second (listCode Nat.bits) signDataCode
  let lh := (first (prodCode Nat.bits boolCode) (listCode Wire.pivotCode)).comp d
  let pivots := (second (prodCode Nat.bits boolCode) (listCode Wire.pivotCode)).comp d
  let fr := ((first Nat.bits boolCode).comp lh).pair (((second Nat.bits boolCode).comp lh).pair tuple)
  exact (mapContextP none (default : PackedExpert) entryP).comp (pivots.pair fr)

noncomputable def rowExpertsP : Procedure (prodCode rowCode (listCode rowCode))
    (listCode Wire.packedExpertCode) (fun z => rowExperts z.2 z.1) := by
  let arg := prodCode rowCode (listCode rowCode)
  let r := first rowCode (listCode rowCode)
  let rows := second rowCode (listCode rowCode)
  let k := (first Nat.bits (listCode Nat.bits)).comp r
  let ts := (tupleWordsP Nat.bits 0 64).comp ((second Nat.bits (listCode Nat.bits)).comp r)
  let ps := pivotWordsP.comp (rows.pair k)
  let atSign := fun sign => (flatContextP [] (default : PackedExpert) tupleEntriesP).comp
    (ts.pair ((k.pair (constant arg boolCode sign)).pair ps))
  let result := (listAppend Wire.packedExpertCode default).comp ((atSign false).pair (atSign true))
  apply result.congrFun
  intro z
  simp [rowExperts]

/-- Run the row generator in order, preserving the common ancestor table. -/
noncomputable def allRowsP : Procedure (listCode rowCode) (listCode Wire.packedExpertCode)
    (fun rows => rows.flatMap (rowExperts rows)) :=
  (flatContextP emptyRow (default : PackedExpert) rowExpertsP).comp
    ((identity (listCode rowCode)).pair (identity (listCode rowCode)))

end Cold
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
