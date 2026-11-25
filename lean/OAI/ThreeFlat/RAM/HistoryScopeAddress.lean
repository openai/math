import OAI.ThreeFlat.RAM.PhysicalPinsNat
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Resolving numerical motif incidence into the occupied tree's bit-source address -/

namespace ThreeFlat.RAM.HistoryScopeAddress

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

/-- Scratch word operands after the geometry-specific bit lookup. The first
four words are `[scope,index,half,offset]`, with absorbed bits encoded as
`[3,edge,offset,0]`. The old child table contains absolute chronological
node IDs. Each retained half-record header/row has two/four words. -/
structure Layout where
  childIDs : ℕ
  nodes : ℕ
  childStarts : ℕ
  newHalves : ℕ
  oldBits : ℕ
  publicPins : ℕ
  privateStarts : ℕ

def Layout.args (T : Layout) (scope index half offset : ℕ) : Fin 11 → ℕ :=
  ![scope,index,half,offset,T.childIDs,T.nodes,T.childStarts,T.newHalves,T.oldBits,T.publicPins,T.privateStarts]

private abbrev E := Formula 11
private abbrev v (i : Fin 11) : E := .reg i
private def field (a i : E) : E := .load (add a i)
private def halfOffset (header : E) : E := field (field header (L 1)) (add (mul (L 4) (v 2)) (L 3))

def formula : E :=
  let child := field (v 4) (v 1)
  let childHalves := field (v 5) (add (mul (L 8) child) (L 6))
  let addr (origin bit : E) := add (L 2) (add origin bit)
  let old := addr (field (v 6) (v 1)) (add (halfOffset childHalves) (v 3))
  let new := addr (v 8) (add (halfOffset (v 7)) (v 3))
  let intra := addr (v 9) (add (field (v 10) (v 1)) (v 2))
  eqz (v 0) (L 0) (L 0) (eqz (v 0) (L 1) old (eqz (v 0) (L 2) new intra))

def value (T : Layout) (mem : ℕ → ℕ) (scope index half offset : ℕ) : ℕ :=
  let halfBase (header : ℕ) := mem (mem (header+1)+(4*half+3))
  if scope=0 then 0 else if scope=1 then
    let child := mem (T.childIDs+index)
    2+(mem (T.childStarts+index)+(halfBase (mem (T.nodes+(8*child+6)))+offset))
  else if scope=2 then 2+(T.oldBits+(halfBase T.newHalves+offset))
  else 2+(T.publicPins+(mem (T.privateStarts+index)+half))

theorem natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (T : Layout) (scope index half offset : ℕ) :
    formula.natural W data mem (T.args scope index half offset)=value T mem scope index half offset := by
  simp [formula,value,Layout.args,halfOffset,field,Formula.natural,natOp,natTest]
  by_cases h0 : scope = 0 <;> by_cases h1 : scope = 1 <;> by_cases h2 : scope = 2 <;>
    simp [h0,h1,h2]

def program (W : ℕ) : Term W 1 11 := formula.compile (fun _ => 0)

theorem binds (W : ℕ) : (program W).binds≤100 := by rw [program,Formula.binds_compile]; decide

theorem eval (W : ℕ) (data : Fin 1 → ℕ) (mem : ℕ → ℕ) (T : Layout) (scope index half offset : ℕ)
    (room : formula.Fits W (fun _ => data 0) mem (T.args scope index half offset)) :
    (program W).eval (fun j => (data j : Word W)) (fun j => (mem j : Word W))
      (fun j => (T.args scope index half offset j : Word W)) = (value T mem scope index half offset : Word W) := by
  simp only [program,Formula.eval_compile,Function.comp_def]
  exact (Formula.value_eq_natural formula (fun _=>data 0) mem _ room).trans
    (congrArg (fun n : ℕ=>(n : Word W)) (natural W (fun _=>data 0) mem T scope index half offset))

end ThreeFlat.RAM.HistoryScopeAddress

end OAI
