import OAI.ThreeFlat.Diagonal.ShrinkStageNav
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal

namespace OAI
/-! # Values of the concrete three-word descriptor and eight admitted supply words -/

namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalPinsExpr RAM.MotifRows ShrinkMotif MotifIntegerChoice RefreshDemandRows
open scoped Classical BigOperators
noncomputable section
variable {W : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ)
local notation "V" => Formula.natural W data mem vs

theorem choiceWords_value {last : ℕ} (current : Word W) (base : Fin (last+1) → Fin 2 → ℕ)
    (size : Fin (last+1) → ℕ) :
    let pos := V (rel current 2)
    let row := pos/3
    let b := fun e : Fin 2 => mem (V (ptr current 8) + row*2 + e.val)
    let j := tileNumber b base
    V (choiceWords current base size) = if pos%3=0 then score b base j
      else if pos%3=1 then j.val else size j := by
  let pos := rel current 2
  let b := fun e : Fin 2 => field (atRow (ptr current 8) (.op .div pos (.lit 3)) 2) e.val
  let j := tileNumber (fun e => V (b e)) base
  let z := chooseFields b base
  have ok := chooseFields_value W data mem vs b base
  have rep : V z.1=score (fun e => V (b e)) base j := congrArg Prod.fst ok
  have id : V z.2=j.val := congrArg Prod.snd ok
  change (if decide (V pos%3=0) then V z.1 else if decide (V pos%3=1) then V z.2
    else V (rowAt _ (fun i => .lit (size i)) z.2)) = _
  rw [rowAt_hit W data mem vs _ _ j id]
  simp only [rep,id,decide_eq_true_eq,Formula.natural]
  rfl

theorem widthWords_value {last : ℕ} (current : Word W) (K : ℕ) (size bits : Fin (last+1) → ℕ)
    (pool : ∀ i, Fin (size i) → Fin 8 → ℕ) (row : ℕ) (j : Fin (last+1)) (e : Fin 8)
    (loc : V (rel current 3)=8*row+e.val)
    (id : mem (V (ptr current 2)+row*3+1)=j.val) :
    V (widthWords current K size bits pool) = mem (V (ptr current 2)+row*3)*bits j +
      ∑ a : Fin (size j), mem (V (ptr current 1)+row*K+a.val)*pool j a e := by
  let pos := rel current 3
  let owner := Formula.op .div pos (.lit 8)
  let port := Formula.op .mod pos (.lit 8)
  let desc := atRow (ptr current 2) owner 3
  let counts := atRow (ptr current 1) owner K
  have div : V owner=row := by change V pos/8=row; have := e.isLt; dsimp [pos]; omega
  have mod : V port=e.val := by change V pos%8=e.val; have := e.isLt; dsimp [pos]; omega
  have code : V (field desc 1)=j.val := by simpa [field,desc,atRow,plus,Formula.natural,natOp,div] using id
  change V (rowAt _ (fun j => rowAt 8 (fun e => outputWidth (fun a => pool j a e) counts (field desc 0)
    (bits j)) port) (field desc 1)) = _
  rw [rowAt_hit W data mem vs _ _ j code, rowAt_hit W data mem vs _ _ e mod, outputWidth_value]
  simp [field,desc,counts,atRow,plus,Formula.natural,natOp,div]

end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
