import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyTemplate
import OAI.Computability.NearSquareRoot.InterchangeROMStageMoves
import OAI.Computability.NearSquareRoot.InterchangeCompiledPivot

/-! # Native coordinate and word semantics of selected template chart slots -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.Template.Data
open InterchangeROMStage InterchangeSpectralRequest InterchangeSlots StageRoute RectangleAtlas Support
  IntegerMultiplication.Loom IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Port

variable {j threshold : ℕ} {x : Data}

theorem lookup_operand (h : Valid j threshold x) (v : (roleRealization h).NativeMove) :
    lookup x.chart ((roleRealization h).operand v) = (AddressROM.instructions (catalog h) v).map Opcode.encode :=
  (roleRealization h).lookup_operand _ _ (catalog_word h) v

theorem lookup_price (h : Valid j threshold x) (v : (roleRealization h).NativeMove) :
    Opcode.price (lookup x.chart ((roleRealization h).operand v)) =
      ((AddressROM.instructions (catalog h) v).map Lag.prices).sum := by
  rw [lookup_operand,Opcode.price_encode]

def nativeLayout (h : Valid j threshold x) [NeZero x.b] (P G S : Tape) (f : ℕ) :
    StageRoute.Layout x.rect (Fin x.m) (Keys P G S (Fin (x.a+x.m+x.a)) (Block x.b f)) :=
  extendLayout P G S (AddressROM.layout (catalog h) (radix_gt_one h) (catalog_valid h) f)

open private swapAt_twice chase_swapAt from OAI.Computability.NearSquareRoot.InterchangeCompiledPivot

/-- The verified atlas's native pullback exchanges the indicated coordinate
and preserves every spectator field. -/
theorem native_pull (h : Valid j threshold x) [NeZero x.b] (q : Fin x.m) (v : Fin x.labels)
    (P G S : Tape) (f : ℕ) (z : Keys P G S (Fin (x.a+x.m+x.a)) (Block x.b f)) :
    let D := nativeLayout h P G S f
    (D.S q v).symm (D.T q v z) = swapAt (mainRank x.a q) z := by
  let D := nativeLayout h P G S f
  let σ := (D.S q v).trans (D.T q v).symm
  have out (y : Keys P G S (Fin (x.a+x.m+x.a)) (Block x.b f)) : σ y = swapAt (mainRank x.a q) y := by
    have eq := congrArg (fun e : Equiv.Perm _ => e y)
      (AddressROM.native_diagonal (catalog h) (radix_gt_one h) (catalog_valid h) q v P G S f)
    apply eq.trans
    apply square.injective
    exact (fore (Equiv.refl _) [.pivot (mainRank x.a q) (mainRank x.a q)] (by simp [Lag.legal]) y).trans
      (congrArg (fun u => (u,watcher y)) (chase_swapAt (mainRank x.a q) y))
  change σ.symm z = _
  apply σ.injective
  rw [Equiv.apply_symm_apply,out,swapAt_twice]

end Interchange.Template.Data

end

end NearSquareRoot
end Computability
end OAI
