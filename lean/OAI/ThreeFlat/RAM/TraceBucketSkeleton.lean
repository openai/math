import OAI.ThreeFlat.RAM.ExpressionShapeOps
import OAI.ThreeFlat.RAM.TraceBucketAtom

namespace OAI
/-! # All ages of the initial atom share one literal-free instruction stream -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open DescriptorExpr.LiteralBank
open scoped Fin.CommRing
variable {W W' n : ℕ}
set_option maxHeartbeats 2500000

open private lit reg plus times sub quot modulo from OAI.ThreeFlat.RAM.TraceBucketAtom

private theorem shape_cons {k m : ℕ} (x : Term W k n) (xs : Fin m→Term W k n) (i : Fin (m+1)) :
    shape (Matrix.vecCons x xs i)=Matrix.vecCons (shape x) (fun j=>shape (xs j)) i :=
  Fin.cases rfl (fun _=>rfl) i

private theorem shape_nil {k : ℕ} (i : Fin 0) :
    shape (Matrix.vecEmpty i : Term W k n)=(Matrix.vecEmpty i : Term 0 k n) := Fin.elim0 i

/-- Normalize each finite argument vector once, preserving literal bank
operations as syntax so the kernel need not unfold the owner program. -/
private theorem normalize_direct (s : Layout) (op : TraceOwnerFormula.Output) (x y : Term W 1 n) :
    shape (TraceOwnerFormula.direct op s.shape 1 x y)=
      ((TraceOwnerFormula.formula op).compile (fun _=>0)).instantiate
        (![shape x,shape y,Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,
          Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,
          Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0,Term.literal 0]) := by
  simp only [TraceOwnerFormula.direct,TraceOwnerFormula.term,shape_instantiate,compile_shape,
    TraceOwnerFormula.args,shape_cons,shape_nil,shape_literal]

theorem origArgs_shape (s s' : Layout) (i : Fin 13) :
    shape (origArgs (W:=W) s i)=shape (origArgs (W:=W') s' i) := by
  simp only [origArgs,shape_cons,shape_nil,ext,pinStart,laneBase,raw,lit,reg,plus,times,sub,quot,modulo,
    shape_binary,shape_select,shape_load,shape_literal,shape_result,normalize_direct]

theorem cmpArgs_shape (s s' : Layout) (i : Fin 15) :
    shape (cmpArgs (W:=W) s i)=shape (cmpArgs (W:=W') s' i) := by
  simp only [cmpArgs,shape_cons,shape_nil,ext,pinStart,laneBase,raw,lit,reg,plus,times,sub,quot,modulo,
    shape_binary,shape_select,shape_load,shape_literal,shape_result,normalize_direct]

theorem holeArgs_shape (s s' : Layout) (i : Fin 7) :
    shape (holeArgs (W:=W) s i)=shape (holeArgs (W:=W') s' i) := by
  simp only [holeArgs,shape_cons,shape_nil,ext,pinStart,laneBase,lit,reg,plus,times,sub,quot,modulo,
    shape_binary,shape_select,shape_literal,shape_result,TraceOwnerFormula.validSlot,
    TraceOwnerFormula.verify,TraceOwnerFormula.verifyArgs,shape_instantiate,normalize_direct]

theorem relayArgs_shape (s s' : Layout) (i : Fin 10) :
    shape (relayArgs (W:=W) s i)=shape (relayArgs (W:=W') s' i) := by
  simp only [relayArgs,shape_cons,shape_nil,ext,pinStart,laneBase,lit,reg,plus,times,sub,shape_binary,shape_select,shape_literal,shape_result]

/-- All word widths, physical addresses, and trace capacities can be
changed without changing a single operation, register, or data flow edge. -/
theorem program_shape (s s' : Layout) :
    shape (program W s)=shape (program W' s') := by
  simp only [program,shape_select,shape_result,shape_literal,shape_instantiate,Diagonal.TraceBucketRelay.program,compile_shape,
    origArgs_shape (W:=W) (W':=W') s s',cmpArgs_shape (W:=W) (W':=W') s s',
    holeArgs_shape (W:=W) (W':=W') s s',relayArgs_shape (W:=W) (W':=W') s s']

end ThreeFlat.RAM.TraceBucketAtom

end OAI
