import OAI.Hierarchy.DescentBundleScalar
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! Primitive fields read at one inner node of a packed terminal word. -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentBundleHistory DescentSIMDLookup
noncomputable section
/-- The same local numberer is applied inside every node lane at every home.
The sole two scalar inputs are the previously published primitive token and
the previously published flattened operand count. -/
structure Raw (M:ℕ) where
  token : ℕ
  live : ℕ
  header : Fin M→SliceCode

variable {M N groups d : ℕ}
abbrev Columns (M:ℕ) := 2+3*M
def leading (j:Fin 2) : Fin (Columns M) := finSumFinEquiv (.inl j)
def triple (f:Fin 3) (j:Fin M) : Fin (Columns M) := finSumFinEquiv (.inr (finProdFinEquiv (f,j)))
structure RawWidths where
  role : ℕ
  count : ℕ
  tripleWidth : Fin 3→ℕ

def laneField (bits:ℕ) (g:Fin groups) (u:Fin N) (value:Cell d) : ℕ :=
  digit bits u.val (digit (bits*N) g.val value.val)

def extract (cfg:RawWidths) (input:Fin (Columns M)→Cell d) (g:Fin groups) (u:Fin N) : Raw M where
  token:=laneField cfg.role g u (input (leading 0))
  live:=laneField cfg.count g u (input (leading 1))
  header j:=⟨laneField (cfg.tripleWidth 0) g u (input (triple 0 j)),
    laneField (cfg.tripleWidth 1) g u (input (triple 1 j)),
    laneField (cfg.tripleWidth 2) g u (input (triple 2 j))⟩
end
end Hierarchy.DescentTerminalSliceRuns

namespace Hierarchy.DescentTerminalSliceShelf
def physicalWidth (groups nodes token record:ℕ) := groups*(nodes*max token record)
end Hierarchy.DescentTerminalSliceShelf

end OAI
