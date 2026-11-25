import OAI.Computability.MultitapeWeakETH.SparseDecision
import OAI.Computability.MultitapeWeakETH.SparseNode

/-! # The deterministic variable-count consequence of characteristic-zero Port

This is the width-three, unit-weight count-positivity instance of Theorem 3.2
of the middle-bit paper. The counting tape and the sparsification budget are
fixed before the number of variables or the encoded input formula.
-/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication Code Bits Strip Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse
open SparseDFSRefinement SparsePreparation SparseIteration VariableSetup Filter
open scoped Classical
noncomputable section

/-- Port in characteristic zero supplies one deterministic machine deciding
nonemptiness on every width-three CNF within the variable-count power saving. -/
theorem middle_count_bridge : MiddleCountBridge := by
  intro port
  obtain ⟨d,hd,leaf,pl,good⟩ := NativeGrid.sparse_count_program port
  obtain ⟨split,ps,branch⟩ := split_program
  exact variable_count_decision hd leaf pl good split ps (fun w two F valid => branch F w valid two)

/-- The cited characteristic-zero Price alternative under exactly the
variable-count deterministic Weak ETH. -/
theorem price_of_variable_weakETH (weak : WeakETH) : PriceZero :=
  price_of_weakETH middle_count_bridge weak

end
end OAI.Computability.MultitapeWeakETH
