import OAI.Computability.MultitapeWeakETH.CoarseTrace
import OAI.Computability.MultitapeWeakETH.Reduction
import OAI.Computability.MultitapeWeakETH.MiddleDecision
import OAI.Computability.MultitapeWeakETH.FieldLower

/-! # Multitape integer multiplication under Weak ETH

The hypothesis `WeakETH` in `Price` rules out a deterministic power saving in
the exponent for 3-SAT measured by variable count. The algorithm in
`MiddleDecision` gives `PriceZero` under this hypothesis. The partial table
bound and the coarse trace of a tape computation then imply `MainStatement`
in `Machine`.

For each machine, a success probability of at least 2^(-n/100) on uniform
input pairs forces a deadline of Ω(n√log n). The randomized machine may
make up to n/100 errors in the low n product bits. A sound nondeterministic
machine must write those bits exactly whenever it accepts with an output.

The companion module `NearRoot` combines this bound with the uniform
multiplication algorithm to identify the infimum of the achievable exponents.
-/

namespace OAI.Computability.MultitapeWeakETH

/-- The tape lower bound follows from the characteristic-zero Price alternative. -/
theorem main_of_price (price : PriceZero) : MainStatement :=
  main_of_tables coarseTraceBound (partialTableBound_of_field (fieldTableBound_of_price price))

/-- For each fixed machine the randomized and sound nondeterministic lower
bounds are uniform in all sufficiently large input lengths and all deadlines. -/
theorem main_of_weakETH (weak : WeakETH) : MainStatement :=
  main_of_price (price_of_variable_weakETH weak)

end OAI.Computability.MultitapeWeakETH
