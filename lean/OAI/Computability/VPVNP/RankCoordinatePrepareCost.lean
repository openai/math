import OAI.Computability.VPVNP.RankCoordinatePreparePorts

/-! # Clock and peak height of the live two-root preparation -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Prepare

/-- Total instruction allowance for root loading, dynamic index selection, label preparation,
and argument installation. -/
def time (P : Type) [Fintype P] (b : Bool) (M B label w : ℕ) := RootInit.loadClock P M + (B+Dynamic.overhead w) +
  labelTime b label w + ArgumentStage.clock w

/-- Peak stack-height allowance through root loading, index selection, and unary label
conversion. -/
def baseCap (P : Type) [Fintype P] (M A S label w : ℕ) := max (A+RootInit.loadClock P M)
  (max (S+Dynamic.overhead w) (max label w + LabelWord.clock label w))

/-- Peak allowance for the complete preparation, including the final argument-copy phase. -/
def peak (P : Type) [Fintype P] (M A S label w : ℕ) := baseCap P M A S label w + ArgumentStage.clock w

end RankQuery.Stack.Coordinate.Prepare

end VPVNP
end Computability
end OAI
