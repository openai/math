import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Public dimensions and field ordinals of a retained reset strip -/
namespace Hierarchy.DescentResetRetainedSetup
open DescentSIMDLookup
noncomputable section
/-- All dimensions are public, including separately chosen widths for
the previous archive, the matrix ingress, the local decoder and its consumer. -/
structure Layout where
  bits : ℕ
  hosts : ℕ
  groups : ℕ
  blocks : ℕ
  previousNodes : ℕ
  previousArgs : ℕ
  nodes : ℕ
  args : ℕ
  previousLanes : ℕ
  gatherLanes : ℕ
  high : ℕ
  low : ℕ
  cut : ℕ
  decodedLanes : ℕ
  emitLanes : ℕ

namespace Layout
variable (v : Layout)
/-- Gate occupation, flattened arity, followed by the seven pointer fields per argument. -/
def fields := 2+7*v.previousArgs
def sources := v.fields*v.blocks
def channels := v.fields*v.previousNodes
def donors := 2^(v.high+v.low-v.cut)
def grouped := 2^v.cut
def matrixLanes := 2^v.low/v.donors
def wholeWord := v.bits*v.previousNodes
def stripWord := v.bits*v.donors
def siteWord := v.stripWord*v.channels
/-- Outputs for each paid node and argument: seven recovered predecessor fields
and the retained private/exterior contribution for each field. -/
def outputs := (2*7*v.args)*v.nodes+v.nodes
def rows := v.hosts*chunks v.grouped v.decodedLanes
def sourceID (f : Fin v.fields) (b : Fin v.blocks) : Fin v.sources :=finProdFinEquiv (f,b)
/-- The first channels give the real occupied-node flag and the arity of the
flattened recipe at the corresponding old node. -/
def occupiedField : Fin v.fields :=⟨0,by unfold fields;omega⟩
def arityField : Fin v.fields :=⟨1,by unfold fields;omega⟩
def operandField (f : Fin 7) (arg : Fin v.previousArgs) : Fin v.fields :=
  ⟨2+(finProdFinEquiv (f,arg)).val,by have h:=(finProdFinEquiv (f,arg)).isLt;unfold fields;omega⟩
end Layout
end
end Hierarchy.DescentResetRetainedSetup

end OAI
