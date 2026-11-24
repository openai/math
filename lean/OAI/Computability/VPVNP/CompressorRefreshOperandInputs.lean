import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress
import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentSite
import OAI.Computability.VPVNP.CompressorRecordRefreshReadback

/-!
# Operand addresses for a selected refresh site

The child and parent carry independent private argument buffers. Their argument banks read
the old and new incidence widths, respectively. Both banks name the same physical site
ordinal. The four external segment heads describe independently oriented half-wires.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.OperandInputs

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe NewSlots
open PairSimulation.NodeArguments RefreshMapOperands

/-- Address expressions for a refresh site's old child and promoted parent argument buffers,
external segment tables, demand row and selected term record. -/
structure Input where
  /-- Address plan for the child's private arguments at the old site, using the input state's
  incidence directory. -/
  child : ArgumentAddress.Input
  /-- Address plan for the promoted parent's private arguments, using the output state's
  incidence directory. -/
  parent : ArgumentAddress.Input
  /-- Expression for the number of residual lane positions, equal to two to the residual lane
  exponent. -/
  lanes : Expr
  /-- Head of the outgoing segment-offset array, supplied by word five of the segment bank. -/
  offOut : Expr
  /-- Head of the incoming segment-offset array, supplied by word six of the segment bank. -/
  offIn : Expr
  /-- Head of the outgoing segment-width array, supplied by word one of the segment bank. -/
  widthOut : Expr
  /-- Head of the incoming segment-width array, supplied by word seven of the segment bank. -/
  widthIn : Expr
  /-- Expression evaluating to the base address of the gathered demand records. -/
  demandBase : Expr
  /-- Expression evaluating to the base address of the selected refresh term records. -/
  termBase : Expr

variable {a b g dH w : ℕ} (I : Input) (pub : Fin 5 → W w) (state : W w) (m : Memory w)
  (X : State a (a+g)) (p : (X.Base × BitWord g) × Fin (2^a))
  (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^b)
  (internal : X.Base × BitWord g → Fin (2^a) × Fin dH → ℕ) (A : Arena) (child parent : ℕ)
  (old next : IncidenceDirectory w) (q : Fin 8 → W w) (demand term : W w)

local notation "Y" => newState X P hD hd internal
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)

/-- The child and promoted parent expressions represent their actual arguments and incidence
directories. The parent site ordinal, lane count and segment, demand and term heads
evaluate to the specified live words. -/
structure Describes : Prop where
  childRep : ArgumentAddress.Represents pub state m I.child X (oldSite X p) old A child
  parentRep : ArgumentAddress.Represents pub state m I.parent Y (promotedSites p) next A parent
  site : (I.parent.siteOrd.eval pub state m).val = (O p).val
  lanes : (I.lanes.eval pub state m).val = 2^g
  offOut : I.offOut.eval pub state m = q 5
  offIn : I.offIn.eval pub state m = q 6
  widthOut : I.widthOut.eval pub state m = q 1
  widthIn : I.widthIn.eval pub state m = q 7
  demandBase : I.demandBase.eval pub state m = demand
  termBase : I.termBase.eval pub state m = term

end CompressorRecords.PortRefresh.OperandInputs

end VPVNP
end Computability
end OAI
