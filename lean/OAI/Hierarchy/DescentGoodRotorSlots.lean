import OAI.Hierarchy.DescentReachedRootRows
import OAI.Hierarchy.DescentObservedSocketCarrier
import OAI.Hierarchy.DescentObservedRotorFaces

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentRelativeContacts
open DescentPackedFallbackTree DescentFallbackItemSelect DescentStageEdgeReceipt
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))

local notation "native" => order.trans Fin.valEmbedding
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
variable (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht) (T : Z.Terminals)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)

variable (effective : ℕ) (extent : effective=m)
variable (zEq : zz=A.z) (wireEq : ww=A.wire) (countEq : ct=A.grainCount)
local notation "asOld" => Equiv.sigmaCongrRight (fun a=>finCongr (congrFun countEq a))
local notation "c" => T.commonDepth
local notation:max "oldPos" s:arg e:arg => localAddress A native S ready digits frm.basis («c»:=c) s (asOld e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((oldPos s e).1.cast (congrArg (fun l=>2^(l-c)) extent.symm)),(oldPos s e).2)

include zEq wireEq in
/-- Signed old-grain coordinates remain injective in the actual chosen good root
when the stored grain count and residual dimension use their reached equalities. -/
theorem observed_rotor_cells_injective (side : Bool) (root : Z.placement.Good) :
    Function.Injective (fun e : Cells Z.placement side root=>row side e.val) :=by
  subst zz
  subst ww
  subst ct
  subst effective
  exact (physicalRoster A S ready digits order Z T frm side root).index.injective

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentStageEdgeReceipt
open DescentFallbackItemSelect DescentNamedContact
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation "native" => input.order.trans Fin.valEmbedding
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item (R).contact (R).owner s (.inr t)
local notation:max "token" t:arg => ((Z).fallLabel T t,((T).code t).2.2)
local notation:max "num" t:arg => ((T).leaves.window (shortName c ((T).code t))).card
local notation:max "who" t:arg => B.frame.host.symm ((T).code t).1
local notation:max "hiAt" t:arg => (Z).rootBlock T (.inr t)
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "widthCast" => congrArg (fun l=>2^(l-c)) B.keyWidth
local notation:max "posOld" s:arg e:arg => localAddress A native S input.valid words B.frame.basis («c»:=c) s (beforeStem B e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((posOld s e).1.cast (widthCast).symm),(posOld s e).2)

/-- The ordered public tap reads the real signed row of each donor. -/
def publicRotorSlots (side : Bool) (root : (Z).placement.Good) :
    DescentChosenRouter.Cells (Z).placement side root↪Fin (2^r*(2*(A).cap)) where
  toFun e:=oldRotorCell B side (beforeStem B e.val)
  inj':=GroupStage.observed_rotor_cells_injective (A) S input.valid words input.order (Z) (T) B.frame
    (effective:=(Z).k) (extent:=B.keyWidth) (zEq:=input.grain.symm)
    (wireEq:=input.edges.symm) (countEq:=B.count_eq) side root

@[simp] theorem publicRotorSlots_apply (side : Bool) (root : (Z).placement.Good) (e : DescentChosenRouter.Cells (Z).placement side root) :
    publicRotorSlots B side root e=oldRotorCell B side (beforeStem B e.val):=rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
