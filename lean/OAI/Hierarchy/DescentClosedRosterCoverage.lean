import OAI.Hierarchy.DescentClosedStemRoster
import OAI.Hierarchy.DescentResetContactLocalRoster

namespace OAI
/-! # Bounded original, public and private reset parents at each reached receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


def contactCount := 2*(rootSlots ((Z).k-c) (2^(Z).n)*(2^(Z).n+2^height))
def privateCount := 2*(rootSlots ((Z).k-c) (2^(Z).n)*capacity)
def stemsCount := 2*(2^(m-c)*(2*(A).cap))

def totalLocal := stemsCount B+(1+(contactCount B+privateCount B))

def contactDigit (u : Host) :
    Part (blocks B) u (contactParent B) ↪Fin (contactCount B) :=
  let take : Part (blocks B) u (contactParent B) ↪ ContactAt B u :=
    ⟨fun x=>⟨x.val,x.property.2⟩,fun _ _ eqn=>Subtype.ext (Subtype.mk.inj eqn)⟩
  let port:=DescentResetCableSlots.sum (Function.Embedding.refl (Fin (2^(Z).n)))
    (Function.Embedding.refl (Fin (2^height)))
  let pack:=DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding
    (DescentResetCableSlots.prod (rootId ((Z).k-c) (2^(Z).n)) port)
  take.trans ((contact_local_chart B u).trans pack)

/-- A positive parent has exactly one short candidate, even if it is a loop.
The same enumeration is used when calculating the earlier signed-frame prefix. -/
def localRoster (u : Host) : Local (blocks B) u↪Fin (totalLocal B) :=
  rawRoster B u (contactDigit B u)

def localOrigin (u : Host) (j : Fin (totalLocal B)) : Option (Local (blocks B) u) :=
  origin (blocks B) u (localRoster B u) j

theorem local_read (u : Host) (j : Fin (totalLocal B)) (e : Local (blocks B) u) :
    localOrigin B u j=some e ↔ localRoster B u e=j :=
  origin_iff (blocks B) u _ _ _

theorem local_covers (u : Host) (e : Local (blocks B) u) : ∃!j,localOrigin B u j=some e :=
  covers (blocks B) u _ _

theorem local_sum (u : Host) (f : Local (blocks B) u→ℕ) :
    (∑j,(localOrigin B u j).elim 0 f)=∑e,f e :=
  origin_sum (blocks B) u _ _


private theorem one_slot (i : Fin 1) : i.val=0 := by omega

theorem trunk_number (u : Host) (t : (Z).Fallback) (active : DescentResetLocalRoster.active (blocks B) u (trunkParent B t)) :
    (localRoster B u ⟨trunkParent B t,active⟩).val=stemsCount B := by
  have value:=DescentResetLocalRoster.trunk_number (blocks B) u (motherNames B)
    (stems_chart B u) (trunk_chart B u) (contactDigit B u) (hidden_chart B u) t active
  exact value.trans ((congrArg (fun j : ℕ => stemsCount B + j)
    (one_slot (trunk_chart B u ⟨t,active⟩))).trans (Nat.add_zero _))

theorem stem_number (u : Host) (s : Bool) (j : (old).graph.Edge)
    (active : DescentResetLocalRoster.active (blocks B) u (stemParent B (s,j))) :
    (localRoster B u ⟨stemParent B (s,j),active⟩).val=
      (finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv
        (localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)))).val :=
  DescentResetLocalRoster.stem_number (blocks B) u (motherNames B)
    (stems_chart B u) (trunk_chart B u) (contactDigit B u) (hidden_chart B u) (s,j) active

theorem contact_number (u : Host) (j : (placement).Contact)
    (live : DescentResetLocalRoster.active (blocks B) u (contactParent B j)) :
    (localRoster B u ⟨contactParent B j,live⟩).val=
      stemsCount B+1+(contactDigit B u ⟨j,live⟩).val :=
  DescentResetLocalRoster.contact_number (blocks B) u (motherNames B)
    (stems_chart B u) (trunk_chart B u) (contactDigit B u) (hidden_chart B u) j live

theorem private_number (u : Host) (x : PrivateOccurrence B)
    (live : DescentResetLocalRoster.active (blocks B) u (privateWire B x)) :
    (localRoster B u ⟨privateWire B x,live⟩).val=
      stemsCount B+1+contactCount B+(localPrivateId _ _ capacity (privateTicket B x)).val :=
  DescentResetLocalRoster.device_number (blocks B) u (motherNames B)
    (stems_chart B u) (trunk_chart B u) (contactDigit B u) (hidden_chart B u) x live

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
