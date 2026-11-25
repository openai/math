import OAI.Hierarchy.DescentOperandStemSource
import OAI.Hierarchy.DescentStageSignedGL
import OAI.Hierarchy.DescentClosedRosterCoverage

namespace OAI
/-! # The true remixed low coordinate and signed old port in the stem candidate query -/
namespace Hierarchy.DescentOperandStemSlot
open DescentSixParty DescentColonies DescentGL DescentSIMDLookup DescentIssuedFallbackPanel
open DescentSharedCableNames DescentResetLocalRoster DescentPackedZip DescentIssuedGoodHeaders
open DescentPackedColony DescentPackedFallbackTree.Image
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {J V : Type} {m k c : ℕ} (digits : Block m≃J×Block k) (matrix : DescentGL.Layout m) (fits : c≤ m)

/-- The old port and all seven operand pages use the same physical donor
when the chosen ordered GL shuffles both banks. The low coordinate is the
public slice number of the remixed (high,low) scan. -/
theorem donor_low (v : V) (hi : Block c) (lo : Fin (2^(m-c))) :
    subcell digits matrix (donor digits matrix fits v hi lo)=lo := by
  change DescentPlainTerminal.low (rearrange matrix (digits.symm
    ((digits ((rearrange matrix).symm (join fits hi lo))).1,
     (digits ((rearrange matrix).symm (join fits hi lo))).2)))=_
  rw [Prod.mk.eta,Equiv.symm_apply_apply,Equiv.apply_symm_apply,DescentPlainTerminal.low_join]

open DescentOperandSignedSearch
def num (radix cap : ℕ) (externalSide : Bool) (lo ix : ℕ) :=
  if ix=0 then 0 else (if externalSide then radix*(2*cap) else 0)+lo*(2*cap)+ix

theorem ordinal (cap radix : ℕ) (s : Bool) (lo : Fin radix) (slot : Fin (2*cap)) :
    num radix cap s lo.val (slot.val+1)=
      (finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv (lo,slot))).val+1 := by
  have yes : finTwoEquiv.symm true = 1 :=rfl
  have no : finTwoEquiv.symm false = 0 :=rfl
  cases s <;> simp [yes,no,num,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

def width (radix cap : ℕ) := Packed.bits (2*(radix*(2*cap)))
def reshaped {oldBits : ℕ} (radix cap : ℕ) (s : Bool) (lo : Fin radix) (slot : Cell oldBits) : Cell (width radix cap) :=
  (num radix cap s lo.val slot.val:Cell (width radix cap))

theorem reshape_at {b : ℕ} (radix cap : ℕ) (s : Bool) (lo : Fin radix) (slot : Fin (2*cap)) (held : Cell b)
    (read : held.val=slot.val+1) :
    (reshaped radix cap s lo held).val=(finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv (lo,slot))).val+1 := by
  let actual : Fin (2*(radix*(2*cap))) :=finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv (lo,slot))
  have room : actual.val+1<2^(width radix cap) := (show actual.val+1≤2*(radix*(2*cap)) from actual.isLt).trans_lt
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide : 1<2) _))
  change num radix cap s lo.val held.val % _=_
  rw [read,ordinal]
  exact Nat.mod_eq_of_lt room

theorem hole {b : ℕ} (radix cap : ℕ) (s : Bool) (lo : Fin radix) : reshaped radix cap s lo (0 : Cell b)=0 := by
  simp [reshaped,num]

/-- Install-reuse of one small scalar law on the actual remixed prior slot.
The slice number is a public loop parameter shared by all packed high groups. -/
theorem issue {b entries groups M w : ℕ} (radix cap : ℕ) (s : Bool) (lo : Fin radix)
    (banks : DescentSIMDLookup.Banks) (out : ℕ) (x : Fin entries→Fin groups→Cell b)
    (pos : 0<M) (fit : DescentSIMDLookup.Fits banks b (width radix cap) M entries groups w out)
    (m : Memory w) (fixed : resident (reshaped (oldBits:=b) radix cap s lo) banks entries groups M m)
    (prior : Reads banks.source x M m) :
    let dst:=imageBank entries groups M out banks m
    (DescentSIMDLookup.program banks out entries groups M w).Exec m dst (4+44*(entries*chunks groups M)) ∧
    (∀v g,digit (width radix cap) (lane g pos).val
      (dst (out+(row entries groups M (position v g pos)).val)).val=(reshaped radix cap s lo (x v g)).val) ∧
    (∀a<out,dst a=m a) ∧ ∀a,out+entries*chunks groups M≤a→dst a=m a :=
  DescentPackedLocalLookup.compile banks out (reshaped radix cap s lo) x pos fit m fixed prior

end
end Hierarchy.DescentOperandStemSlot

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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



/-- A true remixed search of the old signed plane yields, on the receiver's
actual parent row, exactly its immutable short candidate number. -/
theorem stem_query {b : ℕ} (u : Host) (s : Bool) (j : (old).graph.Edge)
    (active : DescentResetLocalRoster.active (blocks B) u (stemParent B (s,j)))
    (value : Cell b)
    (measured : value.val=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).2.val+1) :
    let lo:=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).1
    (DescentOperandStemSlot.reshaped (2^(m-c)) (A).cap s lo value).val=
      (localRoster B u ⟨stemParent B (s,j),active⟩).val+1 := by
  intro lo
  rw [stem_number]
  exact DescentOperandStemSlot.reshape_at _ _ s lo _ value measured

theorem trunk_query (u : Host) (root : (Z).Fallback)
    (active : DescentResetLocalRoster.active (blocks B) u (trunkParent B root)) :
    1+2*(2^(m-c)*(2*(A).cap))=(localRoster B u ⟨trunkParent B root,active⟩).val+1 := by
  rw [trunk_number]
  exact Nat.add_comm ..

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
