import OAI.Hierarchy.DescentDatedSampledOperandValues
import OAI.Hierarchy.DescentDatedSampledMaterialValues
import OAI.Hierarchy.DescentDatedOperandPhysicalRead
import OAI.Hierarchy.DescentDatedTicketDigit

namespace OAI
/-! # The two actual signed parent digits at the operand reader's new packing -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentDatedOperandCoordinates.Ticket
open DescentPackedZip DescentHaloWalkRAM DescentSIMDLookup DescentRawCablePanel DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
set_option quotPrecheck false
set_option hygiene false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "g" => v.ticketReadGeometry
local notation "l" => v.resolver
local notation "seats" => breadth (fmt).degree*DepotRAM.Material.roles fmt
local notation "value" => (Fin (e).hosts→Fin (e).groups→Cell (e).fieldBits)
set_option hygiene true
variable (blocks : (l).blocks=(e).blocks) (bound : (l).hosts≤(e).hosts) (groups : (l).groups=(e).groups)

/-- The exact original data used by the installed matched-ticket return reads the
earlier first-grain serial and the receiver's actual peer at the same dated job. -/
theorem sampled_parent_numbers (R : Fin (e).oldHosts→Fin (fmt).degree→Option (Fin (e).oldHosts))
    (state : Fin (e).oldHosts→Fin (e).oldGroups→DepotRAM.Parts fmt) (bands : (e).oldGroups=(e).groups*(e).blocks)
    (serial peer : Fin (e).blocks→Fin seats→value)
    (orig : Fin (l).jobs→Fin 6→Values g v.operandShortBits) (prior : Fin (l).jobs→Fin 4→Values g ((l).size+2))
    (birth : Fin (l).jobs→Fin 3→Values g v.bornBook.bits)
    (j : Fin (l).jobs) (i : Fin seats) (h : Fin (l).hosts) (y : Fin (l).groups) :
    let data:=v.sampleHeads blocks bound groups orig prior birth (v.wideMaterialValues R state bands serial peer)
      (v.narrowValue R)
    let x:=v.receiverBlock blocks j
    ((v.originalValues data).raw j 6 i h y).val=(serial x i (h.castLE bound) (y.cast groups)).val ∧
      ((v.originalValues data).raw j 7 i h y).val=(peer x i (h.castLE bound) (y.cast groups)).val :=by
  intro data x
  exact ⟨v.original_raw_number data j 6 i h y,v.original_raw_number data j 7 i h y⟩

section
open DescentHaloPackedRebase
variable (R : Fin (e).oldHosts→Fin (fmt).degree→Option (Fin (e).oldHosts))
    (state : Fin (e).oldHosts→Fin (e).oldGroups→DepotRAM.Parts fmt) (bands : (e).oldGroups=(e).groups*(e).blocks)
    (serial peer : Fin (e).blocks→Fin seats→value)
    (orig : Fin (l).jobs→Fin 6→Values g v.operandShortBits) (prior : Fin (l).jobs→Fin 4→Values g ((l).size+2))
    (birth : Fin (l).jobs→Fin 3→Values g v.bornBook.bits)
set_option hygiene false
local notation "heads" => v.wideMaterialValues R state bands serial peer
local notation "record" => v.sampleHeads blocks bound groups orig prior birth heads (v.narrowValue R)
variable (j : Fin (l).jobs) (h : Fin (l).hosts) (y : Fin (l).groups) (recv donor : Fin (e).oldHosts)
local notation "h₀" => h.castLE bound
local notation "y₀" => y.cast groups
local notation "x₀" => v.receiverBlock blocks j
local notation "pack" => state donor ((finProdFinEquiv (y₀,x₀)).cast bands.symm)
set_option hygiene true
variable (atHost : DepotRAM.Material.Route.receiver (e).oldHosts v.materialPitch h₀=some recv)

include atHost

/-- All six material digits at the sampled physical job are the literal fields of
the selected old donor. The reverse path word is taken from the same roster. -/
theorem sampled_material_numbers (p : Fin (breadth (fmt).degree)) (z : DepotRAM.Material.Seat fmt)
    (selected : Gather.select (Gather.reaching R) recv p=some donor) (f : Fin 6) :
    let idx:=finProdFinEquiv (p,DepotRAM.Material.seatIndex fmt z)
    ((v.originalValues record).raw j (f.castLE (by decide : 6≤8)) idx h y).val=
      (DepotRAM.Material.rawObserved fmt v.materialFormat pack
        (digest (DepotRAM.Material.reverseEntries fmt R donor)) z f).val :=by
  intro idx
  refine (v.original_raw_number record j (f.castLE (by decide : 6≤8)) idx h y).trans ?_
  change ((if live : f.val<6 then v.rawMaterialValue R state bands x₀ ⟨f.val,live⟩ idx
    else if f.val=6 then serial x₀ idx else peer x₀ idx) h₀ y₀).val = _
  rw [dite_eq_left f.isLt]
  exact congrArg Fin.val (v.raw_value_at_donor R state bands p x₀ z f h₀ y₀ recv donor atHost selected)

/-- The five measured anchor fields use the original match table, including
the sibling table selected at mode two. -/
theorem sampled_anchor_number (i : Fin (breadth (fmt).degree*((fmt).blocks*((fmt).cap*3)))) (f : Fin 5)
    (selected : Gather.select (Gather.reaching R) recv (v.matchAnchorIndex i f).1=some donor) :
    ((v.originalValues record).anchor j f i h y).val=
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits (v.matchAnchorIndex i f).2.val
        (DepotRAM.combine fmt pack)).val :=by
  refine (v.original_anchor_number record j f i h y).trans ?_
  exact congrArg Fin.val (v.matched_field_at_donor R state bands (v.matchAnchorIndex i f).2
    (v.matchAnchorIndex i f).1 x₀ h₀ y₀ recv donor atHost selected)

/-- The four prior cable-header fields use the installed match table at the earlier donor. -/
theorem sampled_old_number (i : Fin (breadth (fmt).degree*((fmt).blocks*((fmt).degree*(fmt).cap)))) (f : Fin 4)
    (selected : Gather.select (Gather.reaching R) recv (v.matchOldIndex i f).1=some donor) :
    ((v.originalValues record).old j f i h y).val=
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits (v.matchOldIndex i f).2.val
        (DepotRAM.combine fmt pack)).val :=by
  refine (v.original_old_number record j f i h y).trans ?_
  exact congrArg Fin.val (v.matched_field_at_donor R state bands (v.matchOldIndex i f).2
    (v.matchOldIndex i f).1 x₀ h₀ y₀ recv donor atHost selected)
end

private theorem groups_read {w H c n a b : ℕ} {expr : Expr} {mem : Memory w}
    (eqn : a=b) {xs : Fin H→Fin b→Cell c} (held : Source expr xs n mem) :
    Source expr (fun h (y:Fin a)=>xs h (y.cast eqn)) n mem :=by
  subst a
  exact held

/-- Independently of the witness chosen for an OriginalReads receipt, the native
raw operand at field six or seven has the value of its actually posted earlier bank. -/
theorem returned_parent_numbers (floor : ℕ) (c : v.SignedChart) (entry : v.ArgumentEntry)
    («matching» : entry.Match v floor) (shape : v.VectorShape) (data : v.OriginalData)
    {w : ℕ} (mem : Memory w)
    (wide : ∀key,(v.wideHead floor c key).Fits w (v.operandHeaderEnd floor))
    (narrow : ∀key,(v.narrowHead floor key).Fits w (v.operandHeaderEnd floor))
    (room : v.headTransferEnd floor < 2^w) (oldPitch : 0<(e).lanes) (newPitch : 0<(l).lanes)
    (precision : (e).fieldBits*(l).lanes≤w)
    (recorded : v.OriginalReads floor entry «matching» shape blocks data ((v.headTransferPhase floor c w).image mem))
    (j : Fin (l).jobs) (i : Fin seats) (serial peer : value)
    (first : Source (v.parentSerial floor c (v.receiverBlock blocks j) i) serial (e).lanes mem)
    (second : Source (v.parentPeer floor c (v.receiverBlock blocks j) i) peer (e).lanes mem)
    (h : Fin (l).hosts) (y : Fin (l).groups) :
    ((v.originalValues data).raw j 6 i h y).val=(serial (h.castLE bound) (y.cast groups)).val ∧
      ((v.originalValues data).raw j 7 i h y).val=(peer (h.castLE bound) (y.cast groups)).val :=by
  let x:=v.receiverBlock blocks j
  let post:=(v.headTransferPhase floor c w).image mem
  have applyField (f : Fin 8) (xs : value) (fromSource : Source (v.signedRawHead floor c x f i) xs (e).lanes mem) :
      ((v.originalValues data).raw j f i h y).val=(xs (h.castLE bound) (y.cast groups)).val :=by
    let key : v.WideHead:=.inr (.inr (x,f,i))
    have same:=v.wide_word_source floor c mem wide narrow room key xs oldPitch fromSource bound
    have oldWord:=groups_read groups same
    let expr:=v.transferredRaw floor x f i
    have firstRead:=socket_digit expr post _ (recorded.raw j f i).read newPitch precision h y
    have secondRead:=socket_digit expr post _ oldWord newPitch precision h y
    exact (v.original_raw_number data j f i h y).trans (firstRead.symm.trans secondRead)
  exact ⟨applyField 6 serial first,applyField 7 peer second⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
