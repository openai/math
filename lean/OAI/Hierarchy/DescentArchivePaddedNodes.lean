import OAI.Hierarchy.DescentArchivePadInputs
import OAI.Hierarchy.DescentFullPriorPad

namespace OAI
/-! The role and arity of every original node in the padded reset input, including
external hubs, missing actors and final partial words. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}

open DescentOrdinaryHostPad

/-- A padded receiver names an original archive slot only inside the stored host rectangle. -/
def paddedSlot (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist)
    (B : BitDescription W) (number : Local B) (room : RangeRoom ports r B)
    (x : Fin (2^ports.venue.k)) (j : Fin ports.nodes) (h : Fin ports.venue.hosts) (g : Fin ports.venue.groups) :
    Option (NodeOrder.All B) :=
  if seen : h.val<ports.operandHosts then slotAt ports r B number room x j ⟨h.val,seen⟩ g else none

private theorem zeros (a n : ℕ) : encode a n (fun _=>0)=0:=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
  simp

private theorem same_digit {a b n : ℕ} (bits : a=b) (left : Cell (a*n)) (right : Cell (b*n))
    (same : left.val=right.val) (j : Fin n) :
    ((encode a n).symm left j).val=((encode b n).symm right j).val:=by
  subst b
  rw [Fin.ext same]

local notation "C" => ports.presence ports.venue.k
local notation "slot" => slotAt ports r B number room
local notation "where_" => paddedSlot ports r B number room
local notation "arityOf" y => (occurrences (shape.sites (y:NodeOrder.All B).1) y.2).length

theorem padded_presence (roles : Fin (2^ports.venue.k)→Fin ports.operandHosts→Fin ports.venue.groups→
      Cell (ports.tokenBits*ports.nodes)) (tokenWidth : ports.tokenBits=printedBits G s Z op)
    (trueRoles : ∀x h g,(roles x h g).val=(encode (printedBits G s Z op) ports.nodes (fun n=>
      (slot x n h g).elim 0 (fun y=>token G s Z op (label y)))).val)
    (x : Fin (2^ports.venue.k)) (h : Fin ports.venue.hosts) (g : Fin ports.venue.groups) :
    (C).readings (extend ports.venue.hosts (roles x) h g)=
      encode ports.operandBits ports.nodes (fun j=>(where_ x j h g).elim 0 (fun _=>1)):=by
  apply (encode ports.operandBits ports.nodes).symm.injective
  rw [Equiv.symm_apply_apply]
  funext j
  erw [(C).at_node (extend ports.venue.hosts (roles x) h g) j]
  change (if ((encode ports.tokenBits ports.nodes).symm (extend ports.venue.hosts (roles x) h g) j).val=0 then 0 else 1) = _
  by_cases live:h.val<ports.operandHosts
  · let old : Fin ports.operandHosts:=⟨h.val,live⟩
    simp only [extend,paddedSlot,dite_eq_left live]
    have digit:=same_digit tokenWidth _ _ (trueRoles x old g) j
    rw [Equiv.symm_apply_apply] at digit
    erw [digit]
    cases found:slot x j old g with
    | none=>
      change slot x j ⟨h.val,live⟩ g=none at found
      simp
      rfl
    | some y=>
      change slot x j ⟨h.val,live⟩ g=some y at found
      simp [token_val]
      rfl
  · simp only [extend,paddedSlot,dite_eq_right live,Option.elim_none]
    have z:=(encode ports.tokenBits ports.nodes).symm_apply_eq.mpr (zeros ports.tokenBits ports.nodes).symm
    simp [z]
    rfl

theorem padded_arity (data : Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.operandBits*ports.nodes))
    (x : Fin (2^ports.venue.k)) (actual : ∀h g,data h g=encode ports.operandBits ports.nodes
      (fun j=>((slot x j h g).elim 0 (fun y=>arityOf y):Cell ports.operandBits)))
    (h : Fin ports.venue.hosts) (g : Fin ports.venue.groups) :
    extend ports.venue.hosts data h g=encode ports.operandBits ports.nodes
      (fun j=>((where_ x j h g).elim 0 (fun y=>arityOf y):Cell ports.operandBits)):=by
  by_cases live:h.val<ports.operandHosts
  · simpa only [extend,paddedSlot,dite_eq_left live] using actual ⟨h.val,live⟩ g
  · simp only [extend,paddedSlot,dite_eq_right live,Option.elim_none,zeros]

variable (floor : ℕ) (L : DescentResetRetainedSetup.Layout)
local notation "raw" => ports.storage ports.venue.k L
local notation "prev" => ports.archive.prior raw
local notation "roles_" => fun x : Fin (2^ports.venue.k)=>ports.archive.roles.bank x.val
local notation "machine" => ports.fullPad ports.venue.k floor prev roles_ w
local notation "start" => (ports.resetPad ports.venue.k).endAddress floor

/-- Running the actual reset prefix on a reached register yields both node pages
in the same memory, at the layout used by the following remixed intake. -/
theorem ArchiveRead.emitted_node_pages (seen : ArchiveRead ports r B number room shape op label pointer flags m)
    (tokenWidth : ports.tokenBits=printedBits G s Z op) (sized : ports.RoleRows)
    (native : ports.archive.Fits raw floor) (nBlocks : 2^ports.venue.k≤ports.archive.roles.blocks)
    (early : ports.archive.roles.endAddress≤floor) (space : ports.priorStart ports.venue.k floor<2^w)
    (live : 0<ports.roleLanes) :
    (machine).Runs m ∧ (∀i,i<floor ∨ ports.priorStart ports.venue.k floor≤ i→(machine).image m i=m i) ∧
      ∀x,Reads ((C).bank start 0 x) (fun h g=>encode ports.operandBits ports.nodes
        (fun j=>(where_ x j h g).elim 0 (fun _=>1))) ports.operandLanes ((machine).image m) ∧
        Reads ((C).bank start 1 x) (fun h g=>encode ports.operandBits ports.nodes
        (fun j=>((where_ x j h g).elim 0 (fun y=>arityOf y):Cell ports.operandBits))) ports.operandLanes ((machine).image m):=by
  obtain ⟨⟨words,stored,arities,seven⟩,⟨roles,codes,labels⟩⟩:=seen.pad_witness L tokenWidth sized
  have bounds:=ports.pad_order ports.venue.k floor
  have limit:=(bounds.1.trans bounds.2).trans_lt space
  have source : ∀j,(prev j).Fits w floor:=(raw).prior_registers ports.archive.seed ports.archive.nodeBase
    ports.archive.arguments floor w native.1 native.2 limit
  have rfits : ∀x : Fin (2^ports.venue.k),(ports.archive.roles.bank x.val).Fits w floor:=
    fun x=>ports.archive.roles.fits w floor x.val (x.isLt.trans_le nBlocks) early limit
  have runs:=ports.full_pad_any ports.venue.k floor prev roles_ m source rfits space
  have posted:=ports.full_pad_reads ports.venue.k floor prev roles_ m source rfits space live words roles stored codes
  refine ⟨runs.1,runs.2,?_⟩
  intro x
  have occupancy:=posted.1 0 x
  have count:=posted.1 1 x
  simp only at occupancy
  simp only [show (1 : Fin 2)≠0 by decide,ite_false] at count
  have flagEq : (fun h g=>(C).readings (extend ports.venue.hosts (roles x) h g))=
      fun h g=>encode ports.operandBits ports.nodes (fun j=>(where_ x j h g).elim 0 (fun _=>1)):=by
    funext h g
    exact padded_presence (label:=label) roles tokenWidth labels x h g
  have arityEq : extend ports.venue.hosts (words (ports.arityIndex ports.venue.k x))=
      fun h g=>encode ports.operandBits ports.nodes (fun j=>((where_ x j h g).elim 0 (fun y=>arityOf y):Cell ports.operandBits)):=by
    funext h g
    exact padded_arity (shape:=shape) _ x (fun h' g'=>congrFun (congrFun (arities x) h') g') h g
  rw [flagEq] at occupancy
  erw [arityEq] at count
  exact ⟨occupancy,count⟩


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
