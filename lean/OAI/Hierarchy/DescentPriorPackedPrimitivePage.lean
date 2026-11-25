import OAI.Hierarchy.DescentArchivePaddedNodes
import OAI.Hierarchy.DescentPreviousPrimitiveCensus

namespace OAI
/-! # The physical predecessor primitive roster at the padded reset entrance -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}

open DescentOrdinaryHostPad

variable (floor : ℕ) (L : DescentResetRetainedSetup.Layout)
local notation "raw" => ports.storage ports.venue.k L
local notation "prev" => ports.archive.prior raw
local notation "roles_" => fun x : Fin (2^ports.venue.k)=>ports.archive.roles.bank x.val
local notation "machine" => ports.fullPad ports.venue.k floor prev roles_ w
local notation "start" => (ports.resetPad ports.venue.k).endAddress floor


private theorem reads_reindex {w H H' D D' n n' M M' : ℕ} (page : Bank) (mem : Memory w)
    (hosts : H'=H) (groups : D'=D) (bits : n'=n) (bus : M'=M)
    (v : Fin H→Fin D→Cell n) (u : Fin H'→Fin D'→Cell n')
    (stored : Reads page v M mem) (values : ∀h g,(u h g).val=(v (h.cast hosts) (g.cast groups)).val) :
    Reads page u M' mem:=by
  subst_vars
  have same : u=v :=funext fun h=>funext fun g=>Fin.ext (values h g)
  exact same.symm ▸ stored

private theorem same_packed {a b N K : ℕ} (bits : a=b) (nodes : N=K)
    (x : Fin N→Cell a) (y : Fin K→Cell b) (same : ∀j,(x j).val=(y (j.cast nodes)).val) :
    (encode a N x).val=(encode b K y).val:=by
  subst b; subst K
  rw [show x=y from funext fun j=>Fin.ext (same j)]

variable (v : DescentResetRetainedSetup.Layout)
    (blocks : v.blocks=2^k) (groups : v.groups=S.groupCount age)
    (size : v.hosts=ports.venue.hosts) (nodes : v.previousNodes=ports.nodes)
    (width : v.bits=printedBits G s Z op) (pitch : v.previousLanes=ports.roleLanes)
local notation "token_" => fun y:NodeOrder.All B=>(token G s Z op (label y)).cast (congrArg (2^·) width.symm)
local notation "values" => Reached.NodeCells.previousTokens r B number v blocks groups token_
local notation "xx" x:arg => (Fin.cast (blocks.trans (congrArg (2^·) room.radix)) x)
local notation "post" => ports.afterPad ports.venue.k floor

include size nodes pitch in
/-- Reinterpret a physically padded predecessor role at any already-published bank.
An unrepresented host has no old node at any ordinal. -/
theorem padded_token_read (tokenWidth : ports.tokenBits=printedBits G s Z op)
    (x : Fin v.blocks) (page : Bank) (mem : Memory w)
    (previous : Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.tokenBits*ports.nodes))
    (labels : ∀h g,(previous h g).val=(encode (printedBits G s Z op) ports.nodes
      (fun j=>(slotAt ports r B number room (xx x) j h g).elim 0 (fun y=>token G s Z op (label y)))).val)
    (kept : Reads page (extend ports.venue.hosts previous) ports.roleLanes mem) :
    Reads page (values x) v.previousLanes mem:=by
  have wide : v.wholeWord=ports.tokenBits*ports.nodes :=
    congrArg₂ Nat.mul (width.trans tokenWidth.symm) nodes
  let gg:=groups.trans room.groups
  apply reads_reindex _ _ size gg wide pitch _ _ kept
  intro h' g'
  by_cases represented:h'.val<ports.operandHosts
  · rw [extend,dite_eq_left (show (h'.cast size).val<ports.operandHosts from represented)]
    apply Eq.trans _ (labels ⟨h'.val,represented⟩ (g'.cast gg)).symm
    apply same_packed width nodes
    intro j
    let at_ :=Reached.NodeCells.atPhysical r B number (x.cast blocks) j h' (g'.cast groups)
    have ex : (xx x).cast (congrArg (2^·) room.radix.symm)=x.cast blocks:=Fin.ext rfl
    have eg : (g'.cast gg).cast room.groups.symm=g'.cast groups:=Fin.ext rfl
    have same : slotAt ports r B number room (xx x) (j.cast nodes) ⟨h'.val,represented⟩ (g'.cast gg)=at_ :=by
      simp only [slotAt,ex,eg]
      rfl
    rw [same]
    change (at_.elim (0 : Cell v.bits) token_).val = _
    cases at_ <;> rfl
  · rw [extend,dite_eq_right (show ¬(h'.cast size).val<ports.operandHosts from represented)]
    have empty (j : Fin v.previousNodes) :
        Reached.NodeCells.atPhysical r B number (x.cast blocks) j h' (g'.cast groups)=none:=by
      cases hit:Reached.NodeCells.atPhysical r B number (x.cast blocks) j h' (g'.cast groups) with
      | none=>rfl
      | some u=>exact False.elim (represented (((Reached.NodeCells.atPhysical_some r B number
          (x.cast blocks) j h' (g'.cast groups) u.1 u.2).mp hit).1 ▸ room.hosts u.1))
    simp only [Reached.NodeCells.previousTokens,empty,Option.elim_none]
    change (finFunctionFinEquiv (fun _ : Fin v.previousNodes=>(0:Cell v.bits))).val=0
    simp

include size nodes pitch in
/-- This is the actual original token bank after host padding, including nullary and exterior
nodes. The result is expressed in precisely the value family consumed by the retained mover. -/
theorem ArchiveRead.emitted_prior_primitives (seen : ArchiveRead ports r B number room shape op label pointer flags m)
    (tokenWidth : ports.tokenBits=printedBits G s Z op) (sized : ports.RoleRows)
    (native : ports.archive.Fits raw floor) (nBlocks : 2^ports.venue.k≤ports.archive.roles.blocks)
    (early : ports.archive.roles.endAddress≤floor) (space : ports.priorStart ports.venue.k floor<2^w)
    (live : 0<ports.roleLanes) (x : Fin v.blocks) :
    Reads ((post).archive.roles.bank x.val) (values x) v.previousLanes ((machine).image m):=by
  classical
  obtain ⟨⟨words,stored,_,_⟩,⟨roles,codes,labels⟩⟩:=seen.pad_witness L tokenWidth sized
  have bounds:=ports.pad_order ports.venue.k floor
  have limit:=(bounds.1.trans bounds.2).trans_lt space
  have source : ∀j,(prev j).Fits w floor:=(raw).prior_registers ports.archive.seed ports.archive.nodeBase
    ports.archive.arguments floor w native.1 native.2 limit
  have rfits : ∀j : Fin (2^ports.venue.k),(ports.archive.roles.bank j.val).Fits w floor:=
    fun j=>ports.archive.roles.fits w floor j.val (j.isLt.trans_le nBlocks) early limit
  have posted:=ports.full_pad_reads ports.venue.k floor prev roles_ m source rfits space live words roles stored codes
  have kept:=posted.2.2 (xx x)
  exact padded_token_read (room:=room) v blocks groups size nodes width pitch tokenWidth x _ _
    (roles (xx x)) (labels (xx x)) kept

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
