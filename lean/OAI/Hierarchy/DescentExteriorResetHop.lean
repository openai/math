import OAI.Hierarchy.DescentResetPinStep
import OAI.Hierarchy.DescentExteriorReplay
import OAI.Hierarchy.DescentInstalledPublicHeader
import OAI.Hierarchy.DescentDenseHostTape

namespace OAI
/-! # A genuine re-entry attachment read through the issued compacted-host directory -/

namespace Hierarchy.DescentSixParty.ClosedReset
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentRelativeContacts
open DescentCommonHost DescentDenseHostOrder PinCohorts
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
    {W : MarkedWorld F d P bits} {input : Reached W G q ε S k i z D w hist}
    {ctl : ResetRates G S k D n h C f g cut tail} (b : ClosedReset input ctl)
    (owns : ∀p,input.placement.hub (host input p)=true)

set_option quotPrecheck false

local notation "K" => S.groupWidth k tail i
local notation "palette" => DescentDenseHostOrder.roster b.reset.graph (b.reset.k-b.terminals.commonDepth) (GroupStage.depthBound D n f g)
local notation "vertex" => b.frame.host.symm.toEmbedding.trans input.vertex
local notation "rawPin" => (fun p=>(b.reset.reenter b.terminals).graph.attach p)
local notation "low" => fun p=>(address k ((b.pinStep owns).cut (active input ctl.base ctl.radix p)).2)
local notation "native" => fun p=>(input.vertex (host input p)).val
local notation "after" => fun p=>(b.next.vertex (host b.next p)).val

def localTrunk (x : Block k) :=
  let sh:=Node.trunk false ((),((k-g,group (k-g) x),none))
  if h:sh∈palette then (localRank b.reset.graph (b.reset.k-b.terminals.commonDepth)
    (GroupStage.depthBound D n f g) ⟨sh,h⟩).val else 0

theorem trunk_name (p : P) :
    b.reset.commonName b.terminals (rawPin p)=
      .trunk false (b.frame.host (host input p),((k-g,group (k-g) (low p)),none)) := by
  let x:=StarKeys.filled W.graph input.placement.pos input.placement.block
    (S.resetInputDigits ctl.base ctl.radix i) (W.graph.attach p)
  have residueEq : low p=residue k (rearrange b.frame.basis x) :=
    Fin.ext (split_index K k b.frame.basis x).2
  have bounded : K≤K+k-g:=by simpa only [b.commonDepth] using b.frame.enough
  have part : K+k-g-K=k-g:=by omega
  have reduction : group (K+k-g) (rearrange b.frame.basis x)%2^(k-g)=group (k-g) (low p) := by
    rw [residueEq]
    simpa only [show K+k-k=K by omega,part] using
      id_relative (Nat.le_add_left k K) (show K+k-k≤K+k-g by omega)
        (Nat.sub_le (K+k) g) (rearrange b.frame.basis x)
  have raw : b.reset.commonName b.terminals (rawPin p) = (host b.next p).val := by
    change _ = (b.next.placement.pos _).2.val
    rw [(b.raw_pin p).1]
    rfl
  rw [raw,b.public_trunk p]
  rw [b.frame.atHub _ (owns p),b.commonDepth]
  simp only [shortName,part]
  exact congrArg (fun digit => Node.trunk false (b.frame.host (host input p),((k-g,digit),none))) reduction

theorem sparse_trunk (p : P) :
    (b.reset.rawHostRank b.terminals vertex (b.reset.placed b.terminals (rawPin p))).val=
      native p*(palette).card+b.localTrunk (low p) := by
  rw [←b.reset.codeHost_at b.terminals vertex,trunk_name b owns p]
  simp [ResetInput.codeHost,shape,position,localTrunk,Nat.mul_comm,Nat.add_comm]
  split
  · next h => exact dite_eq_left h
  · next h => exact dite_eq_right h

theorem compacted_trunk (p : P) :
    (b.reset.denseHostRank b.terminals vertex (b.reset.placed b.terminals (rawPin p))).val=after p := by
  change _=(b.reset.denseHostRank b.terminals vertex (b.next.placement.pos _).2).val
  rw [(b.raw_pin p).1];rfl

/-- The observed dense directory is the native prefix image built from the genuine installed bitmap. -/
theorem reset_directory {bw flags ids : ℕ} (m : Memory bw)
    (sep : flags+Fintype.card input.V*(palette).card≤ ids)
    (room : ids+Fintype.card input.V*(palette).card+1<2^bw)
    (flagsRead : ∀j<Fintype.card input.V*(palette).card,m (flags+j)=
      (DescentEdgeTapePrefix.row (fun _ : ↥(b.reset.commonNames b.terminals)=>1)
        (fun u=>(b.reset.rawHostRank b.terminals vertex u).val) j : Word bw)) :
    let tape:=b.reset.hostTape b.terminals vertex
    let next:=ProtocolRAMEndpointPrefix.image ids (DescentEdgeTapePrefix.before tape.span tape.rank) m tape.slots
    (ProtocolRAMEndpointPrefix.exclusive bw flags ids tape.slots).Exec m next (10+(3+12*tape.slots)) ∧
      ∀p,next (ids+(native p*(palette).card+b.localTrunk (low p)))=(after p:Word bw) := by
  obtain ⟨ran,live⟩:=b.reset.hostTape_native b.terminals vertex m sep room flagsRead
  refine ⟨ran,fun p=>?_⟩
  rw [←sparse_trunk b owns p,live,compacted_trunk b p]

theorem hop_read {bw count : ℕ} (H : DescentExteriorReplay.Hop) (bank : Bank)
    (kind : H.compact=some bank) (m : Memory bw) (row : Fin count) (pin : P)
    (ancestor : H.source.read m (row.val:Word bw)=(native pin:Word bw))
    (stamp : H.frozenDigit.read m (row.val:Word bw)=((low pin).val:Word bw))
    (base : H.hostBase.read m (native pin:Word bw)=((native pin*(palette).card:ℕ):Word bw))
    (shapeWord : H.localShape.read m ((low pin).val:Word bw)=(b.localTrunk (low pin):Word bw))
    (published : ∀u,bank.read m ((b.reset.rawHostRank b.terminals vertex u).val:Word bw)=
      ((b.reset.denseHostRank b.terminals vertex u).val:Word bw)) :
    DescentExteriorReplay.result count H m (H.dest.base+row.val)=(after pin:Word bw) := by
  rw [DescentExteriorReplay.physical]
  apply DescentExteriorReplay.read_reset H bank kind m row _ _ _ ancestor stamp _ base shapeWord
  rw [←sparse_trunk b owns pin,published,compacted_trunk b pin]

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
