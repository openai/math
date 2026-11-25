import OAI.Hierarchy.DescentExteriorReplay
import OAI.Hierarchy.DescentOrdinaryPinStep

namespace OAI
/-! # A remixed exterior digit selects the actual numbered child of an ordinary subround -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentHostDirectory DescentHostDegree
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
  {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
  (ticket : OrdinaryLink source he T p n target) (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
  (owns : ∀pin,source.placement.hub (host source pin)=true)

local notation "gain" => DescentHostDegree.gainExponent 20 source.placement.degree
local notation "cols" => 2^DescentHostDegree.packExponent 20 source.placement.degree+2
local notation "rotation" => multiplier source.placement.fieldBits (BitDescription.scannedRows he source.placement.stage).μ
local notation "low" => fun pin=>(address k ((ticket.pinStep base radix owns).cut (active source base radix pin)).2)
local notation "old" => fun pin=>(source.vertex (host source pin)).val
local notation "next" => fun pin=>(target.vertex (host target pin)).val

omit [Fintype P] in
theorem OrdinaryLink.frozen_block (pin : P) :
    low pin=rearrange rotation (source.placement.block (W.graph.attach pin)) := by
  let bits := ((splitRows (S.groupWidth k tail i) k) (active source base radix pin)).2
  have block : address k bits = source.placement.block (W.graph.attach pin) :=
    (active_parts source base radix pin).2
  change address k (rotation bits) = _
  calc
    address k (rotation bits) = rearrange rotation (address k bits) := by simp [rearrange]
    _ = _ := congrArg (rearrange rotation) block

omit [Fintype P] in
theorem OrdinaryLink.exterior_ordinal (pin : P) :
    next pin = old pin*((2^(k+1)-1)*cols)+
      nodeNumber (k-gain) (group (k-gain) (low pin))*cols := by
  obtain ⟨age,power,chart,rows,index,_⟩:=ticket.hostOrdinal
  have named :=(rows pin (owns pin)).2
  have eqn:=index (host target pin)
  change chart (host target pin)=((host source pin),(k-gain,
    group (k-gain) (rearrange rotation (source.placement.block (W.graph.attach pin)))),0) at named
  rw [ticket.frozen_block base radix owns pin]
  simpa only [named,add_zero,Nat.add_mul,Nat.mul_assoc] using eqn

omit [Fintype P] in
/-- One access of the universal replay chart, on a truthful incoming common host.
Only public multiplication bases and the single short frozen digit are fetched. -/
theorem OrdinaryLink.hop_read {w count:ℕ} (H : DescentExteriorReplay.Hop) (direct : H.compact=none)
    (m : Memory w) (row : Fin count) (pin : P)
    (ancestor:H.source.read m (row.val:Computability.VPVNP.BurstRAM.Word w)=(old pin:Computability.VPVNP.BurstRAM.Word w))
    (stamp:H.frozenDigit.read m (row.val:Computability.VPVNP.BurstRAM.Word w)=((low pin).val:Computability.VPVNP.BurstRAM.Word w))
    (table:H.hostBase.read m (old pin:Computability.VPVNP.BurstRAM.Word w)=((old pin*((2^(k+1)-1)*cols):ℕ):Computability.VPVNP.BurstRAM.Word w))
    (shape:H.localShape.read m ((low pin).val:Computability.VPVNP.BurstRAM.Word w)=
      ((nodeNumber (k-gain) (group (k-gain) (low pin))*cols:ℕ):Computability.VPVNP.BurstRAM.Word w)) :
    DescentExteriorReplay.result count H m (H.dest.base+row.val)=(next pin:Computability.VPVNP.BurstRAM.Word w) := by
  exact (DescentExteriorReplay.physical H m row).trans
    ((DescentExteriorReplay.read_ordinary H direct m row _ _ _ ancestor stamp _ table shape).trans
      (congrArg (fun ordinal : ℕ => (ordinal : Computability.VPVNP.BurstRAM.Word w))
        (ticket.exterior_ordinal base radix owns pin).symm))

end
end Hierarchy.DescentSixParty.Chronology

end OAI
