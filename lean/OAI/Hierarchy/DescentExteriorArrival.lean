import OAI.Hierarchy.DescentExteriorOrdinaryHop
import OAI.Hierarchy.DescentExteriorResetHop
import OAI.Hierarchy.DescentExteriorCalendar

namespace OAI
/-! # Primitive inputs used at a public-pin ancestry step -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
  {T : StageInput W G u ε} {p : (T.result he).Choice} {nu : Normalize ((T.result he).state p)}
  {target : Reached nu.result G q ε S k (i+1) z' D' wire hist}
  (ticket : Chronology.OrdinaryLink source he T p nu target)
  {bw n : ℕ} (L : Hop) (m : Memory bw) (atPin : Fin n→P)

namespace Chronology.OrdinaryLink
variable (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (owns : ∀p,source.placement.hub (host source p)=true)
local notation "digit" => fun a:Fin n=>(address k ((ticket.pinStep base radix owns).cut (active source base radix (atPin a))).2)
local notation "old" => fun a:Fin n=>(source.vertex (host source (atPin a))).val
local notation "gain" => gainExponent 20 source.placement.degree
local notation "slots" => 2^packExponent 20 source.placement.degree+2

structure Shelf : Prop where
  direct : L.compact=none
  digits : ∀a : Fin n,L.frozenDigit.read m (a.val:Computability.VPVNP.BurstRAM.Word bw)=((digit a).val:Computability.VPVNP.BurstRAM.Word bw)
  bases : ∀a : Fin n,L.hostBase.read m (old a:Computability.VPVNP.BurstRAM.Word bw)=((old a*((2^(k+1)-1)*slots):ℕ):Computability.VPVNP.BurstRAM.Word bw)
  localRanks : ∀a : Fin n,L.localShape.read m ((digit a).val:Computability.VPVNP.BurstRAM.Word bw)=((nodeNumber (k-gain) (group (k-gain) (digit a))*slots:ℕ):Computability.VPVNP.BurstRAM.Word bw)

omit [Fintype P] in
theorem shelf_step (held : Holds m L.source (source.vertex.trans Fin.valEmbedding) (host source) atPin)
    (cells : ticket.Shelf L m atPin base radix owns) (size : n≤L.dest.size) (word : L.dest.size<2^bw) :
    Holds (result n L m) L.dest (target.vertex.trans Fin.valEmbedding) (host target) atPin := by
  apply DescentExteriorReplay.advance m L L.dest rfl size word
  intro a
  exact ticket.hop_read base radix owns L cells.direct m a (atPin a) (held a) (cells.digits a) (cells.bases a) (cells.localRanks a)

end Chronology.OrdinaryLink

namespace ClosedReset
variable {n₀ h C f g cut tail₀ : ℕ} {ctl : ResetRates G S k D n₀ h C f g cut tail₀}
  (b : ClosedReset source ctl) (owns : ∀p,source.placement.hub (host source p)=true)
local notation "digit" => fun a:Fin n=>(address k ((b.pinStep owns).cut (active source ctl.base ctl.radix (atPin a))).2)
local notation "old" => fun a:Fin n=>(source.vertex (host source (atPin a))).val
local notation "vertex" => b.frame.host.symm.toEmbedding.trans source.vertex
local notation "palette" => DescentDenseHostOrder.roster b.reset.graph (b.reset.k-b.terminals.commonDepth) (GroupStage.depthBound D n₀ f g)

/-- The compact table here is the very bitmap prefix returned by the genuine
reset host scan. Its argument is the issued sparse terminal, not a future exterior row. -/
structure Shelf (bank : Bank) : Prop where
  compact : L.compact=some bank
  digits : ∀a : Fin n,L.frozenDigit.read m (a.val:Computability.VPVNP.BurstRAM.Word bw)=((digit a).val:Computability.VPVNP.BurstRAM.Word bw)
  bases : ∀a : Fin n,L.hostBase.read m (old a:Computability.VPVNP.BurstRAM.Word bw)=((old a*(palette).card:ℕ):Computability.VPVNP.BurstRAM.Word bw)
  localRanks : ∀a : Fin n,L.localShape.read m ((digit a).val:Computability.VPVNP.BurstRAM.Word bw)=(b.localTrunk (digit a):Computability.VPVNP.BurstRAM.Word bw)
  roster : ∀u,bank.read m ((b.reset.rawHostRank b.terminals vertex u).val:Computability.VPVNP.BurstRAM.Word bw)=
    ((b.reset.denseHostRank b.terminals vertex u).val:Computability.VPVNP.BurstRAM.Word bw)

omit [Fintype P] in
theorem shelf_step (held : Holds m L.source (source.vertex.trans Fin.valEmbedding) (host source) atPin)
    (bank : Bank) (cells : b.Shelf L m atPin owns bank) (size : n≤L.dest.size) (word : L.dest.size<2^bw) :
    Holds (result n L m) L.dest (b.next.vertex.trans Fin.valEmbedding) (host b.next) atPin := by
  apply DescentExteriorReplay.advance m L L.dest rfl size word
  intro a
  exact b.hop_read owns L bank cells.compact m a (atPin a) (held a) (cells.digits a) (cells.bases a)
    (cells.localRanks a) cells.roster

end ClosedReset
end
end Hierarchy.DescentSixParty

end OAI
