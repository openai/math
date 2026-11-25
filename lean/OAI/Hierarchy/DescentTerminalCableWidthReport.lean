import OAI.Hierarchy.DescentTerminalCableWidthTape

namespace OAI
/-! # The physically indexed cable prefix and header profiles at the earlier cable date -/
namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSixParty DescentCompiler DescentColonies DescentTerminalCableOrder DescentSortedRoster
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalHeaderGroups
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {deg k i H groups M d w p : ℕ} {bits:P→ℕ} {W:MarkedWorld F deg P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (groupsAt:J↪Fin groups) (hosts:V↪Fin H) (raw:Fin H→Fin A.degree→Option (Fin H))
    (C:Sockets) (m:Memory w) (cable:Block k→Fin (2*A.cap)→Bank) (positive:0<M)
    (scale q n:ℕ) (oldOrder:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (external:P↪ℕ) (nodes:W.graph.Site↪ℕ)
    (ops:∀v,DescentKernelHistory.Boundary W.graph v↪ℕ)
local notation "R" => indexed raw
local notation "atH" => fun v:W.graph.Site=>hosts (A.pos v).2
local notation "ctl" => (⟨C,H,A.degree,d,scale,n,cable,positive⟩:Rack (2^k) A.cap groups M)
local notation "amounts" => slotCount (p:=p) R W.graph atH
variable (presentAt:∀v,present raw (hosts v)=(A.near v).map hosts) (hp:0<p) (hq:0<q)
    (grain:A.z*G.b=scale*p) (extWidth:∀z,p∣bits z)
local notation "xs" => stream W.graph atH oldOrder external nodes ops q hp (H*H)

variable (fit:(⟨C,H,A.degree,d,scale,n,cable,positive⟩ : Rack (2^k) A.cap groups M).Fits w) (hostFits:H<2^w) (degreeFits:A.degree<2^d)
    (width:DescentSignedCableCodec.width A.degree A.cap*M≤d)
    (rosterSize:H*A.degree≤C.roster.size)
    (roster:∀(h:Fin H)(j:Fin A.degree),m (C.roster.base+(h.val*A.degree+j.val))=(DescentPackedColony.target (indexed raw h j):Word w))
    (cableSize:∀x j,H*chunks groups M≤(cable x j).size)
    (old:∀x t,Reads (cable x t) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groupsAt hosts x t h g)) M m)
    (heap:H*chunks groups M≤2^w) (maxRows:(stream W.graph (fun v => hosts (A.pos v).2) oldOrder external nodes ops q hp (H*H)).length≤n)
set_option maxHeartbeats 1000000 in
include presentAt hp hq grain extWidth fit hostFits degreeFits width rosterSize roster cableSize old heap maxRows in
theorem cable_fields (rom:ℕ) (rem whole index control:Bank) (prior:rom+DescentTerminalDenseHeaderBoot.extent q p≤C.origin)
    (static_:∀j<DescentTerminalDenseHeaderBoot.extent q p,m (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j) :
    DescentTerminalDenseHeaderRAM.Reads (DescentTerminalDenseHeaderBoot.layout q p rom (ctl).printer.output rem whole index control)
      (padded (n:=n) xs) ((ctl).final q p m) ∧
    ∀j : Fin (H*A.degree),(ctl).printer.prefix.read ((ctl).final q p m) (j.val : Word w)=
      ((DescentTerminalWidthRowsRAM.passed q p amounts (j.val+1)).length : Word w) := by
  have report := cable_widths A native S ready groupsAt hosts raw C m cable positive scale q n
    oldOrder external nodes ops presentAt hp hq grain extWidth fit hostFits degreeFits width
    rosterSize roster cableSize old heap maxRows rom rem whole index control prior static_
  refine ⟨report.2.2.1,?_⟩
  intro j
  have space := fit.space
  have bound : (ctl).printer.prefix.base+(ctl).printer.prefix.size ≤ (ctl).printer.stop := by
    change _ ≤ (ctl).printer.prefix.base+(ctl).printer.prefix.size+(ctl).printer.output.size+1+
      (ctl).printer.groups+(ctl).printer.groups
    omega
  have enough : j.val < (ctl).printer.prefix.size :=
    j.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have word : j.val < 2^w := by omega
  change (ctl).final q p m ((ctl).printer.prefix.base + (j.val : Word w).val % (ctl).printer.prefix.size) = _
  rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt enough]
  exact report.2.2.2.1 j

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
