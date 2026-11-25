import OAI.Hierarchy.DescentTerminalCableWidthMachine

namespace OAI
/-! # The actual four header tables and native cable width stream in the same memory -/
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
theorem cable_widths (rom:ℕ) (rem whole index control:Bank) (prior:rom+DescentTerminalDenseHeaderBoot.extent q p≤C.origin)
    (static_:∀j<DescentTerminalDenseHeaderBoot.extent q p,m (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j) :
    ((ctl).program w q p).Exec m ((ctl).final q p m) ((ctl).time q p) ∧ CheapCode ((ctl).program w q p) ∧
    DescentTerminalDenseHeaderRAM.Reads (DescentTerminalDenseHeaderBoot.layout q p rom (ctl).printer.output rem whole index control)
      (padded (n:=n) xs) ((ctl).final q p m) ∧
    (∀i:Fin (H*A.degree),(ctl).final q p m ((ctl).printer.prefix.base+i.val)=
      ((DescentTerminalWidthRowsRAM.passed q p amounts (i.val+1)).length:Word w)) ∧
    ∀j,j<C.origin→(ctl).final q p m j=m j := by
  have phys:=(ctl).run q p m fit
  have spacing:=(ctl).gaps
  have m₀:(ctl).slab≤(ctl).population.base:=Nat.le_add_right ..
  have socketEnd:C.stop H A.degree<2^w:=by change (ctl).base<_ ;have top:=fit.space;omega
  have dw : d ≤ w := ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp fit.digit).le
  have score (i:Fin (H*A.degree)) : ((ctl).gates (DescentTerminalPointerDigits.Gather.values (ctl).readCols ((ctl).boot m) i)).val=amounts i :=
    measured A native S ready groupsAt hosts raw presentAt C m cable positive socketEnd hostFits degreeFits width dw
      fit.roster rosterSize roster fit.prior cableSize old heap hp scale grain i
  have cap_ (i:Fin (H*A.degree)):amounts i≤(ctl).printer.cap := (score i) ▸ (tally_bound A.degree scale positive _)
  have actual (i:Fin (H*A.degree)):(ctl).counters m ((ctl).population.base+i.val)=(amounts i:Word w) := by
    exact (phys.2.2.1 i).trans (congrArg (fun a : ℕ => (a : Word w)) (score i))
  have inside (e:W.graph.Edge):p∣W.graph.width e := by
    refine ⟨A.grainCount e*scale,?_⟩
    rw [A.grainCount_fit S ready e,grain];ac_rfl
  have tape := slot_stream R W.graph atH oldOrder external nodes ops hp inside extWidth (sorted_mounted raw) (fun e _=>by
    rw [mounted_present A hosts raw presentAt,mounted_present A hosts raw presentAt]
    exact all_adjacent A hosts raw presentAt e) q
  have budget := maxRows
  rw [←tape] at budget
  have priorPop:(ctl).population.Fits w (ctl).printer.origin:=⟨Nat.two_pow_pos _,by
    have lim:=spacing.2.2.2.trans_lt fit.space;change (ctl).population.base+(ctl).population.size<_ at lim;omega,le_rfl⟩
  have widthOut:=DescentTerminalWidthRowsRAM.run (ctl).printer q p amounts ((ctl).counters m) cap_ budget priorPop
    (Nat.le_pow_clog (by decide) _) fit.space actual
  refine ⟨phys.1,phys.2.1,?_,widthOut.2.2.2.1,phys.2.2.2⟩
  apply DescentTerminalDenseHeaderBoot.reads _ _ _ _ _ _ _ _ (Nat.mul_pos hq hp) (prior.trans_lt (spacing.1.trans_lt socketEnd))
  · rw [←tape]
    exact widthOut.2.2.1
  · intro j hj
    exact (phys.2.2.2 (rom+j) ((Nat.add_lt_add_left hj rom).trans_le prior)).trans (static_ j hj)

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
