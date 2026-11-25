import OAI.Hierarchy.DescentResetRepackTariff
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # Instruction, register and constant-slot counts for the same reset CPU -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentGLPacked DescentPacking.PackedMatch.Local DescentSIMDLookup
open DescentPackedColony DescentColonies.CandidateRAM DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem image_text {w : ℕ} (I : Phase.Arena.Image w) : Bounded I.program (4+10*I.length) :=
  ⟨I.hardware.1,by change names I.program≤_;rw [I.hardware.2];omega⟩

theorem repack_text (S : StencilBook) (chip : Bank) (first ratio w : ℕ) {K₀ : ℕ}
    (factor : 2^S.c=K₀*(ratio*S.M)) (ratioPos : 0<ratio) (pos : 0<S.M)
    (nonempty : 0<S.rows) : Bounded (repackProgram S chip first ratio factor ratioPos pos w)
       (repackTime S chip first ratio factor ratioPos pos) := by
  let H:=((1+S.maxPorts)+S.m)*S.hosts
  let a:=S.b*2^S.r
  let I:=Subwords.literals (w:=w) first H a factor ratioPos pos
  let T:=Subwords.chart first a H (2^S.c) ratio S.M
  let out:=Subwords.destination first a H (2^S.c) ratio S.M
  have nr:0<H*chunks (2^S.c) S.M:=by
    dsimp [H];rw [Nat.mul_assoc];exact Nat.mul_pos (by omega) nonempty
  exact seq_bound (image_text I) (scan_bound w out _ (Subwords.term T chip) nr)

theorem paid_text (S : StencilBook) (X : StencilBook.Sources) (base out f B K g cap Y w : ℕ)
    (rows : 0<S.rows) : Bounded (paidProgram S X base out f B K g cap Y w) (paidTime S X base out f B g) := by
  let A:=S.layer base out X.roster
  let L:=S.chosen base out X.roster
  let H:=S.header base
  let C:=S.readers base
  let F:=S.last base
  let D:=32*Nat.clog 2 (2*S.degree)
  let limit:=2^(f+1)*B
  let I:=splitImage A S.degree S.hosts S.c S.r S.b S.M D limit w
  let P:=S.inputs X base out g
  have old:=seq_bound (image_text I) (passes_bound w (passes L S.hosts (2^S.c) S.M S.r) (by
    intro pass member
    obtain ⟨s,hs,rfl⟩:=pass_in L _ _ _ _ member
    exact rows))
  have scalar:=seq_bound (seq_bound (image_text (H.chart (w:=w))) (image_text (H.cutoff S.levels S.total K (2^f*B) (2^S.r*cap)))) (image_text (S.castImage base))
  have readers:=seq_bound (image_text (C.image (w:=w))) (image_text C.planes)
  have code:=seq_bound (image_text (F.gathers (w:=w))) (image_text (F.literals f B Y))
  have collect:=scan_bound w F.scratch S.rows (Stencil.assembly F.tabs (C.inputs P).field) rows
  have lookup:=scan_bound w F.out S.rows (DescentSIMDLookup.lookup F.banks) rows
  have all:=seq_bound (seq_bound old scalar) (seq_bound (seq_bound readers code) (seq_bound collect lookup))
  have header:H.origin≤H.stop:=by dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,
    PortLevels.AddressBook.depth,PortLevels.AddressBook.pos];omega
  have cutoff:H.stop≤(S.narrow base).base:=by change H.stop≤Cutoff.finish H.stop _ _;unfold Cutoff.finish; simp only [Nat.add_assoc, Nat.le_add_right]
  have ca:C.origin≤C.planeBase:=C.before_planes
  have cb:C.planeBase≤C.stop:=C.plane_le
  have f₁:F.base≤F.table:=Nat.le_add_right ..
  have f₂:F.table≤F.scratch:=by dsimp only [Stencil.Layout.Chart.scratch,Stencil.Layout.Chart.mask]; simp only [Nat.add_assoc, Nat.le_add_right]
  have eqHead:(H.chart (w:=w)).length+(H.cutoff (w:=w) S.levels S.total K (2^f*B) (2^S.r*cap)).length=
      (S.narrow base).base-H.origin:=by change H.stop-H.origin+((S.narrow base).base-H.stop)=_;omega
  have eqReads:(C.image (w:=w)).length+(C.planes (w:=w)).length=C.stop-C.origin:=by
    change C.planeBase-C.origin+(C.stop-C.planeBase)=_;omega
  have eqLast:(F.gathers (w:=w)).length+(F.literals (w:=w) f B Y).length=F.scratch-F.base:=by
    change F.table-F.base+(F.scratch-F.table)=_;omega
  apply Eq.mp (congrArg (Bounded (paidProgram S X base out f B K g cap Y w)) ?_) all
  simp only [paidTime,StencilBook.splitTime,StencilBook.scalarTime,Stencil.time,Stencil.cost,
    DescentSIMDLookup.lookup_work]
  change _ = (4+10*I.length+clock (passes L S.hosts (2^S.c) S.M S.r)+
    ((8+10*((S.narrow base).base-H.origin))+(4+10*(S.castImage (w:=w) base).length)))+
    (((8+10*(C.stop-C.origin))+(8+10*(F.scratch-F.base)))+
      ((4+S.rows*(2*(Stencil.assembly F.tabs (C.inputs P).field).work+4))+(4+44*S.rows)))
  omega

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
