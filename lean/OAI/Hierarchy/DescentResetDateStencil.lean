import OAI.Hierarchy.DescentResetMiddleAny
import OAI.Hierarchy.DescentResetTotalStencil

namespace OAI
/-! # Public procedure between the reset estimator and the signed-cable window -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGL DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated DescentColonies DescentGLNielsen
open DescentPlainTerminal.Suffix DescentSIMDLookup ProtocolRAM DescentPackedWalsh
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

structure ResetMiddle where
  S : StencilBook
  chart : Chart
  high : ℕ
  low : ℕ
  solve : ℕ
  origin : ℕ
  fresh : ℕ
  counts : Bank
  peers : Fin S.maxPorts→Bank
  X : StencilBook.Sources
  ratio : ℕ
  groups : ℕ
  factor : 2^S.c=groups*(ratio*S.M)
  ratioPos : 0<ratio
  batchPos : 0<S.M
  positive : 0<S.b
  f : ℕ
  B : ℕ
  K : ℕ
  g : ℕ
  cap : ℕ
  Y : ℕ

namespace ResetMiddle
variable (P : ResetMiddle)
def dim:=P.high+P.low
def stages:=(schedule P.dim).length
def chip:=(P.chart.chosen P.dim).bank P.stages
def saved:=P.fresh+(2^P.dim)^P.dim+(2^P.dim)^P.dim
def first:=P.saved+1
def sheets:=((1+P.S.maxPorts)+P.S.m)*P.S.hosts
def width:=P.S.b*2^P.S.r
def bank:=Subwords.destination P.first P.width P.sheets (2^P.S.c) P.ratio P.S.M
def base:=Subwords.finish P.first P.width P.sheets (2^P.S.c) P.ratio P.S.M
def output:=P.S.output P.base
def endAddress:=P.S.endAddress P.base

def code (w : ℕ) :=
  (middle P.chart P.origin P.solve P.fresh P.counts P.peers P.S.hosts P.high P.low w P.positive).seq
    ((Padded.repackProgram P.S P.chip P.first P.ratio P.factor P.ratioPos P.batchPos w).seq
      (Padded.paidProgram P.S P.X P.base P.bank P.f P.B P.K P.g P.cap P.Y w))
def time (w : ℕ) :=
  middleTime P.chart P.origin P.solve P.counts P.peers P.S.hosts P.high P.low w P.positive+
    (Padded.repackTime P.S P.chip P.first P.ratio P.factor P.ratioPos P.batchPos+
      Padded.paidTime P.S P.X P.base P.bank P.f P.B P.g)

structure Room (w : ℕ) : Prop where
  previous : PhysicalTrajectory.outputBase P.dim P.solve+2^P.dim≤P.origin
  counts : P.counts.Fits w P.origin
  peers : ∀i,(P.peers i).Fits w P.origin
  area : Size P.chart (((1+P.S.maxPorts)+P.dim)*P.S.hosts) P.high P.low P.S.b w
  words : wordEnd P.origin P.high P.low≤P.chart.input.base
  fence : P.chart.input.base+P.chart.input.size≤P.chart.flags
  power : (powers P.origin P.dim).Fits w P.chart.input.base
  offsets : (cols P.origin P.dim).offsets.Fits w P.chart.input.base
  switches : (cols P.origin P.dim).switches.Fits w P.chart.input.base
  planes : ∀i : Fin P.dim,(Original.bank (plane P.origin P.dim) P.high i).Fits w P.chart.input.base
  kept : ∀i : Fin P.dim,PhysicalTrajectory.pointer P.dim P.solve i.val<P.fresh
  saveRoom : P.first<2^w
  chip : P.chip.Fits w P.first
  rows : P.sheets*chunks (2^P.S.c) (P.ratio*P.S.M)≤P.chip.size
  repack : P.base<2^w
  operands : StencilBook.Geometry P.S P.X P.base P.bank w
  total : P.endAddress<2^w
  short : P.S.M*max (P.S.n*Stencil.count P.S.r (P.S.degree+P.S.degree)) (P.S.t*2^P.S.r)≤w/2
  word : P.S.n*P.S.M≤w

private theorem assemble {w : ℕ} (m mid short out : Memory w) :
  let A := middle P.chart P.origin P.solve P.fresh P.counts P.peers P.S.hosts P.high P.low w P.positive
  let B := Padded.repackProgram P.S P.chip P.first P.ratio P.factor P.ratioPos P.batchPos w
  let C := Padded.paidProgram P.S P.X P.base P.bank P.f P.B P.K P.g P.cap P.Y w
  let ca := middleTime P.chart P.origin P.solve P.counts P.peers P.S.hosts P.high P.low w P.positive
  let cb := Padded.repackTime P.S P.chip P.first P.ratio P.factor P.ratioPos P.batchPos
  let cc := Padded.paidTime P.S P.X P.base P.bank P.f P.B P.g
  A.Exec m mid ca → B.Exec mid short cb → C.Exec short out cc →
  CheapCode A → CheapCode B → CheapCode C →
  (P.code w).Exec m out (P.time w) ∧ CheapCode (P.code w) := by
  intro A B C ca cb cc moved retiled said a b c
  exact ⟨@Procedure.Exec.then w A (B.seq C) m mid out ca (cb+cc) @moved
    (@Procedure.Exec.then w B C mid short out cb cc @retiled @said),
    @cheap_seq w A (B.seq C) @a (@cheap_seq w B C @b @c)⟩

theorem any {w : ℕ} (bounds : P.Room w) (m : Memory w) :
    ∃out,(P.code w).Exec m out (P.time w) ∧ CheapCode (P.code w) := by
  obtain ⟨mid,moved,a⟩:=middle_any (D := P.S.maxPorts) (H := P.S.hosts) (h := P.high) (l := P.low) P.chart P.origin P.solve P.fresh P.counts P.peers P.positive m bounds.previous
    bounds.counts bounds.peers bounds.area bounds.words bounds.fence bounds.power bounds.offsets bounds.switches
    bounds.planes bounds.kept bounds.saveRoom
  obtain ⟨short,retiled,b⟩:=Padded.repack_any P.S P.chip P.first P.ratio P.factor P.ratioPos P.batchPos mid
    bounds.chip bounds.rows bounds.repack
  obtain ⟨out,said,c⟩:=Padded.paid_any P.S P.X P.base P.bank P.f P.B P.K P.g P.cap P.Y short
    bounds.operands bounds.total bounds.short bounds.word
  exact ⟨out, P.assemble m mid short out @moved @retiled @said @a @b @c⟩

/-- Malformed input executes the identical branch and can only write inside its dated arena. -/
theorem any_framed {w : ℕ} (bounds : P.Room w) (m : Memory w)
    (ordered : P.chart.heap P.dim+P.stages*P.chart.page≤P.fresh)
    (floor : P.origin≤P.first) :
    ∃out,(P.code w).Exec m out (P.time w) ∧ CheapCode (P.code w) ∧
      ∀z,z<P.origin ∨ P.endAddress≤z → out z=m z := by
  obtain ⟨mid,moved,a,frame₁⟩:=middle_any_framed (D := P.S.maxPorts) (H := P.S.hosts) (h := P.high) (l := P.low) P.chart P.origin P.solve P.fresh P.counts P.peers P.positive m
    bounds.previous bounds.counts bounds.peers bounds.area bounds.words bounds.fence bounds.power bounds.offsets
    bounds.switches bounds.planes bounds.kept bounds.saveRoom ordered
  obtain ⟨short,retiled,b,frame₂⟩:=Padded.repack_any_framed P.S P.chip P.first P.ratio P.factor
    P.ratioPos P.batchPos mid bounds.chip bounds.rows bounds.repack
  obtain ⟨out,said,c,frame₃⟩:=Padded.paid_any_framed P.S P.X P.base P.bank P.f P.B P.K P.g P.cap P.Y short
    bounds.operands bounds.total bounds.short bounds.word
  have tile:P.first≤P.base:=by unfold base Subwords.finish Subwords.destination;omega
  have last : P.base ≤ P.endAddress := by
    rw [endAddress, P.S.extent]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  have top:P.first=P.fresh+2*((2^(P.high+P.low))^(P.high+P.low))+1:=by unfold first saved dim;omega
  obtain ⟨run, cheap⟩ := P.assemble m mid short out @moved @retiled @said @a @b @c
  refine ⟨out, @run, @cheap, ?_⟩
  intro z away
  rcases away with lo|hi
  · exact (frame₃ _ (.inl (lo.trans_le (floor.trans tile)))).trans
      ((frame₂ _ (.inl (lo.trans_le floor))).trans (frame₁ _ (.inl lo)))
  · exact (frame₃ _ (.inr hi)).trans ((frame₂ _ (.inr (last.trans hi))).trans
      (frame₁ _ (.inr (by rw [←top];exact (tile.trans last).trans hi))))

end ResetMiddle
end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
