import OAI.Hierarchy.DescentPhysicalResetPrime
import OAI.Hierarchy.DescentResetDateStencil
import OAI.Hierarchy.DescentRecordedIssuedStencil

namespace OAI
/-! # The fixed reset program through the selected rotation and all paid stencil cells -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPlainTerminal.Suffix
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (a : PhysicalReset)

local notation "S" => a.successor.middle.stencil

/-- Equalities of the two numerical descriptions of the same dates and dyadic packings. -/
structure StencilShape : Prop where
  hosts : (S).hosts=a.hosts
  ports : (S).maxPorts=a.ports
  dimension : (S).m=a.high+a.low
  bits : (S).b=a.bits
  field : (S).b*2^(S).r=a.field
  groups : 2^(S).c=a.groups
  lanes : (S).M=2^a.e
  divides : 2^(S).c=(2^(S).c/(2^a.re*(S).M))*(2^a.re*(S).M)

theorem StencilShape.of_dyadic (hosts : (S).hosts=a.hosts) (ports : (S).maxPorts=a.ports)
    (dimension : (S).m=a.high+a.low) (bits : (S).b=a.bits)
    (field : (S).b*2^(S).r=a.field) (groups : 2^(S).c=a.groups) (lanes : (S).M=2^a.e)
    (depth : a.re+a.e≤(S).c) : a.StencilShape := by
  refine ⟨hosts,ports,dimension,bits,field,groups,lanes,?_⟩
  have dvd : 2^a.re*(S).M ∣ 2^(S).c := by
    rw [lanes,←pow_add]
    exact pow_dvd_pow _ depth
  exact (Nat.div_mul_cancel dvd).symm

/-- The group count supplied by an issued positive run is recoverable from the fixed date's powers. -/
theorem stencil_group_count (sh : a.StencilShape) (j : ℕ)
    (factor : 2^(S).c=j*(2^a.re*(S).M)) : 2^(S).c/(2^a.re*(S).M)=j := by
  have pos : 0<2^a.re*(S).M := by rw [sh.lanes]; positivity
  rw [factor,Nat.mul_div_cancel _ pos]

def stencilPhase (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) : PackedFlow.ResetMiddle where
  «S» := S
  chart := BankImage.Dated.chart (a.estimator floor).endAddress (a.chart floor).routedHosts a.high a.low a.bits
  high := a.high
  low := a.low
  solve := (a.estimator floor).solveAt
  origin := (a.estimator floor).endAddress
  fresh := (a.chart floor).remixEnd a.payload a.gain a.positive
  counts := ⟨(a.chart floor).first,DescentPackedWalsh.rowBits a.hosts a.high⟩
  peers := fun j=>⟨(a.flow floor).middle+j.val*(a.flow floor).pitch,
    DescentPackedFlowPublication.Book.pitchBits a.hosts a.high⟩
  X := ClosedReset.Recorded.stencilSources (a.estimator floor) count hub a.previousRoster
  ratio := 2^a.re
  groups := 2^(S).c/(2^a.re*(S).M)
  factor := sh.divides
  ratioPos := Nat.two_pow_pos _
  batchPos := by rw [sh.lanes];exact Nat.two_pow_pos _
  positive := by rw [sh.bits];exact a.positive
  f := a.depthCut
  B := a.fullBudget
  K := a.classBound
  g := g
  cap := a.fullBudget
  Y := Y

variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
local notation "P" => a.stencilPhase sh floor count hub g Y

theorem stencil_start : (P).base=a.rebased floor := by
  change Subwords.finish ((a.chart floor).rotationEnd a.payload a.gain a.positive) ((S).b*2^(S).r)
    (((1+(S).maxPorts)+(S).m)*(S).hosts) (2^(S).c) (2^a.re) (S).M=_
  rw [sh.field,sh.ports,sh.dimension,sh.hosts,sh.groups,sh.lanes]
  rfl

theorem stencil_end : (P).endAddress=a.successor.middle.afterStencil (a.rebased floor) :=
  congrArg (S).endAddress (a.stencil_start sh floor count hub g Y)

def throughStencil (src : Bank) (R δ w : ℕ) :=
  (a.prime floor src count R δ w).seq ((P).code w)

def throughStencilTicks (R δ w : ℕ) :=a.primeTicks floor R δ w+(P).time w

/-- The estimator's actual output memory is the starting memory of the rotation and stencil. -/
theorem throughStencil_any (src : Bank) (R δ w : ℕ) (mem : Memory w)
    (front : a.PrimeRoom floor src count R δ w) (back : (P).Room w) :
    ∃prior out,
      (a.prime floor src count R δ w).Exec mem
        ((a.estimator floor).image ((a.estimator floor).literal prior)) (a.primeTicks floor R δ w) ∧
      ((P).code w).Exec ((a.estimator floor).image ((a.estimator floor).literal prior)) out ((P).time w) ∧
      (a.throughStencil sh floor count hub g Y src R δ w).Exec mem out
        (a.throughStencilTicks sh floor count hub g Y R δ w) ∧
      CheapCode (a.throughStencil sh floor count hub g Y src R δ w) := by
  obtain ⟨prior,first⟩:=a.prime_any floor src count R δ w mem front
  obtain ⟨out,second,ctrl⟩:=(P).any back _
  let frontProgram := a.prime floor src count R δ w
  let backProgram := (P).code w
  let mid := (a.estimator floor).image ((a.estimator floor).literal prior)
  refine ⟨prior, out, @first, @second, ?_, ?_⟩
  · exact @Procedure.Exec.then w frontProgram backProgram mem mid out
      (a.primeTicks floor R δ w) ((P).time w) @first @second
  · obtain ⟨frontCheap, _⟩ := a.prime_hardware floor src count R δ w
    exact @cheap_seq w frontProgram backProgram @frontCheap @ctrl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
