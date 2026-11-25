import OAI.Hierarchy.GridEvaluatorHardware
import OAI.Hierarchy.TraceReceiverProgram
import OAI.Hierarchy.GridReceiverTickDirectory
import OAI.Computability.VPVNP.RAMClock

namespace OAI
/-! # Hardware of the independent receiving computation -/

noncomputable section
namespace Hierarchy.TraceReceiverProgram
open ThreeFlat RAM PhysicalProcedure Diagonal PhysicalStage
open NavigationPass NavigationDirectory NodePublication TraceAdmission TraceNodeHeaders
open Computability.VPVNP.BurstRAM PrivateRAM Filter
open HistoryStageBody.Physical (resources resources_seq)
open scoped Classical Fin.CommRing

/-- For both physical archive placements the two scans have fixed text.  The
archive locations, rooted stage table and row tariff remain genuine operands. -/
theorem navigation_hardware {F : Type} [Field F] [Fintype F] (B : Block F) :
    ∃ H,∀ (W : ℕ) (d : Directory),d.archive.K=B.alphabetCap →
      d.archive.initialDegree=2^(B.exponent 0) →
      d.node.childCap=directoryCap B → d.node.halfCap=directoryCap B →
      d.node.motifCap=directoryCap B → resources (navigation B W d)≤H := by
  obtain ⟨R,repeated⟩ := repeated_hardware B B.alphabetCap
  refine ⟨(4465+2192*2^(B.exponent 0))+(R+2000)+(100+compactHardware (directoryCap B)+Resources.registerSize),?_⟩
  intro W d alpha degree children halves motifs
  have loop := repeated W (d.archive.control:Word W) ((d.archive.control+1:ℕ):Word W)
  have tail := GridSelector.terminal_hardware d.archive d.stages d.edges W
  change resources (TerminalWireArchive.program (W:=W) (d.archive.terminal d.stages d.edges W))≤2000 at tail
  unfold navigation GridPhysicalAdmission.program
  rw [resources_seq,resources_seq,resources_seq,GridEvaluatorHardware.seed_size,degree,alpha,
    Resources.capped_registration_hardware _ _ _ _ _ _ _ _ _ _ _ children halves motifs]
  omega

/-- A fixed instruction and register multiplier on polynomial logarithmic
scale fits every one of the three actual architecture indices. -/
theorem eventually_capacity (coefficient exponent : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {p r k : ℕ} (M : Machine (64*w) p r k),
      p+r+k≤coefficient*(w.log2+1)^exponent → GridEvaluatorHardware.FitsCapacity M := by
  filter_upwards [eventually_polylog_le (1024*coefficient) exponent] with w bound
  intro p r k M small
  have paid : (p+r+k)*1024 ≤ w := calc
    _ ≤ (coefficient*(w.log2+1)^exponent)*1024 := Nat.mul_le_mul_right _ small
    _ = (1024*coefficient)*(w.log2+1)^exponent := by ring
    _ ≤ _ := bound
  have lim := (Nat.le_div_iff_mul_le (by decide : 0<1024)).2 paid
  change p≤w/1024 ∧ r≤w/1024 ∧ k≤w/1024
  omega

private theorem machine_price (p r k a b c coefficient scale : ℕ)
    (srcSize : p+r+k ≤ coefficient*scale) (one : 1 ≤ scale) :
    (37+(p+400)+a)+(19+(r+129)+b)+(6+(k+1)+c) ≤
      ((37+400+19+129+6+1+a+b+c)+coefficient)*scale := by
  have paid := Nat.mul_le_mul_left (37+400+19+129+6+1+a+b+c) one
  rw [Nat.mul_one] at paid
  rw [Nat.add_mul]
  calc
    _ = (37+400+19+129+6+1+a+b+c)+(p+r+k) := by ac_rfl
    _ ≤ _ := Nat.add_le_add paid srcSize

/-- The actual header shift, ordered gather and seven-slot weighted machine
add fixed hardware to the source program at every data arity and time cap. -/
theorem eventual_machine {F : Type} [Field F] [Fintype F]
    (coefficient exponent : ℕ) : ∀ᶠ w : ℕ in atTop,
    ∀ {p H J : ℕ} (fit : RAM.Contraction.Fits (RAM.TickWeightedBank.shape F p H J) (64*w))
      (src : Procedure (64*w)) (cursor control header row lut : ℕ),
      resources src≤coefficient*(w.log2+1)^exponent →
      GridEvaluatorHardware.FitsCapacity (machine fit src cursor control header row lut) := by
  let extra := 37+400+19+129+6+1+(TraceFactorReceiver.overhead F).1+
    (TraceFactorReceiver.overhead F).2.1+(TraceFactorReceiver.overhead F).2.2
  filter_upwards [eventually_capacity (extra+coefficient) exponent] with w native
  intro p H J fit src cursor control header row lut srcSize
  apply native
  have labels := congrArg (fun d : ℕ×ℕ×ℕ => d.1+d.2.1+d.2.2)
    (machine_dimensions fit src cursor control header row lut)
  change _ = (37+(src.labels+400)+(TraceFactorReceiver.overhead F).1)+
    (19+(src.registers+129)+(TraceFactorReceiver.overhead F).2.1)+
    (6+(src.slots+1)+(TraceFactorReceiver.overhead F).2.2) at labels
  let dims := TraceFactorReceiver.dimensions (machine fit src cursor control header row lut)
  change dims.1+dims.2.1+dims.2.2≤(extra+coefficient)*(w.log2+1)^exponent
  change dims.1+dims.2.1+dims.2.2=_ at labels
  rw [labels]
  exact machine_price src.labels src.registers src.slots (TraceFactorReceiver.overhead F).1
    (TraceFactorReceiver.overhead F).2.1 (TraceFactorReceiver.overhead F).2.2 coefficient
    ((w.log2+1)^exponent) srcSize (Nat.pow_pos (Nat.succ_pos _))

/-- Only the sparse compilation and map/task builders contribute variable
text after the common physical archive and the actual class-major root scan.
All phase parameters, including the selected grid dimensions, are uniform in
the architecture estimate. -/
theorem sources_capacity {F : Type} [Field F] [Fintype F] (B : Block F)
    (coefficient exponent : ℕ) : ∀ᶠ w : ℕ in atTop,
    ∀ (d : Directory) (v text argCount N dims teams : ℕ)
      (compileRoots publishTasks : Procedure (64*w)) (current commands tasks : ℕ),
      d.archive.K=B.alphabetCap → d.archive.initialDegree=2^(B.exponent 0) →
      d.node.childCap=directoryCap B → d.node.halfCap=directoryCap B →
      d.node.motifCap=directoryCap B →
      resources compileRoots+resources publishTasks≤coefficient*(w.log2+1)^exponent →
      ∀ {p H J : ℕ} (fit : RAM.Contraction.Fits (RAM.TickWeightedBank.shape F p H J) (64*w))
        (cursor control header row lut : ℕ),
        GridEvaluatorHardware.FitsCapacity (machine fit
          (sources B d (GridReceiverTickDirectory.receiver w v text argCount N dims teams)
            compileRoots publishTasks current commands tasks) cursor control header row lut) := by
  obtain ⟨K,nav⟩:=navigation_hardware B
  filter_upwards [eventual_machine (F:=F) ((K+2874)+coefficient) exponent] with w available
  intro d v text argCount N dims teams compileRoots publishTasks current commands tasks
    alpha deg children halves motifs sparse p H J fit cursor control header row lut
  apply available
  have a:=nav (64*w) d alpha deg children halves motifs
  have pick:=GridReceiverTickDirectory.receiver_hardware w v text argCount N dims teams
  have select : resources (GridReceiverTickDirectory.receiver w v text argCount N dims teams)≤800 := by
    obtain ⟨labels,regs,slots⟩:=pick
    unfold resources
    omega
  have publish:=TraceFactorReceiver.Commands.dimensions (64*w) current commands tasks
  have cmd : resources (TraceFactorReceiver.Commands.procedure (64*w) current commands tasks)≤2074 := by
    obtain ⟨labels,regs,slots⟩:=publish
    unfold resources
    omega
  have one : 1≤(w.log2+1)^exponent := Nat.pow_pos (by omega)
  have paid:=Nat.mul_le_mul_left (K+2874) one
  rw [Nat.mul_one] at paid
  simp only [sources,resources_seq]
  rw [Nat.add_mul]
  omega

end Hierarchy.TraceReceiverProgram
end

end OAI
