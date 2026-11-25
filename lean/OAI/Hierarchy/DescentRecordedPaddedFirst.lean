import OAI.Hierarchy.DescentRecordedMixer
import OAI.Hierarchy.DescentPackedCanvasRows
import OAI.Hierarchy.DescentEstimatorLiteralIssue

namespace OAI
/-! # Chronological reset basis on the fixed public host and port canvas -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "full" => (A).wire*((A).z*G.b)*(A).cap

/-- Actual old signed load or traffic at each physical input of the fixed
public estimator. Unused host and port slots have zero load. -/
def publicLoad (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) : Fin E.hosts→DescentGL.Bits E.dim→ℕ :=
  let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let H := (A).numberedHeader digits input.vertex
  let loc := PackedFlow.Canvas.loc A H.site digits f input.valid.host (input.branch.le.trans ports)
  let levels := inputLevels (k:=E.dim) (H.depth A f)
  let siteLoad := fun (v : input.V) (z : DescentGL.Bits E.dim)=>(A).resetLoad digits v (DescentColonies.address E.dim z)
  let edgeLoad := fun (e : Contacts (A).mutual) (z : DescentGL.Bits E.dim)=>
    (A).resetFlow digits e.1 e.2.val (DescentColonies.address E.dim z)
  fun v=>padded loc (load levels siteLoad edgeLoad) (fun _=>0) (v.cast hostCount)

include accepted in
/-- Run the basis solver for the selected branch using its preassigned public
rectangle. Every real contact uses the source's slot in the padded row table. -/
theorem padded_mixer_run_first {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (rect :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
        E.depthRows.base E.gainRows.base E.start mem)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (fixed : ∀a<E.start,mem a=E.literal mem a)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    ∃ μ : Layout E.dim, HEq μ reset.frame.basis ∧
      (E.cpu w).Exec mem (E.image mem) E.clock ∧
      (∀a : Fin E.dim,E.image mem (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val : Word w)) ∧
      (∀a : Fin (2^E.dim),E.image mem (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val : Word w)) ∧
      (∀a<E.start,E.image mem a=mem a) ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) (E.image mem) := by
  rcases E with ⟨slots,high,low,payload,precision,gainBits',positive,origin,gap,depthRows,gainRows⟩
  change slots=S.hostSize i*((high+low)+1+maxPorts) at hostCount
  subst slots
  let U : EstimatorArena :=
    ⟨S.hostSize i*((high+low)+1+maxPorts),high,low,payload,precision,gainBits',positive,origin,gap,
      depthRows,gainRows⟩
  let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let name := ((A).numberedHeader digits input.vertex).site
  let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
  exact accepted.mixer_run_from_rows_first U dim mem grain old branch live localBits localGain
    fit stage small score fixed issue loc rect.input rect.levels rect.gains

include accepted in
/-- Install the estimator's actual immediate table before solving the selected
reset basis. Packed source values and both measurement columns survive this
installation. Earlier user data outside the static table retain their values. -/
theorem install_padded_mixer_first {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (rect :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
        E.depthRows.base E.gainRows.base E.start mem)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    ∃ μ : Layout E.dim, HEq μ reset.frame.basis ∧
      ((E.header (w:=w)).program.seq (E.cpu w)).Exec mem (E.image (E.literal mem))
        (4+10*(E.staticEnd-E.origin)+E.clock) ∧
      (∀a : Fin E.dim,E.image (E.literal mem) (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val : Word w)) ∧
      (∀a : Fin (2^E.dim),E.image (E.literal mem) (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val : Word w)) ∧
      (∀a<E.start,a<E.origin ∨ E.staticEnd≤a → E.image (E.literal mem) a=mem a) ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) (E.image (E.literal mem)) := by
  let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let name := ((A).numberedHeader digits input.vertex).site
  let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
  obtain ⟨fixed,depthPage,gainPage,above⟩ := E.original_pages mem fit
  have loaded : PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits
      f K loc E.depthRows.base E.gainRows.base E.start (E.literal mem) := by
    constructor
    · intro v r
      exact (above _ (Nat.le_add_right ..)).trans (rect.input v r)
    · intro v
      exact (depthPage (v.cast hostCount.symm)).trans (rect.levels v)
    · intro v
      exact (gainPage (v.cast hostCount.symm)).trans (rect.gains v)
  obtain ⟨μ,basis,run,rows,perm,below,first⟩ := accepted.padded_mixer_run_first E dim (E.literal mem) maxPorts
    ports hostCount loaded grain old branch live localBits localGain fit stage small score
    (fun a _ => (fixed a).symm) issue
  refine ⟨μ,basis,?_,rows,perm,?_,first⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then (E.header_eq mem endRoom).1 run machine
  · intro a ha apart
    refine (below a ha).trans ?_
    exact apart.elim (E.literal_before mem) (E.literal_after mem)

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
