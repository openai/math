import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentResetNativeBasis
import OAI.Hierarchy.DescentPackedResetRectangle

namespace OAI
/-! # The measured basis of the selected reset on the original packed input words -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem withHosts (E : EstimatorArena) {N : ℕ} (h : E.hosts=N) :
    {E with hosts:=N}=E := by subst N; cases E; rfl

private theorem numbered_width {F P J V : Type} [Field F] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d k m m' : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (width : m'=m) (digits : Block m≃J×Block k)
    (v : V↪Fin (Fintype.card V)) (f K : ℕ) :
    let old := A.numberedHeader digits v
    let new := A.numberedHeader ((Equiv.cast (congrArg Block width)).trans digits) v
    HEq (new.chosenBasis A f K) (old.chosenBasis A f K) ∧ new.depth A f=old.depth A f := by
  subst m'
  exact ⟨HEq.rfl,rfl⟩

namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "lanes" => owners*(E.dim+1)+owners*(A).degree
local notation "full" => (A).wire*((A).z*G.b)*(A).cap

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
include accepted in
/-- The packed depth and gain rows are read on the same memory that holds
the reset's measured site and contact rectangle. Its row and permutation
outputs identify the basis retained by the selected chronological frame. -/
theorem mixer_run {w : ℕ} (dim : E.dim=reset.reset.k) (hosts : E.hosts=lanes)
    (base : ℕ) (mem : Memory w)
    (depthPage : E.depthRows.base=base+lanes) (gainPage : E.gainRows.base=base+2*lanes)
    (rect :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let H := (A).numberedHeader digits input.vertex
      PackedFlow.InstalledRectangle (u:=E.high) (l:=E.low) (b:=E.precision)
        A H.site digits f K base E.start mem)
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
      ∀a<E.start,E.image mem a=mem a := by
  let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let H := (A).numberedHeader digits input.vertex
  let U : EstimatorArena := {E with hosts:=lanes}
  have same : U=E := withHosts E hosts
  have startEq : U.start=E.start := congrArg EstimatorArena.start same
  have solveEq : U.solveAt=E.solveAt := congrArg EstimatorArena.solveAt same
  have transported := numbered_width A (dim.trans reset.keyWidth) sourceDigits input.vertex f K
  have depths (v : input.V) : H.depth A f v≤E.dim := by
    rw [congrFun transported.2 v,←accepted.measured.depth v,dim]
    exact reset.reset.placement.depth _
  let loc := portRow (k:=E.dim) H.site (A).mutual
    (fun v=>(Finset.card_filter_le _ _).trans ((A).degreeBound v)) (H.depth A f)
  have run := (A).mixer_basis S U digits H p f K loc mem mem input.valid ctl.height reset.age.le
    (input.grain.trans grain) (input.edges.trans old) branch live depths localBits localGain
    (by simpa only [same] using fit) stage small (by simpa only [same] using score)
    (by simpa only [same] using fixed)
    (by
      rw [startEq]
      exact rect.input) (fun v => by rw [show U.depthRows.base=base+lanes from depthPage]; exact rect.levels v)
    (fun v => by rw [show U.gainRows.base=base+2*lanes from gainPage]; exact rect.gains v)
    (by simpa only [same] using issue)
  refine ⟨H.chosenBasis A f K,transported.1.trans (heq_of_eq accepted.measured.basis.symm),?_⟩
  obtain ⟨exec,rows,permutation,frame⟩ := run
  have imageEq : U.image mem=E.image mem := congrArg (fun arena : EstimatorArena => arena.image mem) same
  refine ⟨?_,?_,?_,?_⟩
  · rw [←same]
    exact @exec
  · intro a
    have measured := rows a
    rw [imageEq,solveEq] at measured
    exact measured
  · intro a
    have measured := permutation a
    rw [imageEq,solveEq] at measured
    exact measured
  · intro a ha
    have preserved := frame a (startEq.symm ▸ ha)
    rw [imageEq] at preserved
    exact preserved

include accepted in
/-- The selected basis also runs with a public host capacity. Each real signed
site level and contact occupies its assigned row. The remaining rows contribute
zero to the measured numerator. -/
theorem mixer_run_from_rows_first {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (fixed : ∀a<E.start,mem a=E.literal mem a)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let H := (A).numberedHeader digits input.vertex
    let depth := H.depth A f
    let levels := inputLevels (k:=E.dim) depth
    let siteLoad := fun (v : input.V) (x : DescentGL.Bits E.dim) =>
      (A).resetLoad digits v (DescentColonies.address E.dim x)
    let edgeLoad := fun (c : Contacts (A).mutual) (x : DescentGL.Bits E.dim) =>
      (A).resetFlow digits c.1 c.2.val (DescentColonies.address E.dim x)
    ∀ (loc : DescentMeasuredWeights.Item levels (Contacts (A).mutual) ↪ Fin E.hosts),
      Installed E.start (fun v => shaped (fun a => (asCube
        (padded loc (load levels siteLoad edgeLoad) (fun _=>0) v) a : Cell E.precision))) mem →
      (∀v,mem (E.depthRows.base+v.val)=((padded loc
        (level levels (inputDepth depth) (pairDepth (A).mutual depth)) 0 v : ℕ) : Word w)) →
      (∀v,mem (E.gainRows.base+v.val)=((padded loc
        (gain levels f full K) 0 v : ℕ) : Word w)) →
    ∃ μ : Layout E.dim, HEq μ reset.frame.basis ∧
      (E.cpu w).Exec mem (E.image mem) E.clock ∧
      (∀a : Fin E.dim,E.image mem (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val : Word w)) ∧
      (∀a : Fin (2^E.dim),E.image mem (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val : Word w)) ∧
      (∀a<E.start,E.image mem a=mem a) ∧
      E.FirstTotals (padded loc (load levels siteLoad edgeLoad) (fun _=>0)) (E.image mem) := by
  intro digits H depth levels siteLoad edgeLoad loc loads levelPin gainPin
  have transported := numbered_width A (dim.trans reset.keyWidth) sourceDigits input.vertex f K
  have depths (v : input.V) : depth v≤E.dim := by
    change H.depth A f v≤E.dim
    rw [congrFun transported.2 v,←accepted.measured.depth v,dim]
    exact reset.reset.placement.depth _
  refine ⟨H.chosenBasis A f K,transported.1.trans (heq_of_eq accepted.measured.basis.symm),?_⟩
  exact (A).mixer_basis_first S E digits H p f K loc mem mem input.valid ctl.height reset.age.le
    (input.grain.trans grain) (input.edges.trans old) branch live depths localBits localGain fit
    stage small score fixed loads levelPin gainPin issue

include accepted in
theorem mixer_run_from_rows {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (fixed : ∀a<E.start,mem a=E.literal mem a)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let H := (A).numberedHeader digits input.vertex
    let depth := H.depth A f
    let levels := inputLevels (k:=E.dim) depth
    let siteLoad := fun (v : input.V) (x : DescentGL.Bits E.dim) =>
      (A).resetLoad digits v (DescentColonies.address E.dim x)
    let edgeLoad := fun (c : Contacts (A).mutual) (x : DescentGL.Bits E.dim) =>
      (A).resetFlow digits c.1 c.2.val (DescentColonies.address E.dim x)
    ∀ (loc : DescentMeasuredWeights.Item levels (Contacts (A).mutual) ↪ Fin E.hosts),
      Installed E.start (fun v => shaped (fun a => (asCube
        (padded loc (load levels siteLoad edgeLoad) (fun _=>0) v) a : Cell E.precision))) mem →
      (∀v,mem (E.depthRows.base+v.val)=((padded loc
        (level levels (inputDepth depth) (pairDepth (A).mutual depth)) 0 v : ℕ) : Word w)) →
      (∀v,mem (E.gainRows.base+v.val)=((padded loc
        (gain levels f full K) 0 v : ℕ) : Word w)) →
    ∃ μ : Layout E.dim, HEq μ reset.frame.basis ∧
      (E.cpu w).Exec mem (E.image mem) E.clock ∧
      (∀a : Fin E.dim,E.image mem (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val : Word w)) ∧
      (∀a : Fin (2^E.dim),E.image mem (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val : Word w)) ∧
      ∀a<E.start,E.image mem a=mem a := by
  intro digits H depth levels siteLoad edgeLoad loc words cuts gains
  obtain ⟨μ,basis,run,rows,perm,framed,_⟩ := accepted.mixer_run_from_rows_first E dim mem grain old
    branch live localBits localGain fit stage small score fixed issue loc words cuts gains
  exact ⟨μ,basis,run,rows,perm,framed⟩


end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
