import OAI.Hierarchy.DescentRecordedPaddedMixer
import OAI.Hierarchy.DescentRecordedPaddedFirst
import OAI.Hierarchy.DescentPackedCanvasValues
import OAI.Hierarchy.DescentPackedCanvasRun
import OAI.Hierarchy.DescentEstimatorLiteralIssue

namespace OAI
/-! # Preserve the original packed signed-state channels in the genuine chosen reset basis execution -/

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

theorem input_count (dim : E.dim=reset.reset.k) :
    2^(E.high+E.low)=S.groupCount i*2^k := by
  change 2^E.dim=_
  rw [dim,reset.keyWidth,pow_add,S.group_power ctl.base ctl.radix]

/-- The old census registers and the recorded reset use precisely the same surviving-group digits. -/
theorem same_digits (dim : E.dim=reset.reset.k) :
    PackedFlow.digits (Equiv.refl (Fin (S.groupCount i))) (input_count (reset:=reset) E dim)=
      (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits := by
  apply Equiv.ext
  intro x
  have castValue {a b : ℕ} (h : a=b) (y : Block a) :
      ((Equiv.cast (congrArg Block h)) y).val=y.val := by cases h; rfl
  have groupSize : 2^(S.groupWidth k tail i+k)=S.groupCount i*2^k := by
    rw [pow_add,S.group_power ctl.base ctl.radix]
  change finProdFinEquiv.symm (Fin.cast (input_count (reset:=reset) E dim) x) =
    finProdFinEquiv.symm (Fin.cast groupSize ((Equiv.cast (congrArg Block (dim.trans reset.keyWidth))) x))
  apply congrArg finProdFinEquiv.symm
  exact Fin.ext (castValue (dim.trans reset.keyWidth) x).symm

/-- The physical row in the fixed public rectangle for this specific surviving neighbor. -/
def contactRow (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (e : Contacts (A).mutual) : Fin E.hosts :=
  let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let name:=((A).numberedHeader digits input.vertex).site
  ((PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)) (.inr e)).cast hostCount.symm

theorem contact_total {w} (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (mem : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) mem) (e : Contacts (A).mutual) :
    let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let j:=contactRow E dim maxPorts ports hostCount e
    digit E.precision (ordinal E.low (fun _=>false)).val
        (mem (location E.start E.hosts E.high E.dim+(DescentPackedWalsh.row (u:=E.high) j (fun _=>false)).val)).val=
      ∑x : Bits E.dim,(A).resetFlow digits e.1 e.2.val (address E.dim x) := by
  intro digits j
  rw [first]
  apply Finset.sum_congr rfl
  intro x _
  let name:=((A).numberedHeader digits input.vertex).site
  let loc:=PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
  change (padded loc _ _ (loc (.inr e)) : Bits E.dim → ℕ) x = _
  exact congrFun (padded_at loc _ _ (.inr e)) x

include accepted in
theorem after_canvas_named {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    ∃(prior : Memory w) (μ : Layout E.dim),
      let dst:=E.image (E.literal prior)
      prepare.Exec mem prior t ∧ HEq μ reset.frame.basis ∧
      (prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))).Exec mem dst
        (t+(4+10*(E.staticEnd-E.origin)+E.clock)) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a : Fin (2^E.dim),dst (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val:Word w)) ∧
      PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
        A name digits siteBase peerBase pitch dst ∧
      (∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→dst a=mem a) ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) dst ∧
      ∀v,dst (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w) := by
  intro digits name
  obtain ⟨prior,pre,rect,raw,frame⟩:=primed
  obtain ⟨μ,basis,issued,ctl,tab,keepOld,totals⟩:=accepted.install_padded_mixer_first E dim prior maxPorts ports hostCount
    rect grain old branch live localBits localGain fit stage small score endRoom issue
  refine ⟨prior,μ,pre,basis,Procedure.Exec.then pre issued,ctl,tab,?_,?_,totals,?_⟩
  · apply PackedFlow.Canvas.Originals.keep A name digits siteBase peerBase pitch prior _ raw _ width
    intro z hit
    rcases hit with h|h
    · exact keepOld z (h.2.trans_le siteEnd) (by rcases siteSave with left|right <;> omega)
    · exact keepOld z (h.2.trans_le peerEnd) (by rcases peerSave with left|right <;> omega)
  · intro z h ok
    exact (keepOld z (lt_min_iff.mp h).2 ok).trans (frame z (lt_min_iff.mp h).1)
  · intro v
    have host : (name v).val<S.hostSize i:=(name v).isLt.trans_le input.valid.host
    have liveRow : (name v).val*(E.dim+1)<E.hosts := by
      rw [hostCount]
      exact (Nat.mul_lt_mul_of_pos_right host (Nat.succ_pos _)).trans_le
        (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    have inside:=Nat.add_lt_add_left (liveRow.trans_le fit.hostRows.1) E.depthRows.base
    rw [keepOld _ (inside.trans_le fit.depth.2.2) (by rcases fit.depthAway with left|right <;> omega)]
    exact PackedFlow.Canvas.Loaded.own_depth A name digits input.valid.host (input.branch.le.trans ports)
      f K E.depthRows.base E.gainRows.base E.start prior rect v

include accepted in
theorem after_canvas {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    ∃(μ : Layout E.dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      (prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))).Exec mem dst
        (t+(4+10*(E.staticEnd-E.origin)+E.clock)) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a : Fin (2^E.dim),dst (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val:Word w)) ∧
      PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
        A name digits siteBase peerBase pitch dst ∧
      ∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→dst a=mem a := by
  intro digits name
  obtain ⟨prior,μ,_,basis,ran,rows,table,orig,frame,_,_⟩:=accepted.after_canvas_named E dim mem prepare t
    maxPorts ports hostCount siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed
    grain old branch live localBits localGain fit stage small score endRoom issue
  exact ⟨μ,E.image (E.literal prior),basis,ran,rows,table,orig,frame⟩

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
