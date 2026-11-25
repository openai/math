import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationCall
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationCost
import OAI.Optimization.LinearProgramming.Recovery.InitialPairParity

/-! The first rational LP decision and the physical matrix supplied to every
later support query. The original LP remains readable throughout. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open Matrix RAM RAM.Callable OracleSpec Geometry
open scoped Matrix

structure Result {m d h : ℕ} (solver : NormalSubspace.Spec) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m→ℚ) (E : Matrix (Fin h) (Fin (m+1)) ℚ) (src : ℕ) (native caller : Memory ℚ) : Prop where
  context : SupportBundle.Context E (Principal.ref A b).primal src (Principal.capacity solver m d) caller
  footprint : Footprint (Principal.capacity solver m d-1) (native.atPC 0)
  original : SlackRAM.InputAt caller (PublicInput.sourceBase m d) A b
  source : caller.index 24=PublicInput.sourceBase m d
  rows : caller.index 28=m
  cols : caller.index 29=d
  positiveSource : 256 ≤ src
  afterInput : PublicInput.sourceBase m d+(m*d+m) ≤ src
  height : h ≤ m+1
  kernel : LinearMap.ker E.mulVecLin=(Principal.side A b (Principal.ref A b).primal).denote
  entries : ∀ i j,ratBits (E i j) ≤ InitialPair.sourceWidthPolynomial.eval (m+d+totalBits (lpInput A b))
  nativeSafe : native.AllData (fun z => ratBits z ≤ (width solver).eval (m+d+totalBits (lpInput A b)))
  callerSafe : caller.AllData (fun z => ratBits z ≤ (width solver).eval (m+d+totalBits (lpInput A b)))
  addresses : ∀ j,caller.index j ≤ (finalAddresses solver).eval (m+d)

/-- Stage the true slack tableau, compute and test its complementary bases, and
retain exactly the equations defining the requested side of the alternative. -/
theorem program_run {m d : ℕ} (solver : NormalSubspace.Spec) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) :
    ∃ (h : ℕ) (E : Matrix (Fin h) (Fin (m+1)) ℚ) (src : ℕ) (native caller : Memory ℚ),
      (program solver).Run (fun z => ratBits z ≤ (width solver).eval (m+d+totalBits (lpInput A b)))
        (Odd.memory InitialPair.blank (start [m,d] (lpInput A b)).memory) ((clock solver).eval (m+d))
        (Odd.memory native caller) ∧ Result solver A b E src native caller := by
  let side := (Principal.ref A b).primal
  let W := (width solver).eval (m+d+totalBits (lpInput A b))
  let P := fun z : ℚ => ratBits z ≤ W
  let cap := PairBuilder.capacity (d+1) (m+1) 0
  let prior := pairAddresses.eval (m+d)
  obtain ⟨front,back,k,s,F,R,first,safeFront,safeBack,oldFoot,retained,prepared,_,_,_⟩ :=
    InitialPair.fragment_run A b
  have dims : k+s=m+1 := (Nat.add_comm k s).trans prepared.total
  obtain ⟨widen,_,_⟩ := width_bounds solver A b F R dims
    (table_width prepared.firstTable safeBack) (table_width prepared.lastTable safeBack)
  have startRun : InitialPair.fragment.Run P (Odd.memory InitialPair.blank (start [m,d] (lpInput A b)).memory)
      (InitialPair.fragmentTime m d) (Odd.memory front back) := by
    intro target pc code
    obtain ⟨j,count,exec⟩ := first target pc code
    exact ⟨j,count,exec.weaken (fun _ h i => (h i).trans widen)⟩
  obtain ⟨native,invoked,footprint⟩ := first_call solver A b F R front back safeFront safeBack oldFoot prepared
  let a := back.putIndex 154 side.toNat
  let h := SupportBundle.selectedHeight side k s
  let src := SupportBundle.selectedBase side (InitialPair.layout m d).out k (m+1)
  let E := selected side F R
  have raw : RawTapes back (InitialPair.layout m d).out 208 cap (encodedGramInput F++encodedGramInput R) [k,s] :=
    prepared.tapes
  have table : uniformRect h (m+1) src a=E := by
    ext i j
    exact congrFun (congrFun (selected_table prepared side) i) j
  have afterSafe : a.AllData P := fun i => (safeBack i).trans widen
  have nativeSafe : native.AllData P := fun i => by simpa only [Odd.data_even] using invoked.safe_end (2*i)
  have bound (j : ℕ) : a.index j ≤ prior+1 := by
    by_cases eq : j=154
    · subst j
      have small : side.toNat ≤ 1 := by cases side <;> decide
      simpa [a] using small.trans (by omega : 1 ≤ prior+1)
    · have old := pair_address_bound A b first j
      simpa [a,eq] using old.trans (Nat.le_succ prior)
  obtain ⟨t,q,chooseTime,choose,ctx,data,source,rows,cols⟩ := SupportBundle.select_run
    (Principal.capacityC solver) (Principal.capacityE solver) m d k s (InitialPair.layout m d).out (prior+1)
    side a P E afterSafe table (by simpa [a] using retained.rows) (by simpa [a] using retained.cols)
    (by simpa [a] using raw.scalarBase) (by simpa [a] using prepared.dimensions.1)
    (by simpa [a] using prepared.dimensions.2) (by simp [a]) bound
  have picked := Odd.leaf_run P native nativeSafe choose
  have combine := startRun.seq (invoked.seq picked)
  have full : (program solver).Run P (Odd.memory InitialPair.blank (start [m,d] (lpInput A b)).memory)
      ((clock solver).eval (m+d)) (Odd.memory native t) := by
    apply combine.mono
    exact (Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_left 4 chooseTime)
      (NormalSubspace.callTime solver cap (m+1))) (InitialPair.fragmentTime m d)).trans (clock_bound solver m d)
  have fresh := selected_source m d k side
  have bits := table_width (selected_table prepared side) safeBack
  refine ⟨h,E,src,native,t,full,{
    context := ctx, footprint := footprint, original := original_data data retained.original,
    source := source.trans (by simpa [a] using retained.source),rows := rows, cols := cols,
    positiveSource := fresh.1,afterInput := fresh.2,height := selected_height side prepared.total,
    kernel := selected_kernel prepared side, entries := fun i j => (bits i j).trans (InitialPair.rawWidth_le A b),
    nativeSafe := nativeSafe,callerSafe := choose.safe_end,addresses := final_address_bound solver A b full }⟩

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
