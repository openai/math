import OAI.Optimization.LinearProgramming.Compression.RequestGraphGrid
import OAI.Optimization.LinearProgramming.Lattice.BitProbeDyadic
import OAI.Optimization.LinearProgramming.Lattice.BitDriverWire

/-! The existing signed binary bisection engine can start directly at one residual
row. It returns the unique normalized midpoint used to finish the graph request. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit

abbrev ProbeParams := Driver.Probe.Params

def probeParams (x : GridArg) : ProbeParams := ((x.2.length+1,gridDepth x),[])

def startProbe (x : GridArg) : Driver.Probe.Action :=
  let rows := gridRows x
  Driver.Probe.nextRow (probeParams x,rows.2) [rows.1] []

theorem startProbe_runs {n : ℕ} (q : ℕ) (z : Fin (n+1) → ℤ)
    (O : List ℤ → Bool) (o : (Fin ((n+1)+1) → ℤ) → Bool) (ho : ∀ a, O (List.ofFn a)=o a) :
    let x : GridArg := (q,List.ofFn z)
    let rs := requestDyadicRows z (Fin.last n) q (gridLower x) (gridWidth x)
    let ys := Driver.Probe.queryRows o (dyadicSearchQ rs.1 rs.2 (gridDepth x))
    let y := Driver.Probe.coordinate o rs.1 rs.2 (gridDepth x)
    Driver.Probe.Runs O (startProbe x) ys (true,[y]) := by
  intro x rs ys y
  have hdepth : 0 < (probeParams x).1.2 := Nat.zero_lt_succ _
  have hr := Driver.Probe.ratio_prefix O o ho rs.1 rs.2 (probeParams x) [] [] hdepth
  have hf := hr.finish (Driver.Probe.Runs.done (true,[y]))
  have hrows : gridRows x = (List.ofFn rs.1,List.ofFn rs.2) := gridRows_pack q z
  simpa only [ys,startProbe,hrows,probeParams,List.append_nil] using hf

@[simp] theorem gridDepth_pack {n : ℕ} (q : ℕ) (z : Fin (n+1) → ℤ) :
    gridDepth (q,List.ofFn z) = (2*requestCutoff (n+1)*q).log2+1 := by
  simp [gridDepth,orderSize,Nat.mul_assoc]

@[simp] theorem gridLower_pack {n : ℕ} (q : ℕ) (z : Fin (n+1) → ℤ) :
    gridLower (q,List.ofFn z) = -(requestCutoff (n+1)*q : ℤ) := by
  simp [gridLower,orderSize]

theorem graphOffset_eq_requestGrid {n : ℕ} (v : Fin (n+1) → ℝ)
    (neg : (Fin (n+1) → ℤ) → ℤ → Bool) (hn : ∀ a c, neg a c = true ↔ requestForm v a+c<0)
    (z : Fin (n+1) → ℤ) (hz : z (Fin.last n)≠0) (q : ℕ)
    (hr : |requestForm v z/(z (Fin.last n):ℝ)|≤requestCutoff (n+1)) :
    let x : GridArg := (q,List.ofFn z)
    let rs := requestDyadicRows z (Fin.last n) q (gridLower x) (gridWidth x)
    let y := Driver.Probe.coordinate (affineCommitReply neg) rs.1 rs.2 (gridDepth x)
    gridOffset x y = ((requestGridRun neg z (Fin.last n) q (requestCutoff (n+1))).1 : ℚ)/q := by
  intro x rs y
  have hv :  ((gridWidth x : ℕ) : ℚ) = (2:ℚ)^(gridDepth x) := by simp [gridWidth]
  have y_eq : y = (((dyadicSearch (affineCommitReply neg) rs.1 rs.2 (gridDepth x)).numerator : ℤ):ℚ) /
      (gridWidth x : ℚ) := by
    simp only [y,Driver.Probe.coordinate,dyadicSearchQ_run,hv]
  rw [y_eq,gridOffset_of_midpoint]
  have h := requestGridRun_eq_dyadicSearch v neg hn z (Fin.last n) hz q (requestCutoff (n+1)) hr
  have hd : gridDepth x = (2*requestCutoff (n+1)*q).log2+1 := gridDepth_pack q z
  have hl : gridLower x = -(requestCutoff (n+1)*q : ℤ) := gridLower_pack q z
  have hw : (gridWidth x : ℤ) = (2:ℤ)^((2*requestCutoff (n+1)*q).log2+1) := by
    simp [gridWidth,hd]
  apply congrArg (fun m : ℤ => (m:ℚ)/(q:ℚ))
  simpa only [rs,hd,hl,hw] using h.symm

/-- The native reference service uses the homogeneous public word format. Its
second comparison distinguishes zero from positive. The bisection takes the
upper half on either outcome. -/
def referenceOrder {d : ℕ} (neg : (Fin d → ℤ) → ℤ → Bool) (a : Fin (d+1) → ℤ) : Ordering :=
  if affineCommitReply neg a then
    if affineCommitReply neg (fun i => -a i) then .eq else .gt
  else .lt

theorem referenceOrder_exact {d : ℕ} (v : Fin d → ℝ) (neg : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ z c, neg z c=true ↔ requestForm v z+c<0) (a : Fin (d+1) → ℤ) :
    let t := formValue a (Fin.snoc v 1)
    referenceOrder neg a = if t<0 then .lt else if t=0 then .eq else .gt := by
  intro t
  have hpos : affineCommitReply neg a=true ↔ 0≤t := affineCommitReply_correct v neg ho a
  have hneg := affineCommitReply_correct v neg ho (fun i => -a i)
  have he : formValue (fun i => -a i) (Fin.snoc v 1) = -t := by
    simp [t,formValue,Finset.sum_neg_distrib]
  rw [he] at hneg
  rcases lt_trichotomy t 0 with h | h | h
  · have ha := Bool.eq_false_iff.mpr (fun hu => (not_le_of_gt h) (hpos.mp hu))
    simp [referenceOrder,ha,h]
  · have ha := hpos.mpr h.ge
    have hb := hneg.mpr (by linarith)
    simp [referenceOrder,ha,hb,h]
  · have ha := hpos.mpr h.le
    have hb := Bool.eq_false_iff.mpr (fun hu => (not_le_of_gt (neg_neg_of_pos h)) (hneg.mp hu))
    simp [referenceOrder,ha,hb,not_lt.mpr h.le,ne_of_gt h]

theorem reference_reply {d : ℕ} (neg : (Fin d → ℤ) → ℤ → Bool) (h : Transcript)
    (a : Fin (d+1) → ℤ) :
    Driver.nonnegativeAnswer (wordSignOracle (referenceOrder neg) h (signRowWord a)) =
      affineCommitReply neg a ∧
    (wordSignOracle (referenceOrder neg) h (signRowWord a)).length≤2 := by
  simp only [wordSignOracle_query]
  refine ⟨?_,(signReply_length _).le⟩
  rw [Driver.nonnegativeAnswer_sign]
  unfold referenceOrder
  cases affineCommitReply neg a <;> cases affineCommitReply neg (fun i => -a i) <;> rfl

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
