import OAI.Computability.VPVNP.RankCoordinateColumn
import OAI.Computability.VPVNP.RankCoordinateOrdinalABI
import OAI.Computability.VPVNP.RankPrefixRead
import OAI.Computability.VPVNP.RankPrefixTemplate
import OAI.Computability.VPVNP.RankPrefixWorkspace
import OAI.Computability.VPVNP.RankQueryGramExecution

/-! # Computing greedy row and column indices from a streamed matrix

At each prefix the five-word controller starts the complete physical rank
scan in private workspace. All matrix-entry requests address the original
matrix. For a column query the two address ports of its reader are
interchanged. Both routines return the original selected index.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.Select

open RAMTape BurstRAM Dispatch UniversalCountStack Cursor PrefixWorkspace

variable {K : Type} [Fintype K] [DecidableEq K]

/-- Compare prefix-rank stack addresses using the port labels of the Gram scan. -/
local instance : DecidableEq (PrefixPort K) :=
  inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))

/-- Decide equality of addresses in the template, working copy, and scratch stack of a
prefix-rank call. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) :=
  fun a b => PrefixWorkspace.instDecidableEqAux a b

/-- Cursor argument register containing the rank returned by the Gram scan. -/
def rankResult : PrefixPort K := .cursor (.isa (.reg (Registers.arg 1)))

/-- Compute the rank of the current row prefix by passing its length to the Gram routine and
reading its result register. -/
def prefixRank (read : FiniteRoutine (MacaulayRead.Port K)) :=
  rankCall prefixDynamic (gramRank read) rankResult

/-- Scan row prefixes for the rank increase that identifies the requested greedy basis row. -/
def rows (read : FiniteRoutine (MacaulayRead.Port K)) := PrefixWords.machine (prefixRank read)

/-- Apply the greedy row scan to the transpose reader to find the requested original column
index. -/
def columns (read : FiniteRoutine (MacaulayRead.Port K)) := rows (MacaulayRead.transpose read)

/-- Maximum stack length needed for either the initial prefix template or the running Gram
scan. -/
def workCap (d w v e A S : ℕ) := max (w+v+e+e*v+A+1) (gramSpace d w v e A S)

/-- Step bound for copying the prefix template, computing one rank, and returning the result. -/
def timePerRank (K : Type) [Fintype K] (d w v e B A S : ℕ) :=
  let M := workCap d w v e A S
  copyClock (PrefixPort K) M + gramTime d w v e B + returnClock (PrefixPort K) w M

/-- Step bound for testing up to `n` prefixes, including rank calls and updates to the
controller words. -/
def scanTime (K : Type) [Fintype K] (n d w v e B A S : ℕ) :=
  n*((PrefixWords.arithmeticBound w+timePerRank K d w v e B A S+(20*w+10))+1+PrefixWords.arithmeticBound w)

/-- Maximum stack length over the prefix controller's arithmetic and its private rank calls. -/
def scanSpace (K : Type) [Fintype K] (d w v e A S : ℕ) :=
  max (w+PrefixWords.arithmeticBound w) (callSpace (PrefixPort K) w (workCap d w v e A S))

variable {p e n m d w v B A S : ℕ} {c : SliceArithmetic.Vector p e}

/-- Initialize the reusable rank template with zero rows and `m` columns, leaving the working
copy and scratch stack empty. -/
def side (w v m : ℕ) (c : SliceArithmetic.Vector p e) (base : Stacks K) :=
  auxBank (prefixRawBank w v 0 m c base) (fun _ => [])

private theorem workCap_width : w ≤ workCap d w v e A S :=
  (show w ≤ w+v+e+e*v+A+1 by omega).trans (le_max_left ..)

private theorem width_le {d w : ℕ} (hw : gramWidth d ≤ w) : d ≤ w := by
  have h := Nat.le_mul_of_pos_right (2*d+7) (Nat.succ_pos (max widthFactor control.wordFactor))
  change 2*d+7 ≤ (2*d+7)*(max widthFactor control.wordFactor+1) at h
  unfold gramWidth at hw
  omega

private theorem set_result (j k a b r : ℕ) : Function.update (PrefixWords.words (w := w) j k a b) 3 (Fin.ofNat _ r) =
    PrefixWords.words j k r b := by funext i; fin_cases i <;> rfl

theorem side_length {ready : Stacks K → Prop} (c : SliceArithmetic.Vector p e) (base : Stacks K)
    (hr : ready base) (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A) (hm : m < 2^w)
    (i : PrefixWorkspace.Aux (PrefixPort K)) : (side w v m c base i).length ≤ scanSpace K d w v e A S := by
  cases i with
  | template h =>
    apply (prefixRawBank_length c base hr ha (Nat.two_pow_pos w) hm h).trans
    exact (le_max_left ..).trans ((Nat.le_add_right (workCap d w v e A S) _).trans (le_max_right ..))
  | work h | scratch => exact Nat.zero_le _

private theorem rankAt_zero {F : Type*} [Field F] [DecidableEq F] (L : Matrix (Fin n) (Fin m) F) :
    PrefixWords.rankAt L 0 = 0 := by
  rw [PrefixWords.rankAt_eq _ (Nat.zero_le n), rankQuery_eq]
  have h := (prefixRows L 0 (Nat.zero_le n)).rank_le_card_height
  simpa only [Fintype.card_fin, Nat.le_zero] using h

variable [Fact p.Prime] [NeZero e] [Fact (Irreducible (SliceArithmetic.modulus c))]
    [DecidableEq (AdjoinRoot (SliceArithmetic.modulus c))]

/-- The rank subroutine called by the greedy controller. The incoming
prefix register determines every dynamic dimension in the two nested scans. -/
theorem prefixRank_runs (M : Matrix (Fin n) (Fin m) (Scalar c))
    (read : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop}
    (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hsize : n+n+(n+m)*n+m+8 < 2^d) (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : ready base) (j k old : ℕ) (hj : j < n) :
    ∃ t ≤ timePerRank K d w v e B A S, (prefixRank read).BoundedRun (scanSpace K d w v e A S) t
      (PrefixWords.bank (side w v m c base) (PrefixWords.words (w := w) j k old (j+1)))
      (PrefixWords.bank (side w v m c base) (PrefixWords.words (w := w) j k
        (PrefixWords.rankAt (M.map (Scalar.interpretation c)) (j+1)) (j+1))) := by
  let R := (prefixRows (M.map (Scalar.interpretation c)) (j+1) hj).rank
  let rs := PrefixWords.words (w := w) j k old (j+1)
  let template := prefixRawBank w v 0 m c base
  let cap := workCap d w v e A S
  have hm : m < 2^w := (show m < 2^d by omega).trans_le (Nat.pow_le_pow_right (by decide) (width_le hw))
  have ht (h : PrefixPort K) : (template h).length ≤ cap :=
    (prefixRawBank_length c base hr ha (Nat.two_pow_pos w) hm h).trans (le_max_left ..)
  obtain ⟨t,bt,out,aux,_,hout,run⟩ := gramRank_bounded (prefixRows M (j+1) hj) read (hc.prefixMatrix _ hj)
    ha hj hsize hw hv base hr
  have hraw : prepared prefixDynamic template rs = rawGram w v (j+1) m c base := by
    funext h
    change (if prefixDynamic h then digits w (j+1) else template h) = prefixRawBank w v (j+1) m c base h
    exact (prefixRawBank_eq w v (j+1) m c base h).symm
  let final := scanBank (j+1) (0 : Word w) out [] (idle aux)
  have hresult : (out (Registers.arg 1)).val = R := hout 1 (by decide)
  have hword : out (Registers.arg 1) = Fin.ofNat (2^w) R := by
    apply Fin.ext
    exact hresult.trans (Nat.mod_eq_of_lt (hresult ▸ (out (Registers.arg 1)).isLt)).symm
  have hread : final rankResult = wordBits (Fin.ofNat (2^w) R) := congrArg wordBits hword
  have framed := rankCall_bounded prefixDynamic (gramRank read) rankResult template final rs
    (Fin.ofNat (2^w) R) cap t workCap_width ht (hraw.symm ▸ run.enlarge (le_max_right ..)) hread
  obtain ⟨s,hs,hret⟩ := framed
  have update : Function.update rs 3 (Fin.ofNat _ R) = PrefixWords.words j k R (j+1) := set_result ..
  rw [update] at hret
  refine ⟨s,hs.trans (Nat.add_le_add_right (Nat.add_le_add_left bt _) _),?_⟩
  rw [PrefixWords.rankAt_eq _ hj, rankQuery_eq]
  exact hret.enlarge (le_max_right ..)

/-- Complete physical row selection, including all prefix rank and scalar
entry requests, with a reusable private workspace. -/
theorem row_runs (M : Matrix (Fin n) (Fin m) (Scalar c)) (read : FiniteRoutine (MacaulayRead.Port K))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hsize : n+n+(n+m)*n+m+8 < 2^d) (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : ready base) (k : Fin (rankQuery (M.map (Scalar.interpretation c)))) :
    let L := M.map (Scalar.interpretation c)
    let found := (greedyRowIndex L k).val
    ∃ t ≤ scanTime K n d w v e B A S, (rows read).BoundedRun (scanSpace K d w v e A S) t
      (PrefixWords.bank (side w v m c base) (PrefixWords.words (w := w) 0 k.val (PrefixWords.rankAt L 0) 0))
      (PrefixWords.bank (side w v m c base) (PrefixWords.words (w := w) found k.val (PrefixWords.rankAt L (found+1)) (found+1))) := by
  have hdw : 2^d ≤ 2^w := Nat.pow_le_pow_right (by decide) (width_le hw)
  have hn : n < 2^w := by omega
  have hm : m < 2^w := by omega
  apply PrefixWords.machine_runs _ k _ (prefixRank read) hn _ (le_max_left ..)
  · intro j hj
    exact prefixRank_runs M read hc ha hsize hw hv base hr j k _ hj
  · exact side_length c base hr ha hm

/-- The transpose scan returns the columns chosen for the square Cramer
minor of the original matrix. -/
theorem column_runs (M : Matrix (Fin n) (Fin m) (Scalar c)) (read : FiniteRoutine (MacaulayRead.Port K))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hsize : m+m+(m+n)*m+n+8 < 2^d) (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : ready base) (k : Fin (rankQuery (M.map (Scalar.interpretation c)))) :
    let L := M.map (Scalar.interpretation c)
    let found := (coordinateColumns (greedyRowBasis L) (greedyRowBasis_fullRank L) k).val
    ∃ t ≤ scanTime K m d w v e B A S, (columns read).BoundedRun (scanSpace K d w v e A S) t
      (PrefixWords.bank (side w v n c base) (PrefixWords.words (w := w) 0 k.val (PrefixWords.rankAt L.transpose 0) 0))
      (PrefixWords.bank (side w v n c base) (PrefixWords.words (w := w) found k.val (PrefixWords.rankAt L.transpose (found+1)) (found+1))) := by
  dsimp only
  rw [coordinateColumns_greedyRowBasis]
  exact row_runs M.transpose (MacaulayRead.transpose read) hc.transpose ha hsize hw hv base hr
    (Fin.cast (by rw [rankQuery_eq, rankQuery_eq]; exact (Matrix.rank_transpose _).symm) k)

/-- Native ordinal reader for greedy rows of the streamed matrix. Its
private work template is restored on every return. -/
theorem row_correctSpace (M : Matrix (Fin n) (Fin m) (Scalar c)) (read : FiniteRoutine (MacaulayRead.Port K))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hsize : n+n+(n+m)*n+m+8 < 2^d) (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : ready base) :
    OrdinalRead.CorrectSpace (OrdinalABI.machine (rows read)) (greedyRowIndex (M.map (Scalar.interpretation c)))
      w (scanTime K n d w v e B A S+OrdinalABI.overhead w) (scanSpace K d w v e A S+OrdinalABI.overhead w)
      (· = OrdinalABI.idle (w := w) (side w v m c base)) := by
  have hm : m < 2^w := (show m < 2^d by omega).trans_le (Nat.pow_le_pow_right (by decide) (width_le hw))
  apply OrdinalABI.correctSpace _ _ _ (side_length c base hr ha hm) ((Nat.le_add_right _ _).trans (le_max_left ..))
  intro i
  obtain ⟨t,bt,run⟩ := row_runs M read hc ha hsize hw hv base hr i
  rw [rankAt_zero] at run
  exact ⟨t,bt,_,_,run⟩

/-- Native ordinal reader for the selected columns of the square Cramer minor. -/
theorem column_correctSpace (M : Matrix (Fin n) (Fin m) (Scalar c)) (read : FiniteRoutine (MacaulayRead.Port K))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hsize : m+m+(m+n)*m+n+8 < 2^d) (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : ready base) :
    let L := M.map (Scalar.interpretation c)
    OrdinalRead.CorrectSpace (OrdinalABI.machine (columns read))
      (coordinateColumns (greedyRowBasis L) (greedyRowBasis_fullRank L))
      w (scanTime K m d w v e B A S+OrdinalABI.overhead w) (scanSpace K d w v e A S+OrdinalABI.overhead w)
      (· = OrdinalABI.idle (w := w) (side w v n c base)) := by
  have hn : n < 2^w := (show n < 2^d by omega).trans_le (Nat.pow_le_pow_right (by decide) (width_le hw))
  apply OrdinalABI.correctSpace _ _ _ (side_length c base hr ha hn) ((Nat.le_add_right _ _).trans (le_max_left ..))
  intro i
  obtain ⟨t,bt,run⟩ := column_runs M read hc ha hsize hw hv base hr i
  rw [rankAt_zero] at run
  exact ⟨t,bt,_,_,run⟩

end RankQuery.Stack.Coordinate.Select

end

end VPVNP
end Computability
end OAI
