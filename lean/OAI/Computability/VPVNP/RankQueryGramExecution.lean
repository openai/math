import OAI.Computability.VPVNP.RankQueryBoundedExecution
import OAI.Computability.VPVNP.RankCursorDimensions
import OAI.Computability.VPVNP.RankQueryStackGramRoot

/-!
# Rectangular rank on a streamed relation matrix

From the binary row and column dimensions the machine constructs both scan
bounds. It invokes the concrete Schur, weighted Gram, and field arithmetic
controls. The remaining matrix-specific operation is a bounded read of one
scalar entry. A single time budget and a separate stack-height budget cover
every row prefix satisfying the same numerical size bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

/-- Sufficient binary width for the decision trees of both the Schur
interpreter and the outer degree scan. -/
def gramWidth (d : ℕ) := (2*d+7)*(max widthFactor control.wordFactor + 1)+3

private theorem width_conditions {d w : ℕ} (h : gramWidth d ≤ w) :
    3 ≤ w ∧ d ≤ w ∧ 2*d+6 ≤ w ∧ (d+1)*widthFactor ≤ w ∧
      (2*d+6+1)*widthFactor ≤ w ∧ (d+1)*control.wordFactor ≤ w := by
  let b := max widthFactor control.wordFactor + 1
  have h₁ : 2*d+7 ≤ (2*d+7)*b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h₂ : (2*d+7)*widthFactor ≤ (2*d+7)*b :=
    Nat.mul_le_mul_left _ ((le_max_left ..).trans (Nat.le_succ _))
  have h₃ : (d+1)*control.wordFactor ≤ (2*d+7)*b :=
    Nat.mul_le_mul (by omega) ((le_max_right ..).trans (Nat.le_succ _))
  have h₄ : (d+1)*widthFactor ≤ (2*d+7)*widthFactor := Nat.mul_le_mul_right _ (by omega)
  change (2*d+7)*b+3 ≤ w at h
  rw [show 2*d+6+1 = 2*d+7 by omega]
  omega

/-- A root clock that depends on the common bit bound for the entire matrix
and therefore applies to each smaller prefix. -/
private def queryAllowance (d w v e B : ℕ) :=
  loadClock w + (2^((2*d+8)*(2*d+5)) *
    Engine.boundedStepTime (DescribeAdapter.clock w v e B) (Engine.Assembly.localBudget w e v) w v e + 1)

/-- Uniform step bound for the streamed Gram rank routine with a common `d`-bit size bound. It
charges initialization and up to `(2^d + 1)^2` coefficient queries and cursor checks using
the entry-read time bound `B`. -/
def gramTime (d w v e B : ℕ) :=
  startupClock w + ((2^d+1)*(2^d+1)*(queryAllowance d w v e B + checkClock w v e + 1)+2)

/-- Every prefix may reuse the same storage. The cap of the individual
entry reader enters this expression independently of its clock. -/
def gramSpace (d w v e A S : ℕ) :=
  let a := w+v+e+e*v+A
  let b := Engine.Assembly.localBudget w e v
  let ds := GramEngine.descriptorSpace w v e A S (2*d+4)
  max (startupSpace a w 1)
    (outerRankSpace (max (max w a + loadClock w) (Engine.boundedSpace ds a (2*d+4) b w v e)) a w v e)

variable {K : Type} [DecidableEq K]

/-- An entry-point shared by all matrix shapes and every width. -/
def gramRank (read : FiniteRoutine (MacaulayRead.Port K)) : FiniteRoutine (ScanPort (GramEngine.Aux K)) :=
  initializeDimensions.followedBy (fullRank (GramEngine.actions read))

variable {p e : ℕ} {c : SliceArithmetic.Vector p e}

/-- The input includes the two matrix dimensions, the field advice and the
entry reader's own state. The Schur-depth stack starts empty. -/
def rawGram (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (reader : Stacks K) :
    Stacks (ScanPort (GramEngine.Aux K)) :=
  Function.update (scanBank n (0 : Word w) (dimensionRegs w n m) [true]
    (idle (GramEngine.initial w v n m c reader))) .depth []

variable [Fact p.Prime] [NeZero e] [Fact (Irreducible (SliceArithmetic.modulus c))]

/-- The rank of a streamed rectangular matrix is in cursor register one on
return. Both displayed resource bounds are uniform over all row counts up
to `N`; the instruction table depends only on the supplied entry routine. -/
theorem gramRank_bounded {n N m d w v B A S : ℕ} (M : Matrix (Fin n) (Fin m) (Scalar c))
    (read : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop}
    (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (hn : n ≤ N) (hsize : N+N+(N+m)*N+m+8 < 2^d) (hw : gramWidth d ≤ w)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (reader : Stacks K) (hr : ready reader) :
    ∃ t ≤ gramTime d w v e B, ∃ out aux, GramEngine.Ready w v n m c ready aux ∧
      Registers.Stores out ((n+m)*n) (M.map (Scalar.interpretation c)).rank 0 ∧
      (gramRank read).BoundedRun (gramSpace d w v e A S) t (rawGram w v n m c reader)
        (scanBank n (0 : Word w) out [] (idle aux)) := by
  let Z := (n+m)*n
  let a := w+v+e+e*v+A
  let b := Engine.Assembly.localBudget w e v
  let desc := DescribeAdapter.clock w v e B
  let ds := GramEngine.descriptorSpace w v e A S (2*d+4)
  let initial := GramEngine.initial w v n m c reader
  have hZ : Z ≤ (N+m)*N := Nat.mul_le_mul (Nat.add_le_add_right hn _) hn
  have hlocal : n+n+Z+m+8 < 2^d := by omega
  have hn' : n ≤ 2^d := by omega
  have hz' : Z ≤ 2^d := by omega
  obtain ⟨hw₃,hd,hs,hw₁,hw₂,hwc⟩ := width_conditions hw
  have hdw : 2^d ≤ 2^w := Nat.pow_le_pow_right (by decide) hd
  have hready : GramEngine.Ready w v n m c ready initial :=
    GramEngine.initial_ready reader hr (by omega) (by omega)
  have haux : ∀ x, GramEngine.Ready w v n m c ready x → ∀ i, (x i).length ≤ a :=
    fun _ h => GramEngine.ready_length h ha
  have hwork (k : Engine.Port (GramEngine.Aux K)) : (idle initial k).length ≤ a := by
    cases k with
    | aux i => exact haux initial hready i
    | result | condition => exact Nat.zero_le _
    | frame f => cases f <;> exact Nat.zero_le _
  obtain ⟨t₁,h₁,start⟩ := initialize_bounded n m (by omega : n < 2^w) (0 : Word w)
    [true] (idle initial) hwork
  have spec := GramEngine.contracts (U := n) (Z := Z) read M hc.correct hv hw₃ hw₁ hd hlocal d hn' hn' hz' hs hw₂
  have hdesc := GramEngine.describeBounded (U := n) (Z := Z) (depth := 2*d+4) read M hc ha hv hw₃ hw₁ hd hlocal
  have hdepth : Nat.clog 2 n+4+Nat.clog 2 n ≤ 2*d+4 := by
    have h := Nat.clog_le_of_le_pow hn'
    omega
  have hscan : max 1 (max n Z) < 2^d := by omega
  have hregs := startRegs_stores n m (by omega : n+m < 2^w) (by omega : (n+m)*n < 2^w)
  obtain ⟨t₂,h₂,out,aux,ho,rank,run⟩ := fullRank_boundedRun (GramEngine.actions read) M
    (GramEngine.Ready w v n m c ready) (GramEngine.Pending w v m c ready) spec
    (fun q fs s h hr => hdesc q fs s (h.trans hdepth) hr) haux hwc hv hscan
    (0 : Word w) (startRegs w n m) initial hready hregs
  have hroot := readClock_le n n Z desc b w v e d hn' hn' hz'
  have hrect := Nat.mul_le_mul (Nat.add_le_add_right hn' 1) (Nat.add_le_add_right hz' 1)
  have htime : boundedRankTime n m desc b w v e ≤
      (2^d+1)*(2^d+1)*(queryAllowance d w v e B + checkClock w v e + 1)+2 :=
    Nat.add_le_add_right (Nat.mul_le_mul hrect (Nat.add_le_add_right (Nat.add_le_add_right hroot _) _)) _
  have hspace := readSpace_le n n ds a b w v e d hn' hn'
  have htotal : boundedRankSpace n ds a b w v e ≤ gramSpace d w v e A S :=
    (max_le_max hspace le_rfl).trans (le_max_right ..)
  exact ⟨_, Nat.add_le_add h₁ (h₂.trans htime), out, aux, ho, rank,
    (start.enlarge (le_max_left ..)).followedBy (run.enlarge htotal)⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
