import OAI.Hierarchy.DescentPackedWalshBasis

namespace OAI
/-! # A fixed allocation for the reset spectrum, all depth results and the final GL estimator -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- The numbered depth/gain banks come from the physical reset header. All following sizes are
public before reading a history. The host and difference axes specify every allocated row. -/
structure EstimatorArena where
  hosts : ℕ
  high : ℕ
  low : ℕ
  payload : ℕ
  precision : ℕ
  gainBits : ℕ
  positive : 0<precision
  origin : ℕ
  dataGap : ℕ
  depthRows : Bank
  gainRows : Bank

namespace EstimatorArena
variable (A : EstimatorArena)
def dim := A.high+A.low
def plan := reduction A.hosts A.high A.low A.precision A.payload A.positive
def reduceAt := A.origin+Weight.footprint A.hosts A.high A.low A.precision A.gainBits
def orderAt := A.plan.headerAt A.reduceAt A.plan.depth
def transformAt := A.orderAt+Column.size A.dim (A.precision+A.plan.depth) (A.plan.laneBits A.plan.depth)
def squareAt := A.transformAt+A.dim*span A.hosts A.high A.low A.precision
def staticEnd := A.squareAt+2^(smallKey A.low A.precision)
def start := A.staticEnd+A.dataGap
def numeratorAt := location (sqOffset A.start A.hosts A.high A.low) A.hosts A.high A.dim
def inputEnd := A.numeratorAt+page A.hosts A.high
def dataWords := A.plan.dataAt 0 (A.plan.depth+1)
def stride := A.dataWords+2^A.dim
def scratch (j : ℕ) := A.inputEnd+j*A.stride
def bank (j : ℕ) := A.scratch j+A.dataWords
def solveAt := A.scratch (A.dim+1)

def weights := Weight.banks A.origin A.hosts A.high A.low A.precision A.gainBits A.depthRows A.gainRows
  ⟨A.numeratorAt,rowBits A.hosts A.high⟩

def shelf (j : ℕ) : DepthShelf :=
  ⟨A.weights,A.reduceAt,A.orderAt,A.scratch j,A.bank j⟩

def calendar : Calendar A.dim where
  limit:=A.inputEnd
  atDepth:=A.shelf
  pre j:=Nat.le_add_right ..
  order i j lt:=by
    change (A.inputEnd+i*A.stride+A.dataWords)+2^A.dim≤A.inputEnd+j*A.stride
    have regroup : A.inputEnd+i*A.stride+A.dataWords+2^A.dim=A.inputEnd+(i+1)*A.stride := by
      rw [Nat.succ_mul];simp only [stride,Nat.add_assoc]
    rw [regroup]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ lt) _

theorem data_at (start t : ℕ) : A.plan.dataAt start t=start+A.plan.dataAt 0 t := by
  induction t with
  | zero=>simp [Plan.dataAt]
  | succ n ih=>simp only [Plan.dataAt,ih,Nat.add_assoc]

theorem packed_before (j : ℕ) : A.plan.dataAt (A.scratch j) (A.plan.depth+1)=A.bank j := by
  exact A.data_at _ _

/-- The shared reduced row is sent to a separate bank for every j, hence all remain readable by
the genuine central solver. -/
theorem includes_bank (j : ℕ) (live : j<A.dim+1) : A.bank j+2^A.dim≤A.solveAt :=
  A.calendar.order j (A.dim+1) live

def orderRow (a : ℕ) : Word w :=
  Column.fixedRow (Column.chunkAt A.plan ∘centralOrder A.high A.low)
    (Column.laneAt A.plan ∘centralOrder A.high A.low) (A.precision+A.plan.depth) a

def baseMemory (m : Memory w) : Memory w :=
  let weighted:=Weight.install A.origin A.hosts A.high A.low A.precision A.precision A.gainBits m
  let reduced:=A.plan.mount A.reduceAt weighted A.plan.depth
  fun z=>if A.orderAt≤z ∧ z<A.transformAt then A.orderRow (z-A.orderAt) else reduced z

/-- A single history-independent initial literal image, with arbitrary earlier native memory. -/
def literal (m : Memory w) : Memory w :=
  initial A.transformAt A.squareAt A.hosts A.high A.low A.precision (A.baseMemory m)

theorem order_read (m : Memory w) (i : ℕ) (small : i<
    Column.size A.dim (A.precision+A.plan.depth) (A.plan.laneBits A.plan.depth)) :
    A.baseMemory m (A.orderAt+i)=A.orderRow i := by
  simp [baseMemory,transformAt,small]

theorem lower_reduce (m : Memory w) (z : ℕ) (before : z<A.orderAt) :
    A.baseMemory m z=A.plan.mount A.reduceAt
      (Weight.install A.origin A.hosts A.high A.low A.precision A.precision A.gainBits m) A.plan.depth z := by
  simp [baseMemory,Nat.not_le_of_gt before]

end EstimatorArena
end
end Hierarchy.DescentPackedWalsh

end OAI
