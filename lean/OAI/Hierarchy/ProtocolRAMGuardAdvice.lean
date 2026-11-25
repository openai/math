import OAI.Hierarchy.ProtocolRAMAttemptThresholds
import OAI.Hierarchy.ProtocolRAMPrices
import OAI.Hierarchy.ProtocolRAMMenu

namespace OAI
/-! # Finite advice generating the scores of the actual maximizer and local tests -/

noncomputable section
namespace Hierarchy.ProtocolRAM.AttemptGate
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing BigOperators Classical

/-- The first address word of each commodity contains its block offset. The second
word is the current integer inventory. All real-valued calculations are tabulated
once per commodity kind and possible bounded stock. -/
def valueTerm (table offsets stocks : Bank) : Expr :=
  .lookup table (.op .add (.lookup offsets .row) (.lookup stocks .row))

def valueWord (precision : ℕ) (f : ℕ→ℕ→ℝ) (kind bits : ℕ) : ℕ := ⌊(precision:ℝ)*f kind bits⌋₊

def valueAdvice {w : ℕ} (table : Bank) (kinds stride Q : ℕ) (f : ℕ→ℕ→ℝ) (m : Memory w) :=
  fillSegment table.base (kinds*stride) (fun a=>
    (valueWord Q f ((a-table.base)/stride) ((a-table.base)%stride) : Word w)) m

theorem valueTerm_read {w : ℕ} (table offsets stocks : Bank) (kinds stride Q : ℕ)
    (f : ℕ→ℕ→ℝ) (m : Memory w) (row : Word w) (kind : Fin kinds) (bits : Fin stride)
    (kindWord : offsets.read (valueAdvice table kinds stride Q f m) row = (kind.val*stride : ℕ))
    (stockWord : stocks.read (valueAdvice table kinds stride Q f m) row = (bits.val:Word w))
    (room : kinds*stride < 2^w) (capacity : kinds*stride ≤ table.size) :
    (valueTerm table offsets stocks).eval (valueAdvice table kinds stride Q f m) row =
      (valueWord Q f kind.val bits.val : Word w) := by
  let i := kind.val*stride+bits.val
  have b := Nat.mul_le_mul_right stride kind.isLt
  rw [Nat.succ_mul] at b
  have pos := bits.isLt
  have bound : i<kinds*stride := by dsimp [i];omega
  have within : table.base≤table.base+i ∧ table.base+i<table.base+kinds*stride := by omega
  have div : i/stride=kind.val := by
    dsimp [i]
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt pos,Nat.zero_add]
  have mod : i%stride=bits.val := Nat.mul_add_mod_of_lt pos
  simp only [valueTerm,Expr.eval,RowOp.opcode,BinaryOp.eval,kindWord,stockWord,←Nat.cast_add]
  change table.read _ (i:Word w)=_
  simp only [Bank.read,Fin.val_cast_of_lt (bound.trans room),Nat.mod_eq_of_lt (bound.trans_le capacity),
    valueAdvice,fillSegment,ite_eq_left within,Nat.add_sub_cancel_left,div,mod]

def potentialRow (s : PhasePrice) (kind bits : ℕ) :=
  AdaptiveProbe.rowScore s.a (s.bonus kind) s.M (s.quote kind bits)

def payloadRow (s : PhasePrice) (payloadKind : ℕ→Bool) (kind bits : ℕ) :=
  if payloadKind kind then s.quote kind bits else 0

/-- Every grid vector addresses its own local discrepancy score; the finite table can be
reused at every candidate of the same bounded format. -/
def discrepancyWord {d radix k : ℕ} (F : Type*) [Field F] {E A : Type*}
    [Fintype E] [Nonempty E] [Fintype A] [Nonempty (Fin k)] (edge : E→Chord k) (req : A→E)
    (price : (Fin d→Fin radix)→E→ℝ) (Q : ℕ) (v : Fin d→Fin radix) : ℕ :=
  ⌊(Q:ℝ)*Probe.discrepancy F edge req (price v)⌋₊

/-- At the paper's interior threshold 3/8, row quantization by at most one word
leaves the overlap between the 1/4 purchase threshold and the 1/2 advance threshold. -/
theorem excess_overlap {n : ℕ} (value : Fin n → ℝ) (nonneg : ∀i,0≤value i) (Q : ℕ) (hq : 0<Q)
    (population baseline : ℝ) (hp : 0<population) (base : 0≤baseline)
    (precision : (n:ℝ)/Q ≤ population/8) :
    let score := fun i=>⌊(Q:ℝ)*value i⌋₊
    let bound := ⌈(Q:ℝ)*(population*(baseline+3/8))⌉₊
    (bound ≤ ∑ i,score i → 1/4 < (∑i,value i)/population-baseline) ∧
      (¬bound ≤ ∑ i,score i → (∑i,value i)/population-baseline ≤ 1/2) := by
  obtain ⟨large,small⟩ := threshold_bounds value nonneg Q hq (population*(baseline+3/8)) (by positivity)
  constructor
  · intro triggered
    have h := large triggered
    rw [lt_sub_iff_add_lt,lt_div_iff₀ hp]
    nlinarith only [h,hp]
  · intro quiet
    have h := small quiet
    rw [sub_le_iff_le_add,div_le_iff₀ hp]
    nlinarith only [h,precision]

/-- The actual threshold over rounded local discrepancy words separates the mean
needed by failed-ball packing from the low-discrepancy purchase condition.
The phase chooses its base tolerance small enough that 4ε meets that condition. -/
theorem discrepancy_overlap {n k : ℕ} (F : Type*) [Field F] {E A : Type*}
    [Fintype E] [Nonempty E] [Fintype A] [Nonempty (Fin k)] (edge : E→Chord k) (req : A→E)
    (conn : Probe.Connected edge) (price grid : Fin n→E→ℝ) (Q : ℕ) (hq : 0<Q)
    (ε : ℝ) (hε : 0≤ε) (approx : ∀i e,|price i e-grid i e|≤ε/2)
    (precision : (n:ℝ)/Q ≤ n*(ε/2)) :
    let rounded := fun i=>Probe.discrepancy F edge req (grid i)
    let actual := fun i=>Probe.discrepancy F edge req (price i)
    let bound := ⌈(Q:ℝ)*(3*ε*n)⌉₊
    let words := ∑ i,⌊(Q:ℝ)*rounded i⌋₊
    (bound≤words → 2*ε*n ≤ ∑i,actual i) ∧ (¬bound≤words → ∑i,actual i ≤ 4*ε*n) := by
  let r (i : Fin n) := Probe.discrepancy F edge req (grid i)
  let p (i : Fin n) := Probe.discrepancy F edge req (price i)
  have positive (i : Fin n) : 0≤r i := by
    obtain ⟨φ,t,_,eqn⟩ := Probe.discrepancy_attained F edge req (grid i) conn
    change 0≤Probe.discrepancy F edge req (grid i)
    rw [eqn]
    exact Probe.testError_nonneg ..
  obtain ⟨hit,miss⟩ := threshold_bounds r positive Q hq (3*ε*n) (by positivity)
  have near (i : Fin n) : |p i-r i|≤ε/2 := Probe.discrepancy_lipschitz F edge req conn _ _ (approx i)
  have up := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>sub_le_iff_le_add.mp (abs_le.mp (near i)).2)
  have dn := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    show r i≤p i+ε/2 by linarith only [(abs_le.mp (near i)).1])
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at up dn
  constructor
  · intro active
    change 2*ε*n ≤ ∑i,p i
    nlinarith only [hit active,dn,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) hε]
  · intro quiet
    change (∑i,p i)≤4*ε*n
    nlinarith only [miss quiet,up,precision]

end Hierarchy.ProtocolRAM.AttemptGate

end
end OAI
