import OAI.Hierarchy.DescentRawFieldOps
import OAI.Hierarchy.DescentHostCountMask
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # The physical next host-count header in an ordinary dictionary update -/
namespace Hierarchy.DescentHostCount
open ProtocolRAM DescentIssuedTerminalId DescentOrdinaryDestRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w : ℕ}

def advance (bank : Bank) (factor : ℕ) := times factor (.lookup bank (.lit 0))

theorem advance_work (bank : Bank) (factor : ℕ) : (advance bank factor).work=1+7*factor := by
  induction factor with
  | zero=>rfl
  | succ factor ih=>
    change 6+(advance bank factor).work+1=1+7*(factor+1)
    rw [ih];omega

theorem advance_exec (bank : Bank) (factor out before : ℕ) (m : Memory w)
    (fit : bank.Fits w out) (space : out+1<2^w) (prior : m bank.base=(before:Word w)) :
    let term:=advance bank factor
    let dst:=image out 1 term m
    (scan w out 1 term).Exec m dst (4+1*(2*term.work+4)) ∧ dst out=(before*factor:Word w) ∧
      ∀a,a≠out→dst a=m a := by
  have safe : ∀i,(advance bank i).Fits w out := by
    intro i
    induction i with
    | zero=>trivial
    | succ i ih=>exact ⟨⟨fit,trivial⟩,ih⟩
  have value : (Expr.lookup bank (.lit 0)).eval m (0 : Word w) = (before : Word w) :=
    (lookup_nat bank m 0 (.lit 0) 0 rfl fit.1 fit.2.1).trans (by simpa only [Nat.add_zero] using prior)
  refine ⟨scan_exec out 1 (advance bank factor) m (safe factor) space, ?_, fun a away =>
    ProtocolRAMGeneratedWrite.frame_image out 1 (advance bank factor) m a (by omega)⟩
  have row : image out 1 (advance bank factor) m out = (advance bank factor).eval m 0 := by
    simpa only [Fin.val_zero, Nat.add_zero, Nat.cast_zero] using
      ProtocolRAMGeneratedWrite.read_image out 1 (advance bank factor) m (0 : Fin 1)
  exact row.trans (by rw [advance, times_eval, value, mul_comm (factor : Word w) (before : Word w)])


end Hierarchy.DescentHostCount

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCompiler DescentHostDegree ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d k w : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {S : AtomSchedule}
  {q ε : ℝ} {W : MarkedWorld F d P bits} {i z degree wire hist z' degree' : ℕ} {u : ℝ}
  {src : Reached W G q ε S k i z degree wire hist} {he : 0≤ε} {T : StageInput W G u ε}
  {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {tgt : Reached n.result G q ε S k (i+1) z' degree' wire hist}
  (link : OrdinaryLink src he T p n tgt)

include link in
/-- Charge a single scalar header independently of the number of repeated groups. -/
theorem count_read (bank : Bank) (out : ℕ) (m : Memory w) (fits : bank.Fits w out)
    (room : out+1<2^w) (prior : m bank.base=(Fintype.card src.V:Word w)) :
    let factor:=(2^(k+1)-1)*(2^packExponent 20 src.placement.degree+2)
    let term:=DescentHostCount.advance bank factor
    let dst:=image out 1 term m
    (scan w out 1 term).Exec m dst (4+1*(2*term.work+4)) ∧ dst out=(Fintype.card tgt.V:Word w) ∧
      ∀a,a≠out→dst a=m a := by
  let factor := (2^(k+1)-1)*(2^packExponent 20 src.placement.degree+2)
  have count : Fintype.card tgt.V = Fintype.card src.V * factor :=
    link.hostCount.trans (Nat.mul_assoc _ _ _)
  have result : (Fintype.card tgt.V : Word w) = (Fintype.card src.V : Word w) * (factor : Word w) := by
    rw [count, Nat.cast_mul]
  rw [result]
  exact DescentHostCount.advance_exec bank factor out (Fintype.card src.V) m fits room prior

end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
