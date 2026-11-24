import OAI.Computability.VPVNP.LivePublicPaperParser
import OAI.Computability.VPVNP.LivePublicIncidentWidth
import OAI.Computability.VPVNP.PairedChain

/-!
# Assembler operands for the primed pair

The index width is the one-based group's width. The cut field is the maximum
capacity shared by every pair. Actual cut lengths live in the three initial
RAM cells and therefore never occur in this public table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.AssemblerPublic

open PrimedInputRAM BurstRAM

/-- Constants of the fixed live program. -/
structure Spec where
  /-- The universal-machine program whose literal prefix is placed in the primed pair inputs. -/
  program : UniversalMachine.Program
  /-- Exponent controlling the group index width and the height of the first half of the chain. -/
  groupExp : ℕ
  /-- Exponent giving the distributed advice length as a power of the input length. -/
  adviceExp : ℕ
  /-- Exponent giving the basic cut block width as a power of the input length. -/
  cutExp : ℕ

/-- Compute the site's address and RAM word widths from the address multiplier and input
length, and attach the supplied bucket capacity. -/
def geometry (B n H : ℕ) : Geometry :=
  ⟨n,addressWidth B n,H,CursorBounds.wordBits B n⟩

namespace Spec

variable (s : Spec)

/-- The paired chain's actual index, advice, and cut lengths for the specified pair at input
length n. -/
abbrev lengths (n : ℕ) (i : Fin (2^(n^s.groupExp-1))) :=
  PairedChain.lengths (n^s.groupExp-1) (n^s.cutExp) (n^s.adviceExp) i

/-- Public expression for the number of sites in one group, two raised to the site-address
width. -/
def R : PublicExpr := .pow2 .d
/-- Total cells in the input rectangle spanning both groups, twice the number of sites per
group times the input length. -/
def cells : PublicExpr := ((.lit 2 : PublicExpr).mul R).mul .n
/-- Public bit width of the one-based group index, one plus the input length raised to the
group exponent. -/
def index : PublicExpr := ((.n : PublicExpr).natPow s.groupExp).add (.lit 1)
/-- Number of advice bits in a primed row, given by the input length raised to the advice
exponent. -/
def advice : PublicExpr := (.n : PublicExpr).natPow s.adviceExp
/-- Common capacity reserved for a cut, given by the input length raised to the sum of the
group and cut exponents. -/
def capacity : PublicExpr := (.n : PublicExpr).natPow (s.groupExp+s.cutExp)

/-- The sixteen public operands for primed pair assembly, including geometry, virtual scratch
base, literal prefix, incident widths, and cut capacity. -/
def table (virtual : PublicExpr) (j : Fin 16) : PublicExpr :=
  match j.val with
  | 0 => cells
  | 1 => .n
  | 2 => R
  | 3 => .d
  | 4 => .w
  | 5 => .H
  | 6 => virtual
  | 7 => .lit (UniversalMachine.programPrefix s.program).length
  | 8 => IncidentPublic.incident
  | 9 => s.index
  | 10 => s.advice
  | 11 => s.capacity
  | 12 => .lit (Opcodes.packedPrefix s.program).val
  | 13 => IncidentPublic.block
  | 14 => IncidentPublic.successor
  | _ => IncidentPublic.bothSuccessors

variable {B n H : ℕ} {i : Fin (2^(n^s.groupExp-1))}
  (Q : Layout (s.lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (virtual : PublicExpr)

private theorem group_width (hn : 0 < n) : (s.lengths n i).index = n^s.groupExp + 1 := by
  change n^s.groupExp - 1 + 2 = _
  have h := Nat.pow_pos hn (n := s.groupExp)
  omega

private theorem cut_capacity (hn : 0 < n) : (s.lengths n i).cutCapacity = n^(s.groupExp+s.cutExp) := by
  change (n^s.groupExp-1+1)*n^s.cutExp = _
  have h := Nat.pow_pos hn (n := s.groupExp)
  rw [show n^s.groupExp-1+1 = n^s.groupExp by omega,pow_add]

/-- The sixteen expressions are the native assembler's public words before reduction modulo the word width. -/
theorem table_eval (hp : Q.program = s.program) (hv : virtual.eval (geometry B n H) = Q.scratchBase)
    (hn : 0 < n) (j : Fin 16) : (s.table virtual j).eval (geometry B n H) = Opcodes.pubNat Q j := by
  have hk : n^s.groupExp-1+1 = n^s.groupExp := by
    have h := Nat.pow_pos hn (n := s.groupExp)
    omega
  have hpack := congrArg (fun p => (Opcodes.packedPrefix p).val) hp
  fin_cases j <;> simp [table, cells, R, index, advice, capacity, Opcodes.pubNat, hp,
    hk, pow_add, IncidentPublic.successor, IncidentPublic.bothSuccessors,
    geometry, PublicExpr.eval, PrimedInputRAM.positions, PairedChain.lengths, lengths]
  · exact hv
  · exact hpack.symm
  · omega

/-- Word fit for every intermediate of all sixteen assembler expressions. -/
theorem table_fits (F : Opcodes.ParameterFit Q) (hp : Q.program = s.program)
    (hv : virtual.Fits (geometry B n H) (2^CursorBounds.wordBits B n))
    (hB : 1 ≤ B) (hn : 2 ≤ n) (j : Fin 16) :
    (s.table virtual j).Fits (geometry B n H) (2^CursorBounds.wordBits B n) := by
  let g := geometry B n H
  let w := CursorBounds.wordBits B n
  let r := addressWidth B n
  let Fit := PublicExpr.Fits g (2^w)
  have hpos : 0 < n := by omega
  have hr : 1 ≤ r := Nat.mul_pos hB (Nat.clog_pos (by decide) hn)
  have fn : Fit .n := ⟨Opcodes.pubNat_lt Q F 1,trivial⟩
  have fd : Fit .d := ⟨Opcodes.pubNat_lt Q F 3,trivial⟩
  have fw : Fit .w := ⟨Opcodes.pubNat_lt Q F 4,trivial⟩
  have fH : Fit .H := ⟨Opcodes.pubNat_lt Q F 5,trivial⟩
  have fR : Fit R := ⟨Opcodes.pubNat_lt Q F 2,fd⟩
  have hcells : (2*2^r)*n < 2^w := Opcodes.pubNat_lt Q F 0
  have hrow := Nat.le_mul_of_pos_right (2*2^r) hpos
  have hR := Nat.two_pow_pos r
  have f2 : Fit (.lit 2) := ⟨by change 2 < _; omega,trivial⟩
  have frows : Fit ((.lit 2 : PublicExpr).mul R) := ⟨by change 2*2^r < _; omega,f2,fR⟩
  have fcells : Fit cells := ⟨hcells,frows,fn⟩
  have fprefix : Fit (.lit (UniversalMachine.programPrefix s.program).length) := ⟨by
    change (UniversalMachine.programPrefix s.program).length < _
    rw [← hp]; exact Opcodes.pubNat_lt Q F 7,trivial⟩
  have fpacked : Fit (.lit (Opcodes.packedPrefix s.program).val) := ⟨by
    change (Opcodes.packedPrefix s.program).val < _
    rw [← hp]; exact Opcodes.pubNat_lt Q F 12,trivial⟩
  have hindex : n^s.groupExp+1 < 2^w := by
    rw [← group_width (i := i) s hpos]; exact Opcodes.pubNat_lt Q F 9
  have fgroup := PublicExpr.fits_natPow fn hpos s.groupExp (show n^s.groupExp < 2^w by omega)
  have findex : Fit s.index := ⟨by change ((.n : PublicExpr).natPow s.groupExp).eval g+1 < _
                                   rw [PublicExpr.eval_natPow]; exact hindex,
                                 fgroup,⟨by change 1 < _; omega,trivial⟩⟩
  have fadv : Fit s.advice := PublicExpr.fits_natPow fn hpos _ (Opcodes.pubNat_lt Q F 10)
  have hcap : n^(s.groupExp+s.cutExp) < 2^w := by
    rw [← cut_capacity (i := i) s hpos]; exact Opcodes.pubNat_lt Q F 11
  have fcap : Fit s.capacity := PublicExpr.fits_natPow fn hpos _ hcap
  obtain ⟨fblock,fs,fss,fincident⟩ := IncidentPublic.fits Q F hr rfl g rfl rfl rfl
  fin_cases j
  · exact fcells
  · exact fn
  · exact fR
  · exact fd
  · exact fw
  · exact fH
  · exact hv
  · exact fprefix
  · exact fincident
  · exact findex
  · exact fadv
  · exact fcap
  · exact fpacked
  · exact fblock
  · exact fs
  · exact fss

end Spec
end LiveProgram.AssemblerPublic

end VPVNP
end Computability
end OAI
