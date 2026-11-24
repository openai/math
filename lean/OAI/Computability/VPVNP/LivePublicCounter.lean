import OAI.Computability.VPVNP.LivePublicAssembler
import OAI.Computability.VPVNP.LivePublicVirtualSites
import OAI.Computability.VPVNP.LiveProgramLayout

/-!
# Values of the coefficient counter's public bank

At a given program prefix, the 34 scalar values agree with the operands
read by the auxiliary machine, uniformly over its pairs, exterior bits and
nominations. The physical loader of these values reads the prefix from
the input tape, as proved in `LivePublicCounterOperands`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CounterPublic

open BurstRAM BurstRAM.PrivateRAM PrimedCounter

/-- Use the supplied program and the live chain, advice, and cut powers as the fixed primed
assembler specification. -/
def spec (p : UniversalMachine.Program) (c : Constants) : AssemblerPublic.Spec :=
  ⟨p,c.chainPower,c.advicePower,c.deltaPower⟩

/-- The coefficient counter's 34 public length expressions, combining the primed assembler,
paper grammar parser, and call schedule. -/
def table (p : UniversalMachine.Program) (c : Constants) : Fin 34 → PublicExpr :=
  (ParserPublic.paperInputs ((spec p c).table virtualSites) c.circuitExponent).table

variable (p : UniversalMachine.Program) (c : Constants) {B n H : ℕ}
  {i : Fin (2^(n^c.chainPower-1))}
  (Q : PrimedInputRAM.Layout ((spec p c).lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : Data Q (n^(c.circuitExponent+5)))

/-- Every output and every intermediate is correct in an actual fitted parser layout. -/
theorem correct (hB : 1 ≤ B) (hn : 2 ≤ n) (hp : Q.program = p)
    (hbase : Q.scratchBase = 2^CursorBounds.virtualBits B n) (hf : D.Fits) (hroot : D.root.val = 0)
    (j : Fin 34) :
    Fin.ofNat (2^CursorBounds.wordBits B n) ((table p c j).eval (AssemblerPublic.geometry B n H)) = D.pub j ∧
    (table p c j).Fits (AssemblerPublic.geometry B n H) (2^CursorBounds.wordBits B n) := by
  have he : virtualSites.eval (AssemblerPublic.geometry B n H) = Q.scratchBase := by
    rw [hbase]
    exact virtualSites_eval _ hn
  have hb : 2 ^ CursorBounds.virtualBits B n < 2 ^ CursorBounds.wordBits B n := by
    rw [← hbase]
    exact PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 6
  have hvirt := virtualSites_fits (H := H) hB hn hb
  apply ParserPublic.paper_table D _ _ _ hf hroot _ j
  · exact (spec p c).table_eval Q virtualSites hp he (by omega)
  · exact (spec p c).table_fits Q virtualSites hf.assembler hp hvirt hB hn

end LiveProgram.CounterPublic

end VPVNP
end Computability
end OAI
