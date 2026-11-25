import OAI.Computability.BorderVNP.DiagonalEnrichedTape
import OAI.Computability.BorderVNP.TransmissionChosenStartup

/-! # The true processor literal used by the enriched parse network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP

variable {pc reg operands routines R r w a : ℕ}

/-- The original literal field after the two compact cut lengths. It contains
the startup row's actual address, sorter block size, program-specific registers,
public operands, packet advice and all remaining literal bits. -/
def SiteData.enrichedFree (data : SiteData R r reg operands w a) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc reg operands routines) (n ec link : ℕ) :
    Fin (R+1) → Fin r → Fin (setupWidth (w+1) n+(prefixCapacity r operands reg w n+1+a)) → Bool :=
  fun u j => entryTail (w+1) n
    (j.val*entryStride physical (w+1) n (prefixCapacity r operands reg w n+1+a) R link)
    (2^ec) (data.siteBits P n ec u j)

/-- The native RAM's sorter and the enriched private verifier use identical
wiring with these tails, for every packet placement and every later pin. -/
theorem wiringWith_enriched (data : SiteData R r reg operands w a) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc reg operands routines) (k pins link ec : ℕ)
    (fit : fitsWith physical reg operands r w a R link (k+1) ec) :
    wiringWith physical P data pins link (k+1) ec fit =
      Diagonal.CellEntries.SewnTape.wiring (regs := reg) (w := w) (ec := ec) (width := w+1)
        physical fit (data.enrichedFree physical P (k+1) ec link) pins := rfl

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
