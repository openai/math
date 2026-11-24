import OAI.Computability.VPVNP.RegisterTableRoutine
import OAI.Computability.VPVNP.MacaulayExponentQuery

/-! # Returning monomial-index and powered-entry routines

The caller supplies fixed-width registers and receives the raw index or
comparison flags in the same bank. Both routines return with the private log
and instruction scratch ports empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open RAMTape.RegisterTable

/-- Returning register routine that decodes a dense graded monomial ordinal to its raw code. -/
def ordinalRoutine := routine ISA.table
/-- Returning register routine that compares transformed source exponents with a column,
reports divisibility and equality, and reads a requested residual exponent. -/
def exponentRoutine := routine ExponentISA.table

theorem ordinalRoutine_runs {w t D : ℕ} (k : Fin (size t D)) (fit : ISA.Fits (ISA.graded t D k) w) :
    let p := ISA.graded t D k
    let unit := RAMTape.ISA.prepareBound w 0+3
    ∃ ticks ≤ (rawSize t D*(5*t+10)+2)*unit, ∃ out,
      ordinalRoutine.BoundedRun (w+unit) ticks (bank Fin.elim0 0 (ISA.registers w p {}))
        (bank Fin.elim0 0 (ISA.registers w p out)) ∧
      out.cursor = (rawCode (enumeration t D k)).val ∧ out.count = k.val := by
  intro p unit
  obtain ⟨n,hn,out,hout,hr⟩ := ISA.scan_physical p fit
  obtain ⟨ticks,ht,hret⟩ := return_run (T := ISA.table) (pc := 14) rfl hr
  refine ⟨ticks, ?_, out, hret, ISA.ordinal_result hout⟩
  change n ≤ (rawSize t D*(5*t+10)+1)*unit at hn
  change ticks ≤ (rawSize t D*(5*t+10)+1+1)*unit
  rw [Nat.add_one_mul]
  dsimp [unit] at hn ⊢
  omega

theorem exponentRoutine_runs {w t : ℕ} (p : ExponentISA.Parameters) (fit : ExponentISA.Fits p w)
    (source column : ℕ) (ht : t < 2^w) (ha : source < 2^w) (hb : column < 2^w) :
    let input : ExponentISA.Work := ⟨t,source,column,0,true,true,0,0⟩
    let unit := RAMTape.ISA.prepareBound w 0+3
    ∃ ticks ≤ (16*t+2)*unit, ∃ out,
      exponentRoutine.BoundedRun (w+unit) ticks (bank Fin.elim0 0 (ExponentISA.registers w p input))
        (bank Fin.elim0 0 (ExponentISA.registers w p out)) ∧
      (out.divides = true ↔ ∀ i < t, ExponentISA.scaledDigit p (t-i) (source/p.sourceBase^i) ≤ column/p.columnBase^i%p.columnBase) ∧
      (out.same = true ↔ ∀ i < t, ExponentISA.scaledDigit p (t-i) (source/p.sourceBase^i) = column/p.columnBase^i%p.columnBase) ∧
      ∀ i < t, p.request = t-i → out.residual =
        column/p.columnBase^i%p.columnBase - ExponentISA.scaledDigit p (t-i) (source/p.sourceBase^i) := by
  intro input unit
  obtain ⟨n,hn,out,hr,hdiv,heq,hread⟩ := ExponentISA.run_digits p fit source column ht ha hb
  obtain ⟨ticks,hb,hret⟩ := return_run (T := ExponentISA.table) (pc := 17) rfl hr
  refine ⟨ticks, ?_, out, hret, hdiv,heq,hread⟩
  change ticks ≤ (16*t+1+1)*unit
  rw [Nat.add_one_mul]
  dsimp [unit]; omega

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
