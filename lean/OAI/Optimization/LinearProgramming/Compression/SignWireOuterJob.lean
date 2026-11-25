import OAI.Optimization.LinearProgramming.Compression.SignWireNumericService
import OAI.Optimization.LinearProgramming.Compression.SignWireRowWindow
import OAI.Optimization.LinearProgramming.Compression.SignWireResidentData
import OAI.Optimization.LinearProgramming.Compression.SymbolicCacheFrame

/-! Construct the numeric service's input predicate from a persistent allocated
cache and the physical VM header, before seeing any of the adaptive row's signs. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable MinorProxyCache

theorem stableCache_writeRow {n fuel prec base : ℕ} {mag : ℕ → ℚ} {L : Buffers} {caller : Memory ℚ}
    (cache : StableCache caller L n fuel prec mag) (apart : RowAwayFromCache L n base)
    (row : Fin (n+1) → ℚ) :
    StableCache (writeRow caller base row) L n fuel prec mag := by
  refine ⟨cache.header.transfer (fun _ _ _ => rfl),cache.separated,?_,cache.positive,?_,
    cache.symbolic,cache.any,cache.zero,?_⟩
  · intro j hj
    have far := apart.magnitudes
    exact (writeRow_miss _ _ _ _ (by omega)).trans (cache.magnitude j hj)
  · intro j hj
    have far := apart.numerators
    exact (writeRow_miss _ _ _ _ (by omega)).trans (cache.numerator j hj)
  · have far := apart.scale
    exact (writeRow_miss _ _ _ _ (by omega)).trans cache.scale

/-- The outer callback can accept every row that its signed-word decoder actually
writes. Its environment is derived from header and allocation facts, with no
assumption about the result of a numerical comparison or its execution. -/
theorem outerJobData_of_window {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R cap src base : ℕ)
    (P : ℚ → Prop) (raw old caller : Memory ℚ)
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller)
    (window : RowWindowSetup raw old caller cap base (n+1))
    (dimension : raw.index 51=n+1) (destination : raw.index 55=4*base+2)
    (reply : 3≤raw.index 47) (positive : 0<src)
    (safeRead : ∀ i j, i<j → j<n+1 → 4*(base+i)+2≠src+j) :
    OuterJobData (n:=n) mag L fuel prec C R cap src base P raw := by
  refine ⟨dimension,destination,reply,positive,safeRead,?_⟩
  intro row copied t st ht
  let values (i : Fin (n+1)) : ℚ := row i
  let logical := writeRow caller base values
  let finalOld := old.putData 0 (t.data 0)
  obtain ⟨image,parity⟩ := st.window_image window values copied
  have safeValues (i : Fin (n+1)) : P (values i) := by
    have hval := ht (4*(base+i.val)+2)
    rw [st.words i.val i.isLt,copied i] at hval
    exact hval
  have coeff (i : Fin (n+1)) : logical.data (logical.index 67+i.val)=(row i:ℚ) := by
    change (writeRow caller base values).data (caller.index 67+i.val)=_
    rw [seed.rowPtr]
    exact writeRow_at caller base values i
  refine ⟨parity,finalOld,logical,image,?_⟩
  exact {
    cache := stableCache_writeRow seed.cache seed.apart values
    workspace := seed.workspace.transfer_headers (fun _ _ _ _ => rfl)
    reservation := seed.reservation.transfer_headers (fun _ _ _ _ => rfl)
    coeff := coeff
    callerSafe := writeRow_allData base seed.callerSafe safeValues
    nativeSafe := seed.nativeSafe.putData 0 (ht 0)
    nativeBound := footprint_scratchZero seed.nativeBound _
    capacity := seed.capacity
    callerBound := seed.callerBound }

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
