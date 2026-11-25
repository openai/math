import OAI.ThreeFlat.Diagonal.RefreshStageNav
import OAI.ThreeFlat.RAM.HeaderPipeline

namespace OAI
/-! # Native stage return values for the refresh header ABI -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure
open RAM.MotifRows RefreshDemandRows
variable {W a h k : ℕ}

noncomputable def preparation (current : Word W) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : Pipeline W :=
  (Pipeline.scan current 12 13 (closed (splitShifts (mPort a) current))).thenDo
    (Pipeline.scan current 2 18 (closed (choiceWords current base size)))

noncomputable def publication (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) : Pipeline W :=
  let widths := generateWidth (input current) (field current 8) (index current 19) (field current 1)
    pad stride base size bits pool
  (Pipeline.scan current 14 16 (graphWords current E pad)).thenDo
    ((Pipeline.scan current 19 17 (closed widths)).thenDo
      (Pipeline.scan current 3 20 (closed (sparseCopy (mPort a) h pad current))))

theorem preparation_returns (current : Word W)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) (m : Memory W) (fit : (preparation current base size).fits m) :
    (prepare current base size).Spec (fun n => n=m) (fun _ out => out=(preparation current base size).run m)
      ((preparation current base size).ticks m) := (preparation current base size).correct m fit

theorem publication_returns (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ)
    (m : Memory W) (fit : (publication current E pad stride base size bits pool).fits m) :
    (commit current E pad stride base size bits pool).Spec (fun n => n=m)
      (fun _ out => out=(publication current E pad stride base size bits pool).run m)
      ((publication current E pad stride base size bits pool).ticks m) :=
  (publication current E pad stride base size bits pool).correct m fit

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
