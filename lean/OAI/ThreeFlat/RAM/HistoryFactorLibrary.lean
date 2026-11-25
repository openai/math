import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Shared coefficient tables for trivalent weighted factors -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM BitLayout

variable {F : Type*} {p w : ℕ}

/-- Only a library identifier is stored with each factor; multiple factors may share a table. -/
structure Library (N : BitNetwork F p) where
  count : ℕ
  id : Fin N.cells → Fin count
  table : Fin count → (Fin 3 → Bool) → F
  correct : ∀ i, N.table i = table (id i)

/-- The first block stores three resolved bit addresses and one tag per selected factor.
The second block stores the eight entries of each shared coefficient table. -/
structure Stores (N : BitNetwork F p) (L : Library N) (code : FieldCode F w)
    (metadata lut : ℕ) (m : Memory w) : Prop where
  source : ∀ (i : Fin N.cells) (j : Fin 3), m (metadata + 4*i.val+j.val) =
    Fin.ofNat _ (sourceAddress (N.source i j))
  tag : ∀ i : Fin N.cells, m (metadata + 4*i.val+3) = Fin.ofNat _ (L.id i).val
  coefficient : ∀ (t : Fin L.count) (j : Fin 8), m (lut + 8*t.val+j.val) =
    code.encode (L.table t (bits j.val))

end ThreeFlat.RAM.HistoryFactors

end OAI
