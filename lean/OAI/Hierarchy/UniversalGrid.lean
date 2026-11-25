import OAI.Hierarchy.GridDiagonal
import OAI.Hierarchy.PointwiseCollapse
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Exact and accelerated tensors on one programmed grid

Both tensors interpret the same selector, bit sources and equality tests.
Only the table at the cell holes changes. This keeps the data computed by
the controller separate from the spectral estimate on its errors. -/

namespace Hierarchy.UniversalGrid

open ThreeFlat LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

abbrev Bits (p : ℕ) := Fin p → Bool
abbrev Address (E : Type) (h : ℕ) := Fin h ⊕ (GridDiagonal.Ends E ⊕ Bool)

def bit {E : Type} {h : ℕ} (x : GridDiagonal.Pins E) (w : Bits h) : Address E h → Bool :=
  Sum.elim w (Sum.elim x id)

/-- One output of the controller after checking its selector. There is one
table hole per cell. All other junctions and pin choices use bit sources and
equality tests. An unconnected pin can be supplied by either literal. -/
structure Wiring (E P : Type) (L : ℕ) where
  internal : ℕ
  pin : Fin L → P → Address E internal
  equal : List (Address E internal × Address E internal)

namespace Wiring

variable {F : Type*} [Field F] {E P : Type} {L : ℕ}

/-- Direct contraction over all genuinely shared bit choices. -/
noncomputable def eval (W : Wiring E P L) (cell : (P → Bool) → F) (x : GridDiagonal.Pins E) : F :=
  ∑ w : Bits W.internal,
    (if ∀ uv ∈ W.equal, bit x w uv.1 = bit x w uv.2 then
      ∏ i, cell (fun j => bit x w (W.pin i j)) else 0)

end Wiring

/-- A tick has separate pins in every independent copy. The number of
selector bits and all resources are chosen before its controller description. -/
structure Grid (F : Type*) [Field F] (k : ℕ) where
  pins : ℕ
  copies : ℕ
  g : ℕ
  rails : ℕ
  codeBits : ℕ
  selectorBits : ℕ
  tick : BitNetwork F pins
  replacement : Catalyst.Approximation F k (copies*pins)
  direction : Fin rails → Fin k
  wiring : Bits codeBits → Bits selectorBits →
    Option (Wiring (Fin rails) (Catalyst.Port (copies*pins) replacement.width) (g^k))

namespace Grid

variable {F : Type*} [Field F] {k : ℕ} (G : Grid F k)

noncomputable def exactCell :=
  Catalyst.ideal (F:=F) G.replacement.width (Catalyst.tickProduct G.tick G.copies)

noncomputable def row (cell : (Catalyst.Port (G.copies*G.pins) G.replacement.width → Bool) → F)
    (code : Bits G.codeBits) (s : Bits G.selectorBits) (x : GridDiagonal.Pins (Fin G.rails)) : F :=
  (G.wiring code s).elim 0 (fun W => W.eval cell x)

noncomputable def exactGrid (code : Bits G.codeBits) (x : GridDiagonal.Pins (Fin G.rails)) : F :=
  ∑ s, G.row G.exactCell code s x

noncomputable def accelerated (code : Bits G.codeBits) (x : GridDiagonal.Pins (Fin G.rails)) : F :=
  ∑ s, G.row G.replacement.coeff code s x

def Valid (code : Bits G.codeBits) (s : Bits G.selectorBits) := (G.wiring code s).isSome = true

/-- A native trace distribution output on one honest controller description.
Its scalar table is factored before the pins are supplied. The first equation
is the execution of the evaluator. The second applies only to one selected
wiring at a time and accounts for the identity selector and all simulations. -/
structure Distributed (code : Bits G.codeBits) where
  Trace : Type
  [finite : Fintype Trace]
  factors : Trace → ℕ
  scalar : (z : Trace) → Fin (factors z) → GridDiagonal.Pins (Fin G.rails) → F
  decode : {s // G.Valid code s} ≃ Option Trace
  evaluator : ∀ x, G.accelerated code x = ∑ z, ∏ i, scalar z i x
  at_selector : ∀ s : {s // G.Valid code s}, ∀ x,
    G.row G.exactCell code s.1 x =
      (decode s).elim (GridDiagonal.identity F x) (fun z => ∏ i, scalar z i x)

attribute [instance] Distributed.finite

/-- The pointwise estimate is tested on all descriptions, while the trace and
compiled wiring are needed on one actual description. The same approximation is
used in the weighted evaluator and in the spectral inequality. -/
theorem excludes (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (ends : GridDiagonal.Ends (Fin G.rails) → EuclideanSpace ℝ (Fin k))
    (price : ∀ a, G.exactGrid a - G.accelerated a = 0 ∨
      P.price (GridDiagonal.raw (G.exactGrid a - G.accelerated a)) ends <
        P.price (GridDiagonal.raw (GridDiagonal.identity F)) ends)
    (code : Bits G.codeBits) (H : G.Distributed code) : False := by
  classical
  exact GridDiagonal.impossible P ends G.exactGrid G.accelerated price code
    (Bits G.selectorBits) H.Trace (G.Valid code) H.decode (G.row G.exactCell code)
    (fun z x => ∏ i, H.scalar z i x) (fun _ => rfl) H.evaluator
    (fun s hs x => by
      cases eq : G.wiring code s with
      | none => simp [row,eq]
      | some v => exact (hs (by simp [Valid,eq])).elim)
    H.at_selector

end Grid
end Hierarchy.UniversalGrid

end OAI
