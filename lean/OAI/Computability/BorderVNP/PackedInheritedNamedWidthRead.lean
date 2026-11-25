import OAI.Computability.BorderVNP.PackedInheritedWorkSchedule
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows
import OAI.Computability.BorderVNP.PackedNamedPortHeaders

/-! # The two assigned private widths at a named geometry state

The source word valuation reads the original named geometry and the physical
work and extent of each private program. Its static port header and expanded
record bound are carried at the same state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Packing.Inherited.WorkWords InheritedBank
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop}
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
local notation3 "At" j => NamedState.Admissible (src.NamedGood last high V E w cap keep) j
local notation3 "Words" j => WithWidths (src.StatePins last high V E w j) (V j) w

/-- The full assigned geometry, both physical widths, static port addresses
and genuine expanded load at the scheduled inner state. -/
structure WidthRead (bound : ℕ → ℕ) (j : ℕ) (a : At j) (old : Site.Programs a.val.placed.pack.layout)
    (y : (Words j) → Bool) : Prop where
  /-- The geometry subarray is the named state's assigned valuation. -/
  geometry : y ∘ Sum.inl = a.val.words
  /-- Both columns cover every occupied row and give zero on every vacant row. -/
  widths : ∀ b, Covers a.val.names.sites (fun v => if b then (old v).program.size else (old v).program.work)
    (assignedColumn b) y
  /-- The recursively nested port table uses the actual layout and owner names. -/
  ports : (header.nested k V j).Reads a.val.placed.pack.layout a.val.names.sites (Parallel.nestedPorts k leaf j)
  /-- The actual placed programs meet the expanded record bound at this level. -/
  capacity : RecordsWithin a.val.placed old.bankFields true (bound j)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
