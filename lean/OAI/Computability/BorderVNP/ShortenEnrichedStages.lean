import OAI.Computability.BorderVNP.ShortenSourceSelectedPath
import OAI.Computability.BorderVNP.PackedHistoryNamedState
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseReplay

/-!
# Installing selected physical stages on enriched public states

An admissible state may retain its full public words and sparse directories.
The geometric view of those states suffices to install the prescribed
selection. A receipt from a particular Boolean kernel supplies the same
properties for that kernel's own stage, without selecting the placement again.
Every attained histogram remains in the next source catalog after dense saving.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Cover.Frame Epoch Hecke Shortening Shortening.Adaptive Shortening.Framed Packing Catalog Physical
open scoped Classical BorderVNP.Epoch.Cube

variable {D m b k d old : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ}

namespace SourceTemplate

/-- Quantitative and geometric consequences of the very receipt returned by
the node. Eliminating the scheduled depth equality preserves the input rows,
the particular stage and all of its successor histograms. -/
theorem receiptAt_spec (src : SourceTemplate e h H ν S) {he : old = d+2*src.word}
    {child : Fin k → PlacedPack D P bits K (Cube D) old} {hk : 0 < k}
    {sel : src.SelectionAt he child hk} {dir : CableSlots (raw child)} {s : Stage m src.bins.Bin d child}
    (receipt : src.ReceiptAt he child hk sel dir s) :
    s.rowCount = dir.rows ∧ (∀ x, (s.slot x).val = (dir.number x).val) ∧
    Nonempty (Stage.Measurements s hk H ν src.mean src.motion) ∧ s.RecordFactor e src.record ∧
    ∀ q : s.Index e, PlacedAt (src.bins.successorSites src.word e) h (s.result e q) := by
  subst old
  obtain ⟨r⟩ := receipt
  exact ⟨by rw [r.trace.realizes]; rfl,fun x => by rw [r.trace.realizes]; rfl,
    ⟨r.measure⟩,r.records,r.closure⟩

end SourceTemplate

namespace SourcePath

variable (p : SourcePath b e h H ν) (last high : ℕ) {A : ℕ → Type*}
    (view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K (Cube D) (p.asPath.depth last high j))
    (hk : 0 < k)

/-- Consequences for the same stage computed on an enriched child tuple.
The destination names may be those chosen by the serializer on each branch. -/
structure InstalledStage (i : Fin b) (c : Fin k → A i.val)
    (sel : (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => view i.val (c j)) hk)
    (dir : CableSlots (raw fun j => view i.val (c j)))
    (s : Stage m (p.pattern i).bins.Bin (p.asPath.depth last high (i.val+1)) (fun j => view i.val (c j))) : Prop where
  /-- Literal selection, input cable names, placement and estimates. -/
  receipt : (p.pattern i).ReceiptAt (p.stepDepth last high i) (fun j => view i.val (c j)) hk sel dir s
  /-- The public input rectangle has the prescribed size. -/
  capacity : s.rowCount = dir.rows
  /-- The input row of every occupied cable is preserved. -/
  slots : ∀ x, (s.slot x).val = (dir.number x).val
  /-- Measured shortening on the actual selected step. -/
  measure : Nonempty (Stage.Measurements s hk H ν (p.pattern i).mean (p.pattern i).motion)
  /-- Local record growth on each attainable histogram. -/
  records : s.RecordFactor e (p.pattern i).record
  /-- The actual dense cable order stays in the successor catalog. -/
  saved : ∀ (q : s.Index e) (rows : ℕ) (slot : (s.result e q).pack.layout.Edge ↪ Fin rows),
    PlacedAt (p.catalog (i.val+1)) h ((s.result e q).dense slot)

/-- Recover every geometric stage property directly from a supplied physical
receipt. The stage can be the particular one produced by the named kernel. -/
theorem installed_of_receipt (i : Fin b) (c : Fin k → A i.val)
    (sel : (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => view i.val (c j)) hk)
    (dir : CableSlots (raw fun j => view i.val (c j)))
    (s : Stage m (p.pattern i).bins.Bin (p.asPath.depth last high (i.val+1)) (fun j => view i.val (c j)))
    (r : (p.pattern i).ReceiptAt (p.stepDepth last high i) (fun j => view i.val (c j)) hk sel dir s) :
    p.InstalledStage last high view hk i c sel dir s := by
  obtain ⟨capacity,slots,measure,records,closed⟩ := (p.pattern i).receiptAt_spec r
  refine ⟨r,capacity,slots,measure,records,?_⟩
  intro q rows slot
  rw [p.next i]
  exact placedAt_dense _ (closed q) slot

/-- Install prescribed circuit selections and original cable slots for every
tuple of enriched admissible states of the finite source schedule. -/
theorem enrichedStages
    (floors : ∀ i : Fin b, (p.pattern i).floor ≤ p.asPath.depth last high (i.val+1))
    (ready : ∀ (i : Fin b) (c : A i.val), PlacedAt (p.catalog i.val) h (view i.val c))
    (sel : ∀ (i : Fin b) (c : Fin k → A i.val),
      (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => view i.val (c j)) hk)
    (dir : ∀ (i : Fin b) (c : Fin k → A i.val), CableSlots (raw fun j => view i.val (c j))) :
    ∃ stage : ∀ (i : Fin b) (c : Fin k → A i.val),
        Stage m (p.pattern i).bins.Bin (p.asPath.depth last high (i.val+1)) (fun j => view i.val (c j)),
      ∀ i c, p.InstalledStage last high view hk i c (sel i c) (dir i c) (stage i c) := by
  have run (i : Fin b) (c : Fin k → A i.val) : ∃ s, p.InstalledStage last high view hk i c (sel i c) (dir i c) s := by
    obtain ⟨s,_,_,_,⟨r,_⟩,_⟩ := (p.pattern i).installAt (p.stepDepth last high i) (floors i) hk
      (fun j => view i.val (c j)) (fun j => ready i (c j)) (sel i c) (dir i c)
    exact ⟨s,p.installed_of_receipt last high view hk i c (sel i c) (dir i c) s r⟩
  choose stage receipt using run
  exact ⟨stage,receipt⟩

end SourcePath

namespace NamedState

variable {lev V E w : ℕ → ℕ} {W : ℕ → Type} [∀ j, Fintype (W j)] {Extra : ℕ → Type*}
    {B : Fin b → Type} [∀ i, Fintype (B i)]
    {good : ∀ j, At (D := D) (K := K) (lev := lev) (V := V) (E := E) (W := W)
      (Extra := Extra) (k := k) (bits := bits) j → Prop}
    (stage : ∀ (i : Fin b) (c : Fin k → Admissible good i.val), Stage m (B i) (lev (i.val+1))
      (fun j => (c j).val.placed))
    (room : ∀ i c a, (stage i c).matched a < 2^w i.val)
    (kernel : Steps k b W (Pin (Cube D) B lev e.count w))
    (names : ∀ i c (q : (stage i c).Index e), Directory ((stage i c).result e q) (V (i.val+1)) (E (i.val+1)))
    (extra : ∀ i c, (stage i c).Index e → Extra (i.val+1))
    (closed : ∀ i c q, good (i.val+1) (save e stage room kernel names extra i c q))

/-- The sparse destination cables used by the actual named save satisfy the
full directory contract for enriched execution and physical record replay. -/
noncomputable def savedDirectory : (program e stage room kernel names extra closed).SaveNames where
  capacity := fun i _ _ => E (i.val+1)
  number := fun i c q => (names i c q).cables
  stored := fun _ _ _ => rfl

end NamedState
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
