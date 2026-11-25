import OAI.Computability.BorderVNP.DiagonalTaggedHistoryCatalog
import OAI.Computability.BorderVNP.PackedHistoryNamedState
import OAI.Computability.BorderVNP.ShortenPublicDenseReceipt
import OAI.Computability.BorderVNP.ShortenSourceSelectedPath

/-! # Installing the genuinely selected public pass on its assigned child states

The child's stored directory, exact pin assignment and measured tensor are
read together. One execution of the selector fixes the labels, samples and
sorted input before any histogram word. For each attained histogram the
saved dense physical pack and the actual kernel output satisfy the next
directory and catalog contracts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.NamedReceipt

open Cover Cover.Frame Cover.AddressCircuit Crossing Packing Shortening StaticRows CombiningStep
open Epoch Catalog PreparedBins PublicDenseReceipt PublicSegments PublicParallel PublicDirectory
open PublicRelative ParseBatchSort BankCircuit VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ} (src : SourceTemplate e h H ν S)
    {lev d k V E seeds w : ℕ} {Data P : Type} [Fintype Data] {bits : P → ℕ} {Extra : Type*}

/-- All named predecessor data of the selected kernel, including its immutable local payload. -/
abbrev Child := NamedState D P bits K (lev+2*src.word) V E (Fin E ⊕ Raw Data V E w w) Extra

/-- Raw boolean coordinates of the canonical histogram for the sorted physical stage. -/
noncomputable def word {I Bin : Type} [Fintype I] [Fintype Bin] {level old : ℕ}
    {child : Fin k → PlacedPack D P bits K I old} (stage : Stage m Bin level child)
    (room : ∀ a, stage.matched a < 2^w) (hist : stage.Index e) :
    Words ((I → Deck (level+1)) × Bin) e.count w → Bool :=
  let raw := ((branches e stage.matched room).symm hist).val
  fun z => raw z.1 z.2.1 z.2.2

/-- The selected histogram is recovered at every physical seed and term. -/
theorem word_value {I Bin : Type} [Fintype I] [Fintype Bin] {level old : ℕ}
    {child : Fin k → PlacedPack D P bits K I old} (stage : Stage m Bin level child)
    (room : ∀ a, stage.matched a < 2^w) (hist : stage.Index e) (a : (I → Deck (level+1)) × Bin) (t : Fin e.count) :
    (hist a).val t = value (fun j => word stage room hist (a,t,j)) := by
  let E := branches e stage.matched room
  let g := E.symm hist
  have hv := branches_count e stage.matched room g a t
  change (E g a).val t = _ at hv
  rw [show E g = hist from E.apply_symm_apply hist] at hv
  exact hv

omit [Field K] in
/-- Uniform room for the matched-size words at any installed physical step,
derived from the true expanded cable widths of its input children. -/
theorem room_of_total {I Bin : Type} [Fintype I] [Fintype Bin] {level old : ℕ}
    {child : Fin k → PlacedPack D P bits K I old} (stage : Stage m Bin level child)
    (hm : 0 < m) (W : ℕ) (widths : ∀ i, (∑ z, (child i).pack.layout.width z) ≤ W)
    (fits : k*W < 2^w) : ∀ a, stage.matched a < 2^w := by
  have total : (∑ c, (Normalized.raw child).layout.width c) ≤ k*W := by
    change (∑ c : Σ i, (child i).pack.layout.Edge, (child c.1).pack.layout.width c.2) ≤ _
    rw [Fintype.sum_sigma]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => widths i)
  intro a
  rw [Stage.matched_eq]
  apply (blocks_le_donor _ _ _ hm a).trans_lt
  rw [SeedIntervals.count_eq_sum]
  apply lt_of_le_of_lt _ (total.trans_lt fits)
  exact Finset.sum_le_sum fun z _ => by split <;> first | exact le_rfl | exact Nat.zero_le _

set_option maxHeartbeats 1500000 in
/-- Choose the certified stage at one fixed array of named inputs. The returned
flag and next directory work for all guesses at those very inputs, and each saved
state uses the actual output words. The closure and stage receipts refer to this
same chosen crossing, with the sparse row IDs of the actual child states. -/
theorem install_at_named (hm : 0 < m) (level : lev+1=d+2*src.word) (hk : 0<k)
    (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds)
    (child : Fin k → Child (src := src) (P := P) (bits := bits) (Data := Data)
      (lev := lev) (V := V) (E := E) (w := w) (Extra := Extra))
    (f : Frame ((Fin k × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (PublicDenseReceipt.Seed src.bins lev) e.count w)
      (PublicDenseReceipt.Result src.bins e d src.word k V E seeds w))
    (read : NodeReads src level hk seed (fun i => (child i).placed) (fun i => (child i).names.sites)
      (fun i => (child i).names.cables) (fun i => (child i).names.dummy) (fun z => (child z.1).words z.2) f)
    (W : ℕ) (widths : ∀ i, (∑ z, (child i).placed.pack.layout.width z) ≤ W) (fits : k*W < 2^w) :
    let input := fun i => (child i).placed
    let oldWords := fun z : Fin k × (Fin E ⊕ Raw Data V E w w) => (child z.1).words z.2
    let slot := parallelName (fun i => (child i).names.cables)
    ∃ (sel : src.SelectionAt (d := lev) rfl input hk) (stage : Stage m src.bins.Bin lev input)
      (names : ∀ hist : stage.Index e, Directory (stage.result e hist)
        (siteCapacity e (k*V) seeds) (edgeCapacity e (k*E) seeds)),
      src.ReceiptAt rfl input hk sel ⟨k*E,slot⟩ stage ∧
      (∀ hist, (names hist).sites = siteRows e stage.input (parallelName fun i => (child i).names.sites)
        ((seedLevel level).trans seed).toEmbedding) ∧
      (∀ hist z, ((names hist).cables z).val = stage.cableNumber e ((seedLevel level).trans seed).toEmbedding hist z) ∧
      ∃ room : ∀ a, stage.matched a < 2^w,
        (∀ z, f.eval (Sum.elim oldWords z) (.inr ()) = true ↔ Accepted e stage.matched (fun a t j => z (a,t,j))) ∧
        ∀ hist : stage.Index e,
          let dir := names hist
          let bits' := f.eval (Sum.elim oldWords (word stage room hist)) ∘ Sum.inl
          dir.dense.Reads (src.bins.successorSites src.word e)
            (segmentField (factorEnum D) (src.bins.successorSites src.word e) level) bits' ∧
          PlacedAt (src.bins.successorSites src.word e) h ((stage.result e hist).dense dir.cables) := by
  intro input oldWords slot
  obtain ⟨L,ω,g,dev,⟨R⟩,run⟩ := read
  let stage := src.bins.densePlacedStep input L ω slot g
  let id := (seedLevel level).trans seed
  let dummy := nextDummy e (Normalized.raw input) slot (parallelDummy fun i => (child i).names.dummy) id
  let dir := stage.directory e (parallelName fun i => (child i).names.sites) id.toEmbedding dummy
  let sel : src.Selection input hk := ⟨L,ω,dev⟩
  let room := room_of_total stage hm W widths fits
  refine ⟨sel,stage,dir,⟨R⟩,fun _ => rfl,fun _ _ => rfl,room,fun z => (run z).1,?_⟩
  intro hist
  exact ⟨(run (word stage room hist)).2 hist (word_value stage room hist),
    (R.closure hist).dense (dir hist).cables⟩

set_option maxHeartbeats 1500000 in
/-- The selected histogram guard and saved geometric state on the literal predecessor pins. -/
theorem install_at (hm : 0 < m) (level : lev+1=d+2*src.word) (hk : 0<k)
    (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds)
    (child : Fin k → Child (src := src) (P := P) (bits := bits) (Data := Data)
      (lev := lev) (V := V) (E := E) (w := w) (Extra := Extra))
    (f : Frame ((Fin k × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (PublicDenseReceipt.Seed src.bins lev) e.count w)
      (PublicDenseReceipt.Result src.bins e d src.word k V E seeds w))
    (read : NodeReads src level hk seed (fun i => (child i).placed) (fun i => (child i).names.sites)
      (fun i => (child i).names.cables) (fun i => (child i).names.dummy) (fun z => (child z.1).words z.2) f)
    (W : ℕ) (widths : ∀ i, (∑ z, (child i).placed.pack.layout.width z) ≤ W) (fits : k*W < 2^w) :
    let input := fun i => (child i).placed
    let oldWords := fun z : Fin k × (Fin E ⊕ Raw Data V E w w) => (child z.1).words z.2
    let slot := parallelName (fun i => (child i).names.cables)
    ∃ (sel : src.SelectionAt (d := lev) rfl input hk) (stage : Stage m src.bins.Bin lev input)
      (names : ∀ hist : stage.Index e, Directory (stage.result e hist)
        (siteCapacity e (k*V) seeds) (edgeCapacity e (k*E) seeds)),
      src.ReceiptAt rfl input hk sel ⟨k*E,slot⟩ stage ∧
      ∃ room : ∀ a, stage.matched a < 2^w,
        (∀ z, f.eval (Sum.elim oldWords z) (.inr ()) = true ↔ Accepted e stage.matched (fun a t j => z (a,t,j))) ∧
        ∀ hist : stage.Index e,
          let dir := names hist
          let bits' := f.eval (Sum.elim oldWords (word stage room hist)) ∘ Sum.inl
          dir.dense.Reads (src.bins.successorSites src.word e)
            (segmentField (factorEnum D) (src.bins.successorSites src.word e) level) bits' ∧
          PlacedAt (src.bins.successorSites src.word e) h ((stage.result e hist).dense dir.cables) := by
  obtain ⟨sel,stage,names,receipt,_,_,rest⟩ := install_at_named src hm level hk seed child f read W widths fits
  exact ⟨sel,stage,names,receipt,rest⟩

end PackedHistoryCircuit.Normalized.NamedReceipt

end BorderVNP
end Computability
end OAI
