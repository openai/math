import OAI.Computability.BorderVNP.PackedHistoryNamedReceipt
import OAI.Computability.BorderVNP.ShortenPublicSelectedOperands

/-! # Installing the selected numerical population and geometry on the same named child states -/

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

set_option maxHeartbeats 1500000 in
/-- Choose the certified stage at one fixed array of named inputs. The returned
flag and next directory work for all guesses at those very inputs, and each saved
state uses the actual output words. The closure and stage receipts refer to this
same chosen crossing, with the sparse row IDs of the actual child states. -/
theorem install_operands_at_named (hm : 0 < m) (level : lev+1=d+2*src.word) (hk : 0<k)
    (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds)
    (child : Fin k → Child (src := src) (P := P) (bits := bits) (Data := Data)
      (lev := lev) (V := V) (E := E) (w := w) (Extra := Extra))
    (O : Operands (Fin k × (Fin E ⊕ Raw Data V E w w)) (Seed src.bins lev) D (k*E) w)
    (f : Frame ((Fin k × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (PublicDenseReceipt.Seed src.bins lev) e.count w)
      (PublicDenseReceipt.Result src.bins e d src.word k V E seeds w))
    (read : OperandNodeReads src O level hk seed (fun i => (child i).placed) (fun i => (child i).names.sites)
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
      O.OnStage e stage (parallelName fun i => (child i).names.sites) slot ((seedLevel level).trans seed) oldWords ∧
      ∃ room : ∀ a, stage.matched a < 2^w,
        (∀ z, f.eval (Sum.elim oldWords z) (.inr ()) = true ↔ Accepted e stage.matched (fun a t j => z (a,t,j))) ∧
        ∀ hist : stage.Index e,
          let dir := names hist
          let bits' := f.eval (Sum.elim oldWords (word stage room hist)) ∘ Sum.inl
          dir.dense.Reads (src.bins.successorSites src.word e)
            (segmentField (factorEnum D) (src.bins.successorSites src.word e) level) bits' ∧
          PlacedAt (src.bins.successorSites src.word e) h ((stage.result e hist).dense dir.cables) := by
  intro input oldWords slot
  obtain ⟨L,ω,g,dev,⟨R⟩,operands,run⟩ := read
  let stage := src.bins.densePlacedStep input L ω slot g
  let id := (seedLevel level).trans seed
  let dummy := nextDummy e (Normalized.raw input) slot (parallelDummy fun i => (child i).names.dummy) id
  let dir := stage.directory e (parallelName fun i => (child i).names.sites) id.toEmbedding dummy
  let sel : src.Selection input hk := ⟨L,ω,dev⟩
  let room := room_of_total stage hm W widths fits
  refine ⟨sel,stage,dir,⟨R⟩,fun _ => rfl,fun _ _ => rfl,operands,room,fun z => (run z).1,?_⟩
  intro hist
  exact ⟨(run (word stage room hist)).2 hist (word_value stage room hist),
    (R.closure hist).dense (dir hist).cables⟩

end PackedHistoryCircuit.Normalized.NamedReceipt

end BorderVNP
end Computability
end OAI
