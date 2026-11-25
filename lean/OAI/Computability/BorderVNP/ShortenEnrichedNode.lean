import OAI.Computability.BorderVNP.ShortenEnrichedKernelPins
import OAI.Computability.BorderVNP.ShortenPublicNamedOperands

/-!
# Scheduled named-state form of the actual selected combining circuit

The occupied site/cable input and the output use the depth and catalog of
their own schedule level. Equality of public depths and rectangle dimensions
identifies the literal serializer rows. The physical guard and the saved
directory refer to the stage selected from the exact assigned child bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourceTemplate

open Crossing Cover Cover.Frame Cover.AddressCircuit Epoch Hecke Packing Shortening Shortening.Adaptive
open Shortening.PublicRelative Shortening.PublicSegments Shortening.PublicDenseReceipt Shortening.PublicParallel
open Shortening.PreparedBins Shortening.StaticRows BankCircuit NamedKernel
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u v
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ} (src : SourceTemplate e h H ν S)
    {P : Type} {bits : P → ℕ}

/-- A single exact physical stage on canonical named state pins at arbitrary
scheduled levels. All child arrays and directories are supplied literally. -/
def NodeRun {old lev k V E V' E' w : ℕ} (hold : old = lev+2*src.word)
    (hk : 0 < k) (S' : Finset (HyperbolicHost (Cube D))) (widthCap : ℕ)
    (f : Frame ((Fin k × Pins S (old+1) V E w) ⊕ Words (Seed src.bins lev) e.count w)
      (Pins S' (lev+1) V' E' w ⊕ Unit)) : Prop :=
  ∃ seeds : ℕ, ∃ seed : Seed src.bins lev ≃ Fin seeds,
  ∃ O : Operands (Fin k × Pins S (old+1) V E w) (Seed src.bins lev) D (k*E) w,
    O.keyBits = operandBits D src.bins.Bin lev ∧ O.frame.size ≤ f.size ∧
  ∀ {Extra : Type v} (child : Fin k → NamedState D P bits K old V E (Pins S (old+1) V E w) Extra),
    (∀ i, Catalog.PlacedAt S h (child i).placed) →
    (∀ i, (child i).names.Reads S (segmentField (factorEnum D) S rfl) (child i).words) →
    (∀ i, (∑ a, (child i).placed.pack.layout.width a) ≤ widthCap) →
    let input := fun i => (child i).placed
    let oldWords := fun z : Fin k × Pins S (old+1) V E w => (child z.1).words z.2
    let before : CableSlots (raw input) := ⟨k*E,parallelName fun i => (child i).names.cables⟩
    ∃ (sel : src.SelectionAt hold input hk) (s : Stage m src.bins.Bin lev input)
      (dir : ∀ hist : s.Index e, Directory (s.result e hist) V' E'),
      src.ReceiptAt hold input hk sel before s ∧
      (∀ hist v,
        ((dir hist).sites v).val = (siteRows e s.input (parallelName fun i => (child i).names.sites) seed.toEmbedding v).val) ∧
      (∀ hist z, ((dir hist).cables z).val = s.cableNumber e seed.toEmbedding hist z) ∧
      O.OnStage e s (parallelName fun i => (child i).names.sites) before.number seed oldWords ∧
      ∃ room : ∀ a, s.matched a < 2^w,
      (∀ z, f.eval (Sum.elim oldWords z) (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
      ∀ hist : s.Index e, (dir hist).dense.Reads S' (segmentField (factorEnum D) S' rfl)
        (f.eval (Sum.elim oldWords (NamedReceipt.word s room hist)) ∘ Sum.inl)

/-- Install the actual compiled receipt on canonical named pins. It uses the
native stage's exact number of gates and accepts exactly the same word tuples. -/
theorem node_from_native {lev d k V E seeds w widthCap : ℕ} (hm : 0 < m) (hk : 0 < k)
    (level : lev+1=d+2*src.word) (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds)
    {S' : Finset (HyperbolicHost (Cube D))} (hs : S'=src.bins.successorSites src.word e)
    {V' E' : ℕ} (hv : V'=siteCapacity e (k*V) seeds) (he : E'=edgeCapacity e (k*E) seeds)
    (fits : k*widthCap < 2^w)
    (f : Frame ((Fin k × Pins S (lev+2*src.word+1) V E w) ⊕ Words (Seed src.bins lev) e.count w)
      (PublicDenseReceipt.Result src.bins e d src.word k V E seeds w))
    (O : Operands (Fin k × Pins S (lev+2*src.word+1) V E w) (Seed src.bins lev) D (k*E) w)
    (keySize : O.keyBits = operandBits D src.bins.Bin lev) (work : O.frame.size ≤ f.size)
    (native : ∀ {Extra : Type v} (child : Fin k → NamedState D P bits K (lev+2*src.word) V E
        (Pins S (lev+2*src.word+1) V E w) Extra), (∀ i, Catalog.PlacedAt S h (child i).placed) →
      (∀ i, (child i).names.Reads S (segmentField (factorEnum D) S rfl) (child i).words) →
      (∀ i, (∑ a, (child i).placed.pack.layout.width a) ≤ widthCap) →
      OperandNodeReads src O level hk seed (fun i => (child i).placed) (fun i => (child i).names.sites)
        (fun i => (child i).names.cables) (fun i => (child i).names.dummy) (fun z => (child z.1).words z.2) f) :
    ∃ f' : Frame ((Fin k × Pins S (lev+2*src.word+1) V E w) ⊕ Words (Seed src.bins lev) e.count w)
        (Pins S' (lev+1) V' E' w ⊕ Unit),
      f'.size = f.size ∧ NodeRun.{u,v} (P := P) (bits := bits) src rfl hk S' widthCap f' := by
  let back := outputPin (w := w) level hs hv he
  let kernel := scheduled f id back
  refine ⟨kernel,scheduled_size f id back,?_⟩
  refine ⟨seeds,(seedLevel level).trans seed,O,keySize,work.trans_eq (scheduled_size f id back).symm,?_⟩
  intro Extra child prep ready cap
  obtain ⟨sel,s,dir,receipt,sites,cables,operands,room,guard,next⟩ := NamedReceipt.install_operands_at_named src hm level hk seed child O f
    (native child prep ready cap) widthCap cap fits
  let oldWords := fun z : Fin k × Pins S (lev+2*src.word+1) V E w => (child z.1).words z.2
  refine ⟨sel,s,fun q => directoryAt hv he (dir q),receipt,?_,?_,operands,room,?_,?_⟩
  · intro hist v
    exact (directoryAt_site hv he (dir hist) v).trans (congrArg (fun rows => (rows v).val) (sites hist))
  · intro hist z
    exact (directoryAt_cable hv he (dir hist) z).trans (cables hist z)
  · intro z
    have hx : kernel.eval (Sum.elim oldWords z) (.inr ()) = f.eval (Sum.elim oldWords z) (.inr ()) :=
      congrFun (scheduled_eval f id back oldWords z) (.inr ())
    rw [hx]
    exact guard z
  · intro hist
    let z := NamedReceipt.word s room hist
    let data := f.eval (Sum.elim oldWords z) ∘ Sum.inl
    have bitsOut : kernel.eval (Sum.elim oldWords z) ∘ Sum.inl = data ∘ back := by
      funext j
      exact congrFun (scheduled_eval f id back oldWords z) (.inl j)
    rw [bitsOut]
    exact directoryAt_reads level hs hv he (dir hist) data (next hist).1

end PackedHistoryCircuit.Normalized.SourceTemplate

end BorderVNP
end Computability
end OAI
