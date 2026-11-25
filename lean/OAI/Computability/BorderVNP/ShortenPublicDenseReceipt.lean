import OAI.Computability.BorderVNP.ShortenPublicSelectedOperands

/-!
# The selected dense receipt and its saved physical successor on one circuit

A fixed Boolean circuit consumes the separate old pack rectangles and the
physical profile count guesses. Its chosen stage is fixed by the old wires
before any guessed count is read. On every accepted count tuple it produces
the full occupied public table of the actual saved dense successor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDenseReceipt

open Cover Cover.Frame Cover.AddressCircuit Hecke Crossing Epoch Catalog StaticRows CombiningStep
open PreparedBins Framed PublicSegments PublicRelative PublicPopulation PublicParallel
open Packing DirectoryCircuit PublicDirectory BankCircuit VPVNP.VerifierNetwork ParseBatchSort
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ} (src : SourceTemplate e h H ν S)

/-- The common stage is chosen using only the physical child tables. It
works for every word tuple on those same tables. -/
def NodeReads {lev d copies V E seeds w : ℕ} {Data P : Type} [Fintype Data] {bits : P → ℕ}
    (level : lev+1=d+2*src.word) (hk : 0<copies)
    (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds)
    (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*src.word))
    (site : ∀ i, (child i).pack.layout.Site ↪ Fin V) (row : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
    (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
    (x : Fin copies × (Fin E ⊕ Raw Data V E w w) → Bool)
    (f : Frame ((Fin copies × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (Seed src.bins lev) e.count w)
      (Result src.bins e d src.word copies V E seeds w)) : Prop :=
  let old := parallelName site
  let slot := parallelName row
  let physSeed := (seedLevel level).trans seed
  let hole := nextDummy e (raw child) slot (parallelDummy dummy) physSeed
  ∃ (L : Labels src.bins (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (lev+1) src.word)
    (g : src.bins.DensePlacement child L ω slot m),
    let s := src.bins.densePlacedStep child L ω slot g
    src.bins.SampleDeviation child L ω hk src.motion ∧
    Nonempty (src.bins.DenseReceipt e child L ω slot s hk H ν src.mean src.motion src.record) ∧
    ∀ z : Words (Seed src.bins lev) e.count w → Bool,
      let y := f.eval (Sum.elim x z)
      (y (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
      ∀ hist : s.Index e, (∀ a t, (hist a).val t = value (fun j => z (a,t,j))) →
        (s.directory e old physSeed.toEmbedding hole hist).dense.Reads (src.bins.successorSites src.word e)
          (segmentField (factorEnum D) (src.bins.successorSites src.word e) level) (y ∘ Sum.inl)

set_option maxHeartbeats 2100000 in
/-- Compile a complete measured combining node. All constants precede its
level, fan-in, name capacities, port type and count width. The same selected
dense receipt covers every accepted profile from this input. -/
theorem selectedReceipt_frames (hm : 0 < m) :
    ∃ P₀ cut : ℕ, ∃ front : FrontCosts, ∃ C p F s : ℕ, 0<P₀ ∧
      ∀ {P : Type} {bits : P → ℕ} (lev d copies : ℕ) (_ : src.floor ≤ lev) (_ : 1 ≤ d)
        (level : lev+1=d+2*src.word) (hk : 0<copies) (_ : cut ≤ lev+1+2*src.word)
        {Data : Type} [Fintype Data] (V E seeds W w : ℕ)
        (field : FieldBit (↥S) (Cube D) (lev+2*src.word+1) → Data)
        (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds),
        let vol := Fintype.card (Cube D → Deck (lev+1))
        let q := Fintype.card (Cube D)
        P₀ < 2^w → W < 2^w → packRunWidth vol P₀ copies W ≤ w →
        copies*V ≤ 2^w → seeds ≤ 2^w → siteCapacity e (copies*V) seeds ≤ 2^w → edgeCapacity e (copies*E) seeds ≤ 2^w →
        Nat.clog 2 (widthMultiplier e*(copies*W)+1) ≤ w →
        ∃ f : Frame ((Fin copies × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (Seed src.bins lev) e.count w)
          (Result src.bins e d src.word copies V E seeds w),
          (∀ T l, copies*E ≤ T → w ≤ Nat.clog 2 (T+1) → d+1 ≤ l →
            Nat.clog 2 (seeds+copies*E)+(Nat.clog 2 (Fintype.card src.bins.Bin)+keyWidth q (d+2*src.word))+w+1 ≤ l →
            w+Nat.clog 2 (e.count+1)+1 ≤ l →
            f.size ≤ front.bound copies V E w (Fintype.card Data) (Fintype.card src.bins.types) q
              (lev+1) src.word vol T +
              ((1+copies*E*(C*(d+1)^p)+copies*E*Nat.clog 2 (Fintype.card src.bins.Bin)*(2*Fintype.card src.bins.Bin+1)+1) +
                seeds*((sitePattern (n := src.word) src.bins).bins+90*q*(d+2*src.word+1)) +
                (copies*V+copies*E+seeds+1)*F*l^s)) ∧
          ∀ (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*src.word))
            (site : ∀ i, (child i).pack.layout.Site ↪ Fin V) (row : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
            (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
            (x : Fin copies × (Fin E ⊕ Raw Data V E w w) → Bool),
            (∀ i, Catalog.PlacedAt S h (child i)) →
            (∀ i j, x (i,.inl j) = true ↔ j ∈ Set.range (row i)) →
            (∀ i, SegmentReady S (child i).pack.layout (site i) (row i) (dummy i) (child i).site field
              (child i).charged (fun j => x (i,.inr j))) →
            (∀ i, (∑ c, (child i).pack.layout.width c) ≤ W) →
            NodeReads src level hk seed child site row dummy x f := by
  obtain ⟨P₀,cut,cost,C,p,F,s,hP,build⟩ := selectedOperands_frames src hm
  refine ⟨P₀,cut,cost,C,p,F,s,hP,?_⟩
  intro P bits lev d copies hd hr level hk hc Data instData V E seeds W w field seed vol q den fit run fitV hn hs he wfits
  obtain ⟨_,f,_,_,size,sem⟩ := build (P:=P) (bits:=bits) lev d copies hd hr level hk hc
    V E seeds W w field seed den fit run fitV hn hs he wfits
  refine ⟨f,size,?_⟩
  intro child site row dummy x good present ready cap
  obtain ⟨L,ω,g,dev,receipt,_,output⟩ := sem child site row dummy x good present ready cap
  exact ⟨L,ω,g,dev,receipt,output⟩

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
