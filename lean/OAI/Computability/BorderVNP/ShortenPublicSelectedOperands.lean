import OAI.Computability.BorderVNP.ShortenPublicDenseReceiptBackend
import OAI.Computability.BorderVNP.ShortenPublicSelectedFront
import OAI.Computability.BorderVNP.ShortenCompiledSourceTemplate
import OAI.Computability.BorderVNP.ShortenPublicDenseOperands

/-! # Physical old-cable operands of the same selected geometric successor -/

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
def OperandNodeReads {lev d copies V E seeds w : ℕ} {Data P : Type} [Fintype Data] {bits : P → ℕ}
    (O : Operands (Fin copies × (Fin E ⊕ Raw Data V E w w)) (Seed src.bins lev) D (copies*E) w)
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
    O.OnStage e s old slot physSeed x ∧
    ∀ z : Words (Seed src.bins lev) e.count w → Bool,
      let y := f.eval (Sum.elim x z)
      (y (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
      ∀ hist : s.Index e, (∀ a t, (hist a).val t = value (fun j => z (a,t,j))) →
        (s.directory e old physSeed.toEmbedding hole hist).dense.Reads (src.bins.successorSites src.word e)
          (segmentField (factorEnum D) (src.bins.successorSites src.word e) level) (y ∘ Sum.inl)

omit [NeZero D] [Field K] in
private theorem parallel_width {copies prior W : ℕ} {P : Type} {bits : P → ℕ}
    (child : Fin copies → PlacedPack D P bits K (Cube D) prior) (cap : ∀ i, (∑ c, (child i).pack.layout.width c) ≤ W) :
    (∑ c, (raw child).layout.width c) ≤ copies*W := by
  change (∑ c : Σ i, (child i).pack.layout.Edge, (child c.1).pack.layout.width c.2) ≤ _
  rw [Fintype.sum_sigma]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => cap i)

set_option maxHeartbeats 2100000 in
/-- Compile a complete measured combining node. All constants precede its
level, fan-in, name capacities, port type and count width. The same selected
dense receipt covers every accepted profile from this input. -/
theorem selectedOperands_frames (hm : 0 < m) :
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
        ∃ O : Operands (Fin copies × (Fin E ⊕ Raw Data V E w w)) (Seed src.bins lev) D (copies*E) w,
        ∃ f : Frame ((Fin copies × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (Seed src.bins lev) e.count w)
          (Result src.bins e d src.word copies V E seeds w),
          O.keyBits = operandBits D src.bins.Bin lev ∧ O.frame.size ≤ f.size ∧
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
            OperandNodeReads src O level hk seed child site row dummy x f := by
  obtain ⟨P₀,cut,cost,hP,select⟩ := selectedFront_frames src.bins src.compiled
  obtain ⟨C,p,F,s,build⟩ := backend_table_frames src.bins e hm src.word
  refine ⟨P₀,cut,cost,C,p,F,s,hP,?_⟩
  intro P bits lev d copies hd hr level hk hc Data instData V E seeds W w field seed vol q den fit run fitV hn hs he wfits
  obtain ⟨front,fs,fr⟩ := select lev d copies (src.floor_pos.trans_le hd) hr level hk hc V E W w field den fit run fitV
  obtain ⟨pf,back,pfs,exposes,bs,br⟩ := build (P := P) (bits := bits) d lev copies V E seeds w hr level Data field seed hn hs he
  let O : Operands (Fin copies × (Fin E ⊕ Raw Data V E w w)) (Seed src.bins lev) D (copies*E) w :=
    ⟨NumericTable src.bins Data d src.word copies V E w,inferInstance,numericWidth src.bins d src.word,
      pf.subst front,numericPins src.bins d src.word copies V E w level field,numericColumns src.bins Data d src.word copies V E w,
      numericCode src.bins level,CanonicalPlacement.perm (fun t : src.bins.types => t.val.radius) src.bins.chart⟩
  let node := (back.subst (withWords front)).select Sum.inr
  refine ⟨O,node,?_,?_,?_,?_⟩
  · change numericWidth src.bins d src.word = operandBits D src.bins.Bin lev
    unfold numericWidth operandBits
    rw [level]
  · change (pf.subst front).size ≤ node.size
    simpa only [node,Frame.select_size,Frame.subst_size,withWords_size] using Nat.add_le_add_left pfs front.size
  · intro T l hE hW hD hL hG
    rw [show node.size=front.size+back.size by simp [node,withWords_size]]
    exact Nat.add_le_add (fs T hE hW) (bs l hD hL hG)
  intro child site row dummy x good present ready cap
  obtain ⟨occ,old,cls,L,ω,occTrue,saved,labels,dev,sampled⟩ :=
    fr child site row dummy x present ready (fun i => (good i).short) (fun i => (good i).midpoint) cap
  obtain ⟨stage,⟨receipt⟩⟩ := src.run_selected lev hd hk child good L ω (parallelName row) dev
  let trace := receipt.trace
  have certified (z : Words (Seed src.bins lev) e.count w → Bool) := br child site row dummy occ old cls L ω occTrue saved labels (copies*W) (parallel_width child cap)
    wfits trace.geometry trace.moved trace.chart trace.project z
  refine ⟨L,ω,trace.geometry,dev,⟨trace.realizes ▸ receipt⟩,⟨rfl,nextDummy e (raw child) (parallelName row) (parallelDummy dummy) ((seedLevel level).trans seed),?_⟩,?_⟩
  · have z0 := fun _ : Words (Seed src.bins lev) e.count w => false
    have old := (certified z0).1
    rw [exposes] at old
    change Ready e _ _ _ _ _ _ _ _ _ _ ((pf.subst front).eval x)
    have join : (pf.subst front).eval x = pf.eval (front.eval x) := funext fun j => Frame.subst_eval pf front x j
    rw [join,sampled]
    exact old
  · intro z
    have hx : node.eval (Sum.elim x z) = back.eval (Sum.elim (front.eval x) z) ∘ Sum.inr := by
      funext j
      simp only [node,Frame.select_eval,Frame.subst_eval,withWords_eval,Function.comp_apply]
    rw [hx,sampled]
    exact (certified z).2

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
