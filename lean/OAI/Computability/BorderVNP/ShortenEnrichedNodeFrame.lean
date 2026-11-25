import OAI.Computability.BorderVNP.ShortenEnrichedNode
import OAI.Computability.BorderVNP.PackedSelectedNodeCost

/-! # Compiling a scheduled node on the actual named child arrays

The dense-receipt circuit reads the canonical product tile and catalog fields
from the children's stored pins. Reindexing its outputs to the scheduled
successor rectangle preserves the gate count, the selected receipt, and the
accepted history words.
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

/-- A single choice of compiler constants covers every scheduled depth and
rectangle. The circuit reads the supplied named predecessor words and returns
the scheduled-node semantics for all accepted histograms, with precisely the
native front-end and dense serializer gate bound. -/
theorem scheduledNode_frames (hm : 0 < m) :
    ∃ P₀ cut : ℕ, ∃ front : FrontCosts, ∃ C p F s : ℕ, 0 < P₀ ∧
      ∀ {P : Type} {bits : P → ℕ} (old lev d k : ℕ) (hold : old=lev+2*src.word)
        (_ : src.floor ≤ lev) (_ : 1 ≤ d) (_ : lev+1=d+2*src.word) (hk : 0<k)
        (_ : cut ≤ old+1) (V E V' E' seeds W w : ℕ) (S' : Finset (HyperbolicHost (Cube D)))
        (_ : S'=src.bins.successorSites src.word e)
        (_ : V'=siteCapacity e (k*V) seeds) (_ : E'=edgeCapacity e (k*E) seeds)
        (_ : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds),
        let vol := Fintype.card (Cube D → Deck (lev+1))
        let q := Fintype.card (Cube D)
        let data := Fintype.card (ProductSlots q (old+1) ⊕ ↥S)
        P₀ < 2^w → k*W < 2^w → packRunWidth vol P₀ k W ≤ w →
        k*V ≤ 2^w → seeds ≤ 2^w → V' ≤ 2^w → E' ≤ 2^w →
        Nat.clog 2 (DirectoryCircuit.widthMultiplier e*(k*W)+1) ≤ w →
        ∃ f : Frame ((Fin k × Pins S (old+1) V E w) ⊕ Words (Seed src.bins lev) e.count w)
          (Pins S' (lev+1) V' E' w ⊕ Unit),
          (∀ T l, k*E ≤ T → w ≤ Nat.clog 2 (T+1) → d+1 ≤ l →
            Nat.clog 2 (seeds+k*E)+(Nat.clog 2 (Fintype.card src.bins.Bin)+keyWidth q (d+2*src.word))+w+1 ≤ l →
            w+Nat.clog 2 (e.count+1)+1 ≤ l →
            f.size ≤ front.bound k V E w data (Fintype.card src.bins.types) q (lev+1) src.word vol T +
              SelectedNodeCost.backend (Fintype.card src.bins.Bin) ((sitePattern (n := src.word) src.bins).bins)
                q src.word C p F s k V E seeds d l) ∧
          NodeRun.{u,v} (P := P) (bits := bits) src hold hk S' W f := by
  obtain ⟨P₀,cut,front,C,p,F,s,hP,make⟩ := selectedOperands_frames src hm
  refine ⟨P₀,cut,front,C,p,F,s,hP,?_⟩
  intro P bits old lev d k hold floor hd level hk hcut V E V' E' seeds W w S' hs hv he seed
  subst old
  intro vol q data hden fits run fitsV fitsSeed fitsV' fitsE' hword
  let Data := ProductSlots q (lev+2*src.word+1) ⊕ ↥S
  let field := segmentField (factorEnum D) S (lev := lev+2*src.word) rfl
  have hw : W < 2^w := (Nat.le_mul_of_pos_left W hk).trans_lt fits
  obtain ⟨O,native,keySize,oldCost,cost,reads⟩ := make (P := P) (bits := bits) lev d k floor hd level hk (by omega)
    (Data := Data) V E seeds W w field seed hden hw run fitsV fitsSeed (hv ▸ fitsV') (he ▸ fitsE') hword
  obtain ⟨f,hsize,hsem⟩ := node_from_native.{u,v} (P := P) (bits := bits) src hm hk level seed
    hs hv he fits native O keySize oldCost (by
      intro Extra child prep ready cap
      exact reads (fun i => (child i).placed) (fun i => (child i).names.sites) (fun i => (child i).names.cables)
        (fun i => (child i).names.dummy) (fun z => (child z.1).words z.2) prep
        (fun i => (ready i).present) (fun i => (ready i).geometry) cap)
  refine ⟨f,?_,hsem⟩
  intro T l hE hW hD hL hG
  rw [hsize]
  exact cost T l hE hW hD hL hG

end PackedHistoryCircuit.Normalized.SourceTemplate

end BorderVNP
end Computability
end OAI
