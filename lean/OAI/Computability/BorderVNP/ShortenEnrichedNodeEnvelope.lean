import OAI.Computability.BorderVNP.ShortenEnrichedNodeFrame

/-! # Row and word budget for an actual scheduled node

The canonical payload uses three Boolean wires per quaternion position and one
tag per finite catalog element. This gives a fixed linear depth bound on its
width. The circuit cost includes its validity flag and all histogram inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourceTemplate

open Crossing Cover Cover.Frame Cover.AddressCircuit Epoch Hecke Packing Shortening Shortening.Adaptive
open Shortening.PublicRelative Shortening.PublicSegments Shortening.PublicDenseReceipt Shortening.PublicParallel
open Shortening.PreparedBins Shortening.StaticRows Shortening.PublicPopulation BankCircuit NamedKernel
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u v
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ} (src : SourceTemplate e h H ν S)

/-- Gates, conjunction, and histogram words of a scheduled combining frame
have one row-volume factor times a fixed power of the logarithmic address
budget. The full named-state receipt is retained for the very same frame. -/
theorem scheduledNode_envelope (hm : 0 < m) :
    ∃ P₀ cut A p : ℕ, 0 < P₀ ∧
      ∀ {P : Type} {bits : P → ℕ} (old lev d k : ℕ) (hold : old=lev+2*src.word)
        (_ : src.floor ≤ lev) (_ : 1 ≤ d) (_ : lev+1=d+2*src.word) (hk : 0<k)
        (_ : cut ≤ old+1) (V E V' E' seeds W w : ℕ) (S' : Finset (HyperbolicHost (Cube D)))
        (_ : S'=src.bins.successorSites src.word e)
        (_ : V'=siteCapacity e (k*V) seeds) (_ : E'=edgeCapacity e (k*E) seeds)
        (_ : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds),
        let vol := Fintype.card (Cube D → Deck (lev+1))
        P₀ < 2^w → k*W < 2^w → packRunWidth vol P₀ k W ≤ w →
        k*V ≤ 2^w → seeds ≤ 2^w → V' ≤ 2^w → E' ≤ 2^w →
        Nat.clog 2 (DirectoryCircuit.widthMultiplier e*(k*W)+1) ≤ w →
        ∃ f : Frame ((Fin k × Pins S (old+1) V E w) ⊕ Words (Seed src.bins lev) e.count w)
          (Pins S' (lev+1) V' E' w ⊕ Unit),
          (∀ T, k*V ≤ T → k*E ≤ T → w ≤ Nat.clog 2 (T+1) →
            f.size+(2*k+4)+Fintype.card (Words (Seed src.bins lev) e.count w) ≤
              (k*V+2*(k*E)+k*(vol+1)+seeds+1)*A*(Nat.clog 2 (T+vol+2)+1)^p) ∧
          NodeRun.{u,v} (P := P) (bits := bits) src hold hk S' W f := by
  obtain ⟨P₀,cut,front,C,p,F,s,hP,make⟩ := scheduledNode_frames.{u,v} src hm
  let q := Fintype.card (Cube D)
  let bins := Fintype.card src.bins.Bin
  let bank := (sitePattern (n := src.word) src.bins).bins
  let G := 90*q+S.card
  obtain ⟨A,z,hcost⟩ := SelectedNodeCost.bound_le front (Fintype.card src.bins.types) bins bank
    e.count q src.word G 1 C p F s
  refine ⟨P₀,cut,A,z,hP,?_⟩
  intro P bits old lev d k hold floor hd level hk hcut V E V' E' seeds W w S' hs hv he seed vol den fits run fitV fitSeed fitV' fitE' hword
  obtain ⟨f,hf,hsem⟩ := make (P := P) (bits := bits) old lev d k hold floor hd level hk hcut
    V E V' E' seeds W w S' hs hv he seed den fits run fitV fitSeed fitV' fitE' hword
  refine ⟨f,?_,hsem⟩
  intro T hV hE hw
  let data := Fintype.card (ProductSlots q (old+1) ⊕ ↥S)
  have payload : data ≤ G*(lev+1+2*src.word+1)^1 := by
    have hr : S.card ≤ S.card*(old+2) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    simp only [data,ProductSlots,StackFrame.Slots,AddressCircuit.width,Fintype.card_sum,
      Fintype.card_prod,Fintype.card_fin,Fintype.card_option,Fintype.card_bool,Fintype.card_coe,G,pow_one]
    rw [show lev+1+2*src.word+1 = old+2 by omega]
    nlinarith only [hr]
  have hseed : Fintype.card (Seed src.bins lev) = seeds := by
    simpa only [Fintype.card_fin] using Fintype.card_congr ((seedLevel level).trans seed)
  have hvol : seeds = vol*bins := by simpa only [Seed,Fintype.card_prod] using hseed.symm
  have hwords : Fintype.card (Words (Seed src.bins lev) e.count w) = seeds*e.count*w := by
    simp only [Words,Fintype.card_prod,Fintype.card_fin,hseed,Nat.mul_assoc]
  obtain ⟨l,hd',hkey,hterms,hh⟩ := hcost k V E w data lev d vol T seeds hV hE hw
    (depth_le_clog_tiles (Cube D) (lev+1)) level payload hvol
  rw [hwords]
  exact (Nat.add_le_add_right (Nat.add_le_add_right (hf T l hE hw hd' hkey hterms) _) _).trans hh

end PackedHistoryCircuit.Normalized.SourceTemplate

end BorderVNP
end Computability
end OAI
