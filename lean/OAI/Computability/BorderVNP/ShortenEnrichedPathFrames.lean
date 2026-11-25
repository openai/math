import OAI.Computability.BorderVNP.ShortenEnrichedNodeEnvelope
import OAI.Computability.BorderVNP.ShortenEnrichedNamedPath

/-! # Selecting the actual frame family of a prepared shortening path

The finite source path fixes its denominators, decoding cutoffs and a common
cost coefficient and exponent. Once the scheduled public rectangles and word
width satisfy their arithmetic ranges, each stage has one named frame. The
frame is selected before any child assignment or histogram word is given.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath

open Crossing Cover Cover.Frame Cover.AddressCircuit Epoch Hecke Packing Shortening Shortening.Adaptive
open Shortening.PublicRelative Shortening.PublicSegments Shortening.PublicDenseReceipt Shortening.PublicParallel
open Shortening.PreparedBins Shortening.StaticRows BankCircuit NamedKernel
open scoped Classical BorderVNP.Epoch.Cube

universe u v
variable {D m b : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {h H ν : ℝ} (p : SourcePath b e h H ν)

/-- The seed directory at a scheduled node contains all absolute tile and
relative bin pairs. -/
noncomputable def stageSeeds (last high : ℕ) (i : Fin b) : ℕ :=
  Fintype.card (Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1)))

/-- The public depth and integer range conditions of one scheduled physical
node, including the exact next rectangle allocated for its full seed list. -/
structure NodeRange (last high k : ℕ) (V E : ℕ → ℕ) (W : Fin b → ℕ) (w : ℕ)
    (i : Fin b) (den cut : ℕ) : Prop where
  /-- The positive auxiliary depth used by the prepared motion. -/
  depth : ∃ d, 1 ≤ d ∧ p.asPath.depth last high (i.val+1)+1 = d+2*(p.pattern i).word
  /-- The input pack meets the geometric floor of its preparation. -/
  floor : (p.pattern i).floor ≤ p.asPath.depth last high (i.val+1)
  /-- The deep input address meets the decoder cutoff. -/
  cutoff : cut ≤ p.asPath.depth last high i.val+1
  /-- Site identifiers of the saved successor. -/
  sites : V (i.val+1) = siteCapacity e (k*V i.val) (p.stageSeeds last high i)
  /-- Cable identifiers of the saved successor. -/
  cables : E (i.val+1) = edgeCapacity e (k*E i.val) (p.stageSeeds last high i)
  /-- The finite candidate denominator, input width and selector score fit. -/
  counts : den < 2^w ∧ k*W i < 2^w ∧
    packRunWidth (Fintype.card (Cube D → Deck (p.asPath.depth last high (i.val+1)+1))) den k (W i) ≤ w
  /-- Both public rectangles, the seed list and the multiplied cable population fit. -/
  pointers : k*V i.val ≤ 2^w ∧ p.stageSeeds last high i ≤ 2^w ∧ V (i.val+1) ≤ 2^w ∧ E (i.val+1) ≤ 2^w ∧
    Nat.clog 2 (DirectoryCircuit.widthMultiplier e*(k*W i)+1) ≤ w

/-- The envelope used for one complete node, including the child validity
conjunction and all guessed histogram words. -/
noncomputable def nodeRows (last high k : ℕ) (V E : ℕ → ℕ) (i : Fin b) : ℕ :=
  k*V i.val + 2*(k*E i.val) +
    k*(Fintype.card (Cube D → Deck (p.asPath.depth last high (i.val+1)+1))+1) + p.stageSeeds last high i+1

/-- Compile every stage of a finite source path once on its named public pins.
All compiler thresholds precede the varying cover level and the actual table
capacities. Each compiled frame has both the measured source semantics and
the common polylogarithmic gate-and-word envelope. -/
theorem pathNode_frames (hm : 0 < m) :
    ∃ (den cut : Fin b → ℕ) (A z : ℕ), (∀ i, 0 < den i) ∧
      ∀ {P : Type} {bits : P → ℕ} (last high k : ℕ) (hk : 0 < k)
        (V E : ℕ → ℕ) (W : Fin b → ℕ) (w : ℕ),
        (∀ i, p.NodeRange last high k V E W w i (den i) (cut i)) →
        ∃ nodes : ∀ i : Fin b, p.Node last high V E w k i,
          (∀ i, SourceTemplate.NodeRun.{u,v} (P := Port k P i.val) (bits := width bits k i.val)
            (p.pattern i) (p.stepDepth last high i) hk (p.catalog (i.val+1)) (W i) (nodes i)) ∧
          ∀ i T, k*V i.val ≤ T → k*E i.val ≤ T → w ≤ Nat.clog 2 (T+1) →
            let vol := Fintype.card (Cube D → Deck (p.asPath.depth last high (i.val+1)+1))
            (nodes i).size + (2*k+4) + Fintype.card (Words (Seed (p.pattern i).bins
              (p.asPath.depth last high (i.val+1))) e.count w) ≤
              p.nodeRows last high k V E i * A * (Nat.clog 2 (T+vol+2)+1)^z := by
  choose den cut C e' hden make using fun i : Fin b => SourceTemplate.scheduledNode_envelope.{u,v} (p.pattern i) hm
  let A := Finset.univ.sup C
  let z := Finset.univ.sup e'
  refine ⟨den,cut,A,z,hden,?_⟩
  intro P bits last high k hk V E W w ranges
  let level := p.asPath.depth last high
  have one (i : Fin b) : ∃ f : p.Node last high V E w k i,
      SourceTemplate.NodeRun.{u,v} (P := Port k P i.val) (bits := width bits k i.val)
        (p.pattern i) (p.stepDepth last high i) hk (p.catalog (i.val+1)) (W i) f ∧
      ∀ T, k*V i.val ≤ T → k*E i.val ≤ T → w ≤ Nat.clog 2 (T+1) →
        let vol := Fintype.card (Cube D → Deck (level (i.val+1)+1))
        f.size+(2*k+4)+Fintype.card (Words (Seed (p.pattern i).bins (level (i.val+1))) e.count w) ≤
          p.nodeRows last high k V E i*A*(Nat.clog 2 (T+vol+2)+1)^z := by
    have r := ranges i
    obtain ⟨d,hd,hl⟩ := r.depth
    let seed := (seedLevel (A := (p.pattern i).bins.Bin) hl).symm.trans
      (Fintype.equivFin (Seed (p.pattern i).bins (level (i.val+1))))
    obtain ⟨dencap,total,score⟩ := r.counts
    obtain ⟨sites,seedcap,outSites,outEdges,charge⟩ := r.pointers
    obtain ⟨f,hcost,hsem⟩ := make i (P := Port k P i.val) (bits := width bits k i.val)
      (level i.val) (level (i.val+1)) d k (p.stepDepth last high i) r.floor hd hl hk r.cutoff
      (V i.val) (E i.val) (V (i.val+1)) (E (i.val+1)) (p.stageSeeds last high i) (W i) w
      (p.catalog (i.val+1)) (p.next i) r.sites r.cables seed dencap total score sites seedcap outSites outEdges charge
    refine ⟨f,hsem,?_⟩
    intro T hV hE hw vol
    have hc : C i ≤ A := Finset.le_sup (Finset.mem_univ i)
    have he : e' i ≤ z := Finset.le_sup (Finset.mem_univ i)
    apply (hcost T hV hE hw).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left (p.nodeRows last high k V E i) hc)
      (Nat.pow_le_pow_right (Nat.succ_pos _) he)
  choose nodes semantics costs using one
  exact ⟨nodes,semantics,costs⟩

end PackedHistoryCircuit.Normalized.SourcePath

end BorderVNP
end Computability
end OAI
