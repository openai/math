import OAI.Hierarchy.ProbePacketSite
import OAI.Hierarchy.ProbeBroadcastLinks
import OAI.Hierarchy.TaggedWireSiteMatrix

namespace OAI
/-! # Literal broadcast and signed-site matrices on the actual installed states -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open ThreeFlat.Diagonal.MotifBinaryPacking
open WireTelescope
open scoped BigOperators Classical

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
  {k : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

abbrev Packet.inputWidths (P : Packet F edge req) (r : ℕ) := ∑ _ : Fin r,P.width • demandWidths edge req

abbrev Packet.outputWidths (P : Packet F edge req) {r : ℕ} (h : Histogram (Fin P.terms) r) :=
  installed (fun j=>optionWidths edge (P.count j)) h

def Packet.siteEntry (P : Packet F edge req) {r : ℕ} (h : Histogram (Fin P.terms) r)
    (u : {w : Fin r→Fin P.terms // histogram w=h}) (i : Fin k)
    (x : State (P.inputWidths r) i) (y : State (P.outputWidths h) i) : F :=
  (P.siteNetwork i r).eval (P.sitePins i u.val x (cast
    (congrArg (fun B=>State B i) (word_installed (fun j=> optionWidths edge (P.count j)) h u).symm) y))

def Packet.checkEntry (P : Packet F edge req) {r : ℕ} (h : Histogram (Fin P.terms) r)
    (u : {w : Fin r→Fin P.terms // histogram w=h}) : F :=
  (NativeHistogram.network F (NativeHistogram.alphabet_pos P) P.selectorBits h).eval
    ((word (r*P.selectorBits)).symm (P.selectorWord r u.val))

private def allFields (a q : Widths k) :
    (∀i,State (a+q) i) ≃ ((∀i,State a i) × (∀i,State q i)) :=
  (Equiv.piCongrRight (splitPortState a q)).trans (Equiv.arrowProdEquivProdArrow _ _ _)

def Packet.copyCode (P : Packet F edge req) {r : ℕ} (h : Histogram (Fin P.terms) r) :
    {w : Fin r→Fin P.terms // histogram w=h} ↪ Fin (2^(r*P.selectorBits)) :=
  (Function.Embedding.subtype _).trans (P.selectorWord r)

/-- Use the same native histogram checker at the root and the same stable
compaction site LUT at every site. All broadcast sockets read the actual
decoded chord fields. Parallel links have canonical zero padding. -/
def Packet.broadcastMatrix (P : Packet F edge req) (root : Fin k) (r : ℕ)
    (G : PortGraph (Fin k) B) (h : Histogram (Fin P.terms) r) :
    SiteMatrix (State (P.inputWidths r))
      (State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits))) F :=
  let q := G.chordWidths (fun _=>r*P.selectorBits)
  fun i x y =>
    let f := splitPortState (P.outputWidths h) q i y
    ∑ u : {w : Fin r→Fin P.terms // histogram w=h},
      (if f.2=colourState q i (P.copyCode h u) then 1 else 0) *
      ((if i=root then P.checkEntry h u else 1) * P.siteEntry h u i x f.1)

private theorem Packet.branchAction (P : Packet F edge req) (root : Fin k) (r : ℕ)
    (G : PortGraph (Fin k) B) (connected : BroadcastConnected G) (h : Histogram (Fin P.terms) r)
    (x : ∀ i,State (P.inputWidths r) i) :
    let a := P.outputWidths h
    let q := G.chordWidths (fun _=>r*P.selectorBits)
    SiteMatrix.act (P.broadcastMatrix root r G h) (raw F (a+q)).coeff x =
      ∑ y : ∀ i,State a i,(raw F a).coeff y *
        ∑ u : {w : Fin r→Fin P.terms // histogram w=h},P.checkEntry h u * ∏ i,P.siteEntry h u i (x i) (y i) := by
  intro a q
  let W := {w : Fin r→Fin P.terms // histogram w=h}
  let M (y : ∀i,State a i) (i : Fin k) (u : W) :=
    (if i=root then P.checkEntry h u else 1)*P.siteEntry h u i (x i) (y i)
  let T (y : ∀i,State a i) (v : ∀i,State q i) :=
    (raw F a).coeff y * ((raw F q).coeff v *
      ∏i,∑u : W,(if v i=colourState q i (P.copyCode h u) then (1:F) else 0)*M y i u)
  calc
    _ = ∑ z : ((∀ i,State a i) × (∀ i,State q i)),T z.1 z.2 := by
      apply Fintype.sum_equiv (allFields a q)
      intro y
      rw [raw_add_coeff]
      change (_*_) * _ = _ * (_ * _)
      rw [mul_assoc]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      change (∑v,(raw F a).coeff y*_)=_
      rw [←Finset.mul_sum,sum_broadcast (P.copyCode h) q (actual_links G connected _) root (M y)]
      apply congrArg ((raw F a).coeff y * ·)
      apply Finset.sum_congr rfl
      intro u _
      simp only [M,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true]

/-- The same explicit local matrix whose entries run the signed site LUT
and the connected selector test gives the ordinary coefficient identity
before the tensor is placed on the common physical board. -/
theorem Packet.broadcastMatrix_action (P : Packet F edge req) (root : Fin k) (r : ℕ)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (x : ∀ i,State (P.inputWidths r) i) :
    (raw F (P.inputWidths r)).coeff x =
      ∑h : Histogram (Fin P.terms) r, SiteMatrix.act (P.broadcastMatrix root r G h)
        (raw F (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits))).coeff x := by
  refine (P.site_network_identity r x).trans (Finset.sum_congr rfl ?_)
  intro h _
  exact (P.branchAction root r G conn h x).symm

end Hierarchy.Probe
end

end OAI
