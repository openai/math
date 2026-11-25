import OAI.Hierarchy.ProbeArbitraryPlacement
import OAI.Hierarchy.ProbeHistogramPhysical
import OAI.Hierarchy.TaggedWireExpansion

namespace OAI
/-! # A fixed signed packet on any order of its actual physical sites -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {k : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]
    {edge : E→Chord k} {req : A→E} {B : Type} [Fintype B]

theorem Packet.physical_histogram {S : ℕ} [Nonempty (Fin S)] (P : Packet F edge req) (t : ℕ)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (place : Fin k ↪ Fin S) :
    let target := ∑ _ : Fin t, P.width • demandWidths edge req
    let U (j : Fin P.terms) := optionWidths edge (P.count j)
    ∃ z : Histogram (Fin P.terms) t → (∀ i, State (placeWidths place target) i) → F,
      (raw F (placeWidths place target)).coeff = ∑ h, z h ∧ ∀ h,
        ({raw F (placeWidths place target) with coeff := z h} : Raw (Fin S) F).Restricts
          (raw F (placeWidths place (installed U h + G.chordWidths (fun _ => t*P.selectorBits)))) := by
  obtain ⟨z,hz,tiles⟩ := P.histogram_physical t G conn
  exact arbitrary_sum place _ _ z hz tiles


end Hierarchy.Probe

namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms Probe
open scoped Classical BigOperators
variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
    {k S : ℕ} [Nonempty (Fin k)] [Nonempty (Fin S)] {edge : E → Chord k} {req : A → E}

def physicalPacket (P : Packet F edge req) (t : ℕ) (G : PortGraph (Fin k) B)
    (conn : BroadcastConnected G) (place : Fin k ↪ Fin S) :
    Expansion (raw F (placeWidths place (∑ _ : Fin t,P.width • demandWidths edge req)))
      (Histogram (Fin P.terms) t) (fun h=>placeWidths place
        (installed (fun j=>optionWidths edge (P.count j)) h + G.chordWidths (fun _=>t*P.selectorBits))) :=
  let result := P.physical_histogram t G conn place
  ⟨result.choose,result.choose_spec.1,result.choose_spec.2⟩

omit [Fintype E] [Nonempty (Fin S)] [Nonempty (Fin k)] in
/-- Repeated demand occurrences remain separate in the source bank. Each
gets `copies*width` physical bits, including repeated commodity keys. -/
theorem physical_demand (place : Fin k ↪ Fin S) (width copies : ℕ) :
    placeWidths place (∑ _ : Fin copies,width • demandWidths edge req) =
      optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>copies*width) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,demandWidths,optionWidths,map_sum,place_single,Finset.smul_sum,Finsupp.smul_single,
    smul_eq_mul,Nat.mul_one,Function.comp_apply]

omit [Nonempty (Fin S)] [Nonempty (Fin k)] in
/-- The per-option widths in a placed physical branch are the integer
histogram dot products returned for that same option by `Batch.wire`. -/
theorem physical_histogram_width (P : Packet F edge req) {copies : ℕ}
    (h : Histogram (Fin P.terms) copies) (place : Fin k ↪ Fin S) :
    placeWidths place (installed (fun j=>optionWidths edge (P.count j)) h) =
      optionWidths (fun e=>physicalChord place (edge e)) (histWidth P.count h) := by
  simp only [installed,optionWidths,map_sum,place_single,histWidth,
    Finset.smul_sum,Finsupp.smul_single,Finsupp.single_finsetSum,smul_eq_mul]
  rw [Finset.sum_comm]

def physicalPacket_on_rows (P : Packet F edge req) (copies : ℕ) (G : PortGraph (Fin k) B)
    (conn : BroadcastConnected G) (place : Fin k ↪ Fin S) :
    Expansion (raw F (optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>copies*P.width)))
      (Histogram (Fin P.terms) copies) (fun h=>
        optionWidths (fun e=>physicalChord place (edge e)) (histWidth P.count h) +
          placeWidths place (G.chordWidths (fun _=>copies*P.selectorBits))) := by
  have H := physicalPacket P copies G conn place
  simpa only [physical_demand, map_add,physical_histogram_width] using H


end Hierarchy.WireTelescope
end

end OAI
