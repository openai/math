import OAI.Computability.BorderVNP.ShortenPublicSegmentLabels
import OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics

/-!
# Sparse reconstruction of charged cable rows from stable site pointers

All cable endpoints are joined to the site table in one sort-and-scan. Each
row then reads a geometric type and its enabled bit. The output forwards the
original site and width fields and both joined endpoints, so the downstream
pack-motion and histogram circuits share the same public join.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Crossing Cover Epoch Catalog PackMotions PreparedBins
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BigOperators

/-- Stable public cable charge flags together with the original site/cable arrays. -/
abbrev Raw (Data : Type*) (V E k w : ℕ) := Fin E ⊕ PublicEndpoints.Inputs Data V E k w

/-- Joined site fields and the original stable charge flags. -/
abbrev Expanded (Data : Type*) (V E k w : ℕ) := Fin E ⊕ PublicEndpoints.Outputs Data V E k w

/-- Output wires for all actual or reserved rows, with the complete expanded input. -/
abbrev Classified (Data T : Type*) (V E k w : ℕ) :=
  Expanded Data V E k w ⊕ Fin E × (Unit ⊕ T)

variable {Data X T : Type*} [Fintype Data] [Fintype X] [Fintype T] {V E k w : ℕ}

/-- One shared endpoint lookup, with the charge flags forwarded to every local row. -/
noncomputable def expand (Data : Type*) [Fintype Data] {V E k : ℕ} (w : ℕ) (fit : V ≤ 2^k) :
    Frame (Raw Data V E k w) (Expanded Data V E k w) :=
  parallelFrame (Frame.initial Sum.inl) ((PublicEndpoints.join Data w fit).subst (Frame.initial Sum.inr))

/-- Projection from the batched public join to the ordered pair of endpoint records.
Other site fields, including private table pointers, remain in the expanded output. -/
def pairAt (field : X → Data) (i : Fin E) (z : Bool × X) : Expanded Data V E k w :=
  .inr (.inr ((i,z.1),field z.2))

/-- An endpoint-derived type and activity bit at every padded cable row. -/
theorem batch_frames (field : X → Data) (f : Frame (Bool × X) T) (fit : V ≤ 2^k) :
    ∃ g : Frame (Raw Data V E k w) (Classified Data T V E k w),
      g.size ≤ 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+Fintype.card Data+1)^3 +
        (1+E*(f.size+2*Fintype.card T+3)) ∧
      ∀ x, let y := (expand Data w fit).eval x
        (∀ j, g.eval x (.inl j) = y j) ∧ ∀ i j, g.eval x (.inr (i,j)) =
          (markRow f).eval (Sum.elim (fun _ => x (.inl i)) (y ∘ pairAt field i)) j := by
  let grab (i : Fin E) : Unit ⊕ Bool × X → Expanded Data V E k w :=
    Sum.elim (fun _ => .inl i) (pairAt field i)
  let row (i : Fin E) := (markRow f).subst (Frame.initial (grab i))
  obtain ⟨bank,hb,he⟩ := exists_parallelFrames row
  let all := (bank.select fun ij : Fin E × (Unit ⊕ T) => ⟨ij.1,ij.2⟩).withInput
  refine ⟨all.subst (expand Data w fit),?_,?_⟩
  · have hbank : bank.size ≤ 1 + E*(markRow f).size := by simpa [row] using hb
    have hjoin := PublicEndpoints.join_size (cables := E) Data w fit
    simp only [all, Frame.subst_size,Frame.withInput_size,Frame.select_size,expand,parallelFrame_size,
      Frame.initial_size,zero_add]
    exact Nat.add_le_add hjoin (hbank.trans (Nat.add_le_add_left (Nat.mul_le_mul_left E (markRow_size f)) 1))
  · intro x y
    refine ⟨fun j => ?_,fun i j => ?_⟩
    · simp [all,y,Frame.subst_eval,Frame.withInput_eval_inl]
    · have hr : (Frame.initial (grab i)).eval y = Sum.elim (fun _ => x (.inl i)) (y ∘ pairAt field i) := by
        funext z
        cases z <;> simp [grab,y,expand]
      simp only [Frame.subst_eval,all,Frame.withInput_eval_inr,Frame.select_eval,he,row,hr,y]

/-- Site-field and width values of the shared expansion. -/
theorem expand_join (fit : V ≤ 2^k) (x : Raw Data V E k w → Bool)
    (j : PublicEndpoints.Outputs Data V E k w) :
    (expand Data w fit).eval x (.inr j) = (PublicEndpoints.join Data w fit).eval (x ∘ Sum.inr) j := by
  have hx : (Frame.initial (Sum.inr : PublicEndpoints.Inputs Data V E k w → Raw Data V E k w)).eval x =
      x ∘ Sum.inr := funext fun _ => by simp
  simp [expand,Frame.subst_eval,hx]

variable {D d : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (site : N.Site ↪ Fin V) (rows : N.Edge ↪ Fin E) (dummy : Fin E → N.Site)
variable (pos : N.Site → SurfaceHost (Cube D) (d+1)) (valid : ∀ v, relative d (pos v) ∈ S)
variable (field : FieldBit (↥S) (Cube D) (d+1) → Data)
variable (x : Raw Data V E k w → Bool) (fit : V ≤ 2^k)
variable (names : PublicEndpoints.Represents N site rows dummy (x ∘ Sum.inr))
variable (payload : ∀ v j, x (.inr (.inl (site v,field j))) = siteBits (pos v) (valid v) j)

set_option maxHeartbeats 1000000

include names payload

/-- For a live cable, both looked-up endpoint records are exactly the canonical
geometry of its ordered ends, including their tie-resolved tile addresses. -/
theorem expanded_occupied (e : N.Edge) : (expand Data w fit).eval x ∘ pairAt field (rows e) =
    endpointBits (pos (N.src e)) (pos (N.dst e)) (valid _) (valid _) := by
  have hj := PublicEndpoints.join_occupied N site rows dummy fit names e
  funext z
  rcases z with ⟨side,j⟩
  cases side
  · change (expand Data w fit).eval x (.inr (.inr ((_,false),field j))) = siteBits _ _ j
    rw [expand_join, hj.2.1 (field j)]
    exact payload _ j
  · change (expand Data w fit).eval x (.inr (.inr ((_,true),field j))) = siteBits _ _ j
    rw [expand_join, hj.1 (field j)]
    exact payload _ j

/-- An unused cable has two reads of the same reserved site, independently
of the stored charge bit. The type reader therefore emits no segment there. -/
theorem expanded_unused (i : Fin E) (hi : i ∉ Set.range rows) :
    let v := dummy (Packing.Names.rowSlot i)
    (expand Data w fit).eval x ∘ pairAt field i = endpointBits (pos v) (pos v) (valid v) (valid v) := by
  have hj := PublicEndpoints.join_unused N site rows dummy fit names i hi
  funext z
  rcases z with ⟨side,j⟩
  cases side
  · change (expand Data w fit).eval x (.inr (.inr ((_,false),field j))) = siteBits _ _ j
    rw [expand_join, hj.2.1 (field j)]
    exact payload _ j
  · change (expand Data w fit).eval x (.inr (.inr ((_,true),field j))) = siteBits _ _ j
    rw [expand_join, hj.1 (field j)]
    exact payload _ j

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
