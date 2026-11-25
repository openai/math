import OAI.Hierarchy.ProbeBatchReplacement
import OAI.Hierarchy.ProbeTreeBroadcast

namespace OAI
/-! # Ordinary field coefficients for installed histogram branches -/

noncomputable section
namespace Hierarchy.Probe

open scoped BigOperators Classical
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open ThreeFlat.CatalyticEmbedding

variable {k : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]
  {edge : E → Chord k} {req : A → E} {B : Type} [Fintype B]

private theorem atPoint {J X K : Type*} [Fintype J] [AddCommMonoid K] (v : J→X→K) (x : X) :
    (∑j,v j) x=∑j,v j x := Finset.sum_apply _ _ _

private theorem physical_enum {X K : Type*} [AddCommMonoid K] (a b : Fintype X) (f : X→K) :
    (@Finset.univ X a).sum f=(@Finset.univ X b).sum f :=
  congrArg (fun e : Fintype X=>(@Finset.univ X e).sum f) (Subsingleton.elim a b)

/-- Each public histogram corresponds to a single ordinary local restriction
on its actual installed widths. The full selector word is transported over
every chosen broadcast link at the stated bit width. The coefficient of this
branch is the sum of the original matrix products over exactly its word fiber. -/
theorem Packet.histogram_physical (P : Packet F edge req) (t : ℕ)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) :
    let a := P.width • demandWidths edge req
    let U (j : Fin P.terms) := optionWidths edge (P.count j)
    let target := ∑ _ : Fin t, a
    ∃ z : Histogram (Fin P.terms) t → (∀ i, State target i) → F,
      (raw F target).coeff = ∑ h, z h ∧ ∀ h,
        ({raw F target with coeff := z h} : Raw (Fin k) F).Restricts
          (raw F (installed U h + G.chordWidths (fun _ => t*P.selectorBits))) := by
  let a := P.width • demandWidths edge req
  let U (j : Fin P.terms) := optionWidths edge (P.count j)
  let target := ∑ _ : Fin t, a
  let M := P.siteMatrices
  have hit := P.batch_fixed.choose_spec
  let Fiber (h : Histogram (Fin P.terms) t) := {w : Fin t → Fin P.terms // histogram w = h}
  let localMap (h : Histogram (Fin P.terms) t) (w : Fiber h) (i : Fin k)
      (x : State target i) (y : State (installed U h) i) :=
    tiledTable (g := fun _ : Fin t => a) (fun j => M (w.1 j)) i x
      (cast (congrArg (fun g => State g i) (word_installed U h w).symm) y)
  let piece (h : Histogram (Fin P.terms) t) (w : Fiber h) (x : ∀ i, State target i) :=
    ∑ y : ∀ i, State (installed U h) i,
      (raw F (installed U h)).coeff y * ∏ i, localMap h w i (x i) (y i)
  refine ⟨fun h => ∑ w, piece h w,?_,?_⟩
  · funext x
    refine (hit t x).trans (?_ : _ = (∑ h,∑ w,piece h w) x)
    rw [atPoint (fun h=>∑w,piece h w) x]
    apply Finset.sum_congr rfl
    intro h _
    rw [atPoint (piece h) x]
    change (∑ y : ∀ i, State (installed U h) i, (raw F (installed U h)).coeff y *
      (∑ w : Fiber h, ∏ i, localMap h w i (x i) (y i))) = _
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  · intro h
    let code : Fiber h ↪ Fin (2^(t*P.selectorBits)) :=
      ⟨fun w => P.selectorWord t w.val,fun _ _ eq => Subtype.ext ((P.selectorWord t).injective eq)⟩
    apply sum_restricts_broadcast G conn code (piece h)
    intro w
    refine ⟨localMap h w,fun x => ?_⟩
    unfold piece
    exact physical_enum _ _ _

/-- Local balls may be enumerated by increasing common-site name. The
result is an ordinary coefficient identity in the common ambient format,
with one actual restricted tensor per public histogram. -/
theorem Packet.named_histogram {S : ℕ} [Nonempty (Fin S)] (P : Packet F edge req) (t : ℕ)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (place : Fin k ↪o Fin S) :
    let target := ∑ _ : Fin t, P.width • demandWidths edge req
    let U (j : Fin P.terms) := optionWidths edge (P.count j)
    ∃ z : Histogram (Fin P.terms) t → (∀ i, State (push place target) i) → F,
      (raw F (push place target)).coeff = ∑ h, z h ∧ ∀ h,
        ({raw F (push place target) with coeff := z h} : Raw (Fin S) F).Restricts
          (raw F (push place (installed U h + G.chordWidths (fun _ => t*P.selectorBits)))) := by
  obtain ⟨z,hz,tiles⟩ := P.histogram_physical t G conn
  exact named_sum place _ _ z hz tiles


end Hierarchy.Probe
end

end OAI
