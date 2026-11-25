import OAI.Hierarchy.ProbeSiteHardware
import OAI.Hierarchy.ProbeHistogramNative

namespace OAI
/-! # Reuse the same finite signed packet entries on the actual site pins -/

noncomputable section
namespace Hierarchy.Probe

open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal MotifBinaryPacking MotifOrderedCells MotifOuterTerms
open scoped Classical BigOperators

variable {K E A : Type*} [Field K] [Fintype E] [Fintype A] {k r b : ℕ}
  [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

def Packet.symbol (P : Packet K edge req) (z : Fin P.selectorBits→Bool) : Fin P.terms :=
  (P.decode (word _ z)).getD ⟨0,NativeHistogram.alphabet_pos P⟩

def Packet.header (P : Packet K edge req) (w : Fin r→Fin P.terms) (j : Fin r) :
    Fin P.selectorBits→Bool := (word _).symm (P.encode (w j))

@[simp] theorem Packet.symbol_header (P : Packet K edge req) (w : Fin r→Fin P.terms) (j : Fin r) :
    P.symbol (P.header w j) = w j := by simp [Packet.symbol,Packet.header]

def Packet.siteTile (P : Packet K edge req) (i : Fin k) :=
  SiteHardware.tile P.symbol
    (SiteHardware.socketWidth (P.width • demandWidths edge req) (fun h=>optionWidths edge (P.count h)) i)
    (SiteHardware.socketValue P.siteMatrices i)

def Packet.siteNetwork (P : Packet K edge req) (i : Fin k) (r : ℕ) :=
  SiteHardware.network (P.siteTile i) r

/-- The input to the signed site network consists of the real selector fields,
followed by the packed words at the old and newly installed sockets. Unused
high bits on each physical socket are canonically zero. -/
def SiteHardware.pins {H V : Type*} [Fintype H] [Fintype V] (width : H→V→ℕ)
    (z : Fin r→Fin b→Bool) (w : Fin r→H) (x : ∀v,Fin (2^∑ j,width (w j) v)) :
    Fin (r*b+Fintype.card V*(r*SiteHardware.widthCap width))→Bool :=
  arguments z (fun e j => let v := (Fintype.equivFin V).symm e
    if h : j.val < ∑ i,width (w i) v then (word _).symm (x v) ⟨j.val,h⟩ else false)

omit [Nonempty (Fin k)] in
theorem SiteHardware.tiled_pins {H : Type*} [Fintype H] (symbol : (Fin b→Bool)→H)
    (a : Widths k) (U : H→Widths k) (M : ∀ h i,State a i→State (U h) i→K)
    (i : Fin k) (z : Fin r→Fin b→Bool) (w : Fin r→H) (decoded : (fun j=>symbol (z j))=w)
    (x : State (∑ _ : Fin r,a) i) (y : State (∑ j,U (w j)) i) :
    let W := SiteHardware.socketWidth a U i
    (SiteHardware.network (SiteHardware.tile symbol W (SiteHardware.socketValue M i)) r).eval
        (SiteHardware.pins W z w (SiteHardware.socketFields a U w i x y)) =
      tiledTable (g:=fun _ : Fin r => a) (fun j=>M (w j)) i x y := by
  subst w
  exact SiteHardware.tiled_eval symbol a U M i z x y

def Packet.sitePins (P : Packet K edge req) (i : Fin k) (w : Fin r→Fin P.terms)
    (x : State (∑ _ : Fin r,P.width • demandWidths edge req) i)
    (y : State (∑ j,optionWidths edge (P.count (w j))) i) :=
  let a := P.width • demandWidths edge req
  let U := fun h => optionWidths edge (P.count h)
  SiteHardware.pins (SiteHardware.socketWidth a U i) (P.header w) w
    (SiteHardware.socketFields a U w i x y)

/-- Actual selected per-site coefficient, with the same one-copy matrices
as the exact histogram sum at every copy and every listed physical port. -/
theorem Packet.eval_site (P : Packet K edge req) (i : Fin k) (w : Fin r→Fin P.terms)
    (x : State (∑ _ : Fin r,P.width • demandWidths edge req) i)
    (y : State (∑ j,optionWidths edge (P.count (w j))) i) :
    (P.siteNetwork i r).eval (P.sitePins i w x y) =
      tiledTable (g:=fun _ : Fin r=>P.width • demandWidths edge req) (fun j=>P.siteMatrices (w j)) i x y :=
  SiteHardware.tiled_pins P.symbol _ _ P.siteMatrices i (P.header w) w
    (funext (P.symbol_header w)) x y

/-- The original ordinary tensor equals the finite histogram expansion in
which every site factor is now the measured value of a trivalent network.
There is one and the same network per site for every hidden selector word. -/
theorem Packet.site_network_identity (P : Packet K edge req) (r : ℕ) :
    let a := P.width • demandWidths edge req
    let U := fun h => optionWidths edge (P.count h)
    ∀ x : ∀ i,State (∑ _ : Fin r,a) i,
      (raw K (∑ _ : Fin r,a)).coeff x =
        ∑ hist : Histogram (Fin P.terms) r, ∑ y : ∀ i,State (installed U hist) i,
          (raw K (installed U hist)).coeff y *
            ∑ u : {w : Fin r→Fin P.terms // histogram w=hist},
              (NativeHistogram.network K (NativeHistogram.alphabet_pos P) P.selectorBits hist).eval
                  ((word (r*P.selectorBits)).symm (P.selectorWord r u.val)) *
                ∏ i,(P.siteNetwork i r).eval (P.sitePins i u.val (x i)
                  (cast (congrArg (fun B => State B i) (word_installed U hist u).symm) (y i))) := by
  dsimp only
  intro x
  refine (P.batch_fixed.choose_spec r x).trans ?_
  apply Finset.sum_congr rfl
  intro hist _
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (_ * ·)
  apply Finset.sum_congr rfl
  intro u _
  simp only [NativeHistogram.broadcast_eval,u.property,ite_true,one_mul,Packet.eval_site]; rfl

/-- Per-site hardware cost at the concrete packet's actual format. -/
theorem Packet.site_cost (P : Packet K edge req) (i : Fin k) (r : ℕ) :
    let d := SiteHardware.widthCap (SiteHardware.socketWidth (P.width • demandWidths edge req)
      (fun h=>optionWidths edge (P.count h)) i)
    let e := Fintype.card (SiteHardware.Sockets i)
    let b := P.selectorBits
    let N := P.siteNetwork i r
    N.cells+N.internal ≤ r*(2^(b+(e*d+e*d))*((b+(e*d+e*d))+2)) + 2*(e*(r*d)) +
      128000*e*(r*d+1)*(Nat.log 2 (r*d+1)+2)^3 :=
  SiteHardware.network_size (P.siteTile i) r


end Hierarchy.Probe
end

end OAI
