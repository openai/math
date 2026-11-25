import OAI.ThreeFlat.BitNetwork.OrderedPair
import OAI.ThreeFlat.Diagonal.HistogramAdmissionNet
import OAI.ThreeFlat.Diagonal.HistogramTileNetwork

namespace OAI
/-! # Full local trivalent histogram kernel, including invalid selector words -/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

noncomputable section

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifOuterTerms MotifBinaryPacking MotifOrderedCells TraceCircuit
open scoped BigOperators Classical

variable {J E S H F : Type*} [CommRing F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h : ℕ}
  (D : PortGraph J E) (G : Supply J S) (j : J) (base : E → ℕ)
  (B : Header (D.Port j) H (fun p => base p.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (fits : ∀ z a, sw z (portsAt a).1.1 ≤ d)
  (M : ∀ z v, D.State (fun a => Fin (2^base a)) v → (ports G).State (fun a => Fin (2^sw z a)) v → F)
  (id : H ≃ Fin h) (v : Histogram H r)
  (C : BitNetwork F ((r*d)+(r*d+r*d))) (Ccount : BitNetwork F (r+(r+r)))

noncomputable def partyNetwork := BitNetwork.Ordered.pair (admissionNetwork G j portsAt id B.code Ccount v)
    ((tile D G j base B portsAt sw fits M).network C)

variable (w : E → ℕ) (hpad : ∀ a, w a ≤ base a*r)

def rawHeads (raw : (ports G).Port j → Fin r → Fin (2^k)) (x : D.State (fun a => Fin (2^w a)) j) (i : Fin r) :=
  B.encodeRaw (raw (anchorPort G j) i) (MotifDemandPadding.readSlice D
    (fun a => MotifDemandPadding.digits (w a) (base a) r (hpad a)) i j x)

def boundaryInput (y : (ports G).State (fun a => Fin (2^histWidth sw v a)) j) (a : Fin e) (z : Fin (r*d)) :=
  if hz : z.val < histWidth sw v (portsAt a).1.1 then (word _).symm (y (portsAt a)) ⟨z.val,hz⟩ else false

def partyInputs (x : D.State (fun a => Fin (2^w a)) j)
    (y : (ports G).State (fun a => (Fin r → Fin (2^k)) × Fin (2^histWidth sw v a)) j) :=
  let raw := fun a => (y a).1
  Fin.append (blocks r _ (selectorBits G j portsAt raw)) (arguments (rawHeads D G j base B w hpad raw x)
    (boundaryInput G j portsAt sw v (d:=d) (fun a => (y a).2)))

omit [CommRing F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] in
/-- On a branch whose anchor words are valid, padding the declared fixed
boundary width is the same input as padding the widths decoded from the
actual selected sequence. -/
private theorem packed_header (s : Fin r → H) (x : D.State (fun a => Fin (2^w a)) j)
    (y : (ports G).State (fun a => Fin (2^histWidth sw (histogram s) a)) j) :
    let K := tile D G j base B portsAt sw fits M
    let z := heads D j base B w hpad s x
    let aWord (a : Fin e) : Fin (2^∑ i, K.lengths z a i) := Fin.cast (by
      dsimp [K,z,Tile.lengths,tile,heads]
      simp only [Header.letter_encode]
      exact congrArg (2^ ·) (histogram_width sw s (portsAt a).1.1)) (y (portsAt a))
    K.packedInput z aWord = boundaryInput G j portsAt sw (histogram s) (d:=d) y := by
  dsimp only
  funext a z
  have ha : (∑ i, (tile D G j base B portsAt sw fits M).lengths (heads D j base B w hpad s x) a i) =
      histWidth sw (histogram s) (portsAt a).1.1 := by
    simp only [Tile.lengths,tile,heads,Header.letter_encode]
    exact (histogram_width sw s (portsAt a).1.1).symm
  unfold Tile.packedInput boundaryInput
  by_cases yes : z.val < histWidth sw (histogram s) (portsAt a).1.1
  · rw [dite_eq_left (ha.symm ▸ yes),dite_eq_left yes]; rfl
  · rw [dite_eq_right (ha.symm ▸ yes),dite_eq_right yes]

omit [Fintype J] [Nonempty J] [Fintype E] in
/-- The three required public pin intervals contain per-port selector codes,
each copy's anchor and old digits, and the occupied prefix of each supply
payload. All remaining candidate addresses are literal zeros. -/
theorem party_eval (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y = Routing.StableCompaction.compact M X then 1 else 0)
    (hcount : ∀ M X Y, Ccount.eval (Fin.append M (Fin.append X Y)) = if Y = Routing.StableCompaction.compact M X then 1 else 0)
    (x : D.State (fun a => Fin (2^w a)) j)
    (y : (ports G).State (fun a => (Fin r → Fin (2^k)) × Fin (2^histWidth sw v a)) j) :
    (partyNetwork D G j base B portsAt sw fits M id v C Ccount).eval (partyInputs D G j base B portsAt sw v w hpad x y) =
      histogramKernel D G w base hpad sw B.code M v j x y := by
  rw [partyNetwork,partyInputs,BitNetwork.Ordered.pair_eval,admission_eval _ _ _ _ _ _ _ hcount]
  symm
  apply histogramKernel_admit
  rintro ⟨s,hs⟩ hcode
  subst v
  have headers : rawHeads D G j base B w hpad (fun a => (y a).1) x = heads D j base B w hpad s x := by
    funext i
    have h := (congrFun hcode i).symm
    change (y (anchorPort G j)).1 i = B.code (s i) at h
    simp only [rawHeads,heads,Header.encode,h]
  rw [headers]
  have run := eval_tile D G j base B portsAt sw fits M w hpad s x (fun a => (y a).2) C hC
  dsimp only at run
  rw [packed_header D G j base B portsAt sw fits M w hpad s x (fun a=>(y a).2)] at run
  exact run

end

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
