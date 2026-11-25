import OAI.Computability.BorderVNP.ShortenPublicDenseReceipt
import OAI.Computability.BorderVNP.ShortenPublicSelectedFrontCost

/-!
# Size of a selected combining node

The selector, the dense successor directory, the conjunction of child flags,
and every physical histogram input fit one linear row-count factor times a
polynomial in the address length. The coefficients depend on the prepared
stage and on the permitted polynomial payload width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SelectedNodeCost

open Cover Cover.Frame Cover.AddressCircuit Hecke Crossing Epoch Shortening Catalog StaticRows
open PreparedBins Framed PublicSegments PublicRelative PublicPopulation PublicParallel
open Packing DirectoryCircuit PublicDirectory BankCircuit VPVNP.VerifierNetwork PublicDenseReceipt
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

/-- The exact post-selection summand in the gate bound of `selectedReceipt_frames`. -/
def backend (bins bank q n C p F s k V E seeds d l : ℕ) : ℕ :=
  (1 + k*E*(C*(d+1)^p) + k*E*Nat.clog 2 bins*(2*bins+1) + 1) +
    seeds*(bank + 90*q*(d+2*n+1)) + (k*V+k*E+seeds+1)*F*l^s

private theorem lane {r R L p e x b : ℕ} (c : ℕ) (hr : r ≤ R) (hL : 1 ≤ L)
    (hx : x ≤ b*L) (hp : p ≤ e) :
    r*c*x^p ≤ (R*L^e)*(c*b^p) := by
  calc
    _ ≤ R*c*(b*L)^p := Nat.mul_le_mul (Nat.mul_le_mul_right _ hr) (Nat.pow_le_pow_left hx _)
    _ = (R*L^p)*(c*b^p) := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL hp))

/-- The front-end bound and the actual directory callback yield one joint
budget, including the tree conjunction cost and the exact number of guessed
histogram bits. The selected backend word bound is large enough for both its
address key and its paid-count key. -/
theorem bound_le (a : FrontCosts) (kinds bins bank terms q n G g C p F s : ℕ) :
    ∃ A e : ℕ, ∀ (k V E w data lev d vol T seeds : ℕ),
      k*V ≤ T → k*E ≤ T → w ≤ Nat.clog 2 (T+1) → lev+1 ≤ Nat.clog 2 vol+2 →
      lev+1 = d+2*n → data ≤ G*(lev+1+2*n+1)^g → seeds = vol*bins →
      ∃ l : ℕ, d+1 ≤ l ∧
        Nat.clog 2 (seeds+k*E)+(Nat.clog 2 bins+keyWidth q (d+2*n))+w+1 ≤ l ∧
        w+Nat.clog 2 (terms+1)+1 ≤ l ∧
        a.bound k V E w data kinds q (lev+1) n vol T +
          backend bins bank q n C p F s k V E seeds d l + (2*k+4) + seeds*terms*w ≤
          (k*V+2*(k*E)+k*(vol+1)+seeds+1)*A*(Nat.clog 2 (T+vol+2)+1)^e := by
  obtain ⟨A₀,e₀,front⟩ := a.bound_le kinds q n G g
  let B := Nat.clog 2 (bins+1) + Nat.clog 2 bins + Nat.clog 2 (terms+1) + 360*q + 10
  let e := max e₀ (max p (max s 1))
  let A := A₀ + C*4^p + Nat.clog 2 bins*(2*bins+1) + bank+360*q + F*B^s + terms + 8
  refine ⟨A,e,?_⟩
  intro k V E w data lev d vol T seeds hv hr hw hdepth hlevel hdata hs
  let L := Nat.clog 2 (T+vol+2)+1
  let R := k*V+2*(k*E)+k*(vol+1)+seeds+1
  let U := R*L^e
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have h1 : 1 ≤ e := by dsimp [e]; omega
  have hp : p ≤ e := by dsimp [e]; omega
  have hs' : s ≤ e := by dsimp [e]; omega
  have hfront := front k V E w data (lev+1) vol T hv hr hw hdepth hdata
  have hR : 1 ≤ R := Nat.le_add_left _ _
  have hRU : R ≤ U := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hL)
  have hrows : k*E ≤ R := by dsimp [R]; omega
  have hseeds : seeds ≤ R := by dsimp [R]; omega
  have hk : k ≤ R := by dsimp [R]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hfront' : a.bound k V E w data kinds q (lev+1) n vol T ≤ U*A₀ := by
    have hx : k*V+2*(k*E)+k*(vol+1)+1 ≤ R := by dsimp [R]; omega
    have hy := Nat.mul_le_mul_right A₀ (Nat.mul_le_mul hx
      (Nat.pow_le_pow_right hL (le_max_left e₀ (max p (max s 1)))))
    apply hfront.trans
    simpa only [U,e,L,Nat.mul_right_comm _ A₀] using hy
  have hbits : w ≤ L := hw.trans ((Nat.clog_mono_right 2 (by omega : T+1 ≤ T+vol+2)).trans (Nat.le_succ _))
  have hlogvol := Nat.clog_mono_right 2 (by omega : vol ≤ T+vol+2)
  have hdeep : d+2*n+1 ≤ 4*L := by dsimp [L]; omega
  have hd : d+1 ≤ 4*L := by omega
  have hkey : keyWidth q (d+2*n) ≤ 360*q*L := by
    change q*(30*(d+2*n+1)*3) ≤ _
    calc
      _ = 90*q*(d+2*n+1) := by ring
      _ ≤ 90*q*(4*L) := Nat.mul_le_mul_left _ hdeep
      _ = _ := by ring
  have hsort : Nat.clog 2 (seeds+k*E) ≤ Nat.clog 2 (bins+1)+L := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have hcap : seeds+k*E ≤ (bins+1)*(T+vol+2) := by rw [hs]; nlinarith only [hr]
    exact hcap.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) ((Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ _))))
  have hbank := Nat.le_mul_of_pos_right (Nat.clog 2 bins) hL
  have hterms := Nat.le_mul_of_pos_right (Nat.clog 2 (terms+1)) hL
  have hsort' := Nat.le_mul_of_pos_right (Nat.clog 2 (bins+1)) hL
  let l := B*L
  have hbackend :
      d+1 ≤ l ∧ Nat.clog 2 (seeds+k*E)+(Nat.clog 2 bins+keyWidth q (d+2*n))+w+1 ≤ l ∧
        w+Nat.clog 2 (terms+1)+1 ≤ l := by
    simp only [l,B,Nat.add_mul]
    omega
  refine ⟨l,hbackend.1,hbackend.2.1,hbackend.2.2,?_⟩
  have hreader := lane C hrows hL hd hp
  have hbin := Nat.mul_le_mul_right (Nat.clog 2 bins*(2*bins+1)) (hrows.trans hRU)
  have hseed := Nat.mul_le_mul_right bank (hseeds.trans hRU)
  have hcoord := lane (90*q) hseeds hL hdeep h1
  have hbe : k*V+k*E+seeds+1 ≤ R := by dsimp [R]; omega
  have htable := lane F hbe hL (show l ≤ B*L from le_rfl) hs'
  have hwords := lane terms hseeds hL (show w ≤ 1*L by simpa using hbits) h1
  simp only [pow_one, Nat.mul_one] at hcoord hwords
  change _ ≤ U*_ at hreader hcoord htable hwords
  have hflags := hk.trans hRU
  have hunit := hR.trans hRU
  calc
    _ ≤ U*A := by
      unfold backend
      dsimp only [A]
      nlinarith only [hfront',hreader,hbin,hseed,hcoord,htable,hwords,hflags,hunit]
    _ = _ := by dsimp only [U,R,L]; ring

universe u

variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}
    {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ} (src : SourceTemplate e h H ν S)

set_option maxHeartbeats 2100000 in
/-- An actual selected frame with its gate, validity-flag and count-input
budget. Its full receipt for the physical successor is retained. The choice
of the frame precedes the expanded bound `T`, so one can use any such bound,
including an exponential of the word length. -/
theorem selectedReceipt_envelope (hm : 0 < m) (G g : ℕ) :
    ∃ P₀ cut A p : ℕ, 0 < P₀ ∧
      ∀ {P : Type} {bits : P → ℕ} (lev d k : ℕ) (_ : src.floor ≤ lev) (_ : 1 ≤ d)
        (level : lev+1 = d+2*src.word) (hk : 0 < k) (_ : cut ≤ lev+1+2*src.word)
        {Data : Type} [Fintype Data] (V E seeds W w : ℕ)
        (field : FieldBit (↥S) (Cube D) (lev+2*src.word+1) → Data)
        (seed : ((Cube D → Deck (d+2*src.word)) × src.bins.Bin) ≃ Fin seeds),
        let vol := Fintype.card (Cube D → Deck (lev+1))
        P₀ < 2^w → W < 2^w → packRunWidth vol P₀ k W ≤ w →
        k*V ≤ 2^w → seeds ≤ 2^w → siteCapacity e (k*V) seeds ≤ 2^w →
        edgeCapacity e (k*E) seeds ≤ 2^w → Nat.clog 2 (widthMultiplier e*(k*W)+1) ≤ w →
        ∃ f : Frame ((Fin k × (Fin E ⊕ Raw Data V E w w)) ⊕ Words (Seed src.bins lev) e.count w)
          (Result src.bins e d src.word k V E seeds w),
          (∀ T : ℕ, k*V ≤ T → k*E ≤ T → w ≤ Nat.clog 2 (T+1) →
            Fintype.card Data ≤ G*(lev+1+2*src.word+1)^g →
            f.size + (2*k+4) + Fintype.card (Words (Seed src.bins lev) e.count w) ≤
              (k*V+2*(k*E)+k*(vol+1)+seeds+1)*A*(Nat.clog 2 (T+vol+2)+1)^p) ∧
          ∀ (child : Fin k → PlacedPack D P bits K (Cube D) (lev+2*src.word))
            (site : ∀ i, (child i).pack.layout.Site ↪ Fin V) (row : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
            (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
            (x : Fin k × (Fin E ⊕ Raw Data V E w w) → Bool),
            (∀ i, Catalog.PlacedAt S h (child i)) →
            (∀ i j, x (i,.inl j) = true ↔ j ∈ Set.range (row i)) →
            (∀ i, SegmentReady S (child i).pack.layout (site i) (row i) (dummy i) (child i).site field
              (child i).charged (fun j => x (i,.inr j))) →
            (∀ i, (∑ c, (child i).pack.layout.width c) ≤ W) →
            NodeReads src level hk seed child site row dummy x f := by
  obtain ⟨P₀,cut,a,C,b,F,s,hP,build⟩ := selectedReceipt_frames src hm
  let q := Fintype.card (Cube D)
  let bins := Fintype.card src.bins.Bin
  let bank := (sitePattern (n := src.word) src.bins).bins
  obtain ⟨A,p,cost⟩ := bound_le a (Fintype.card src.bins.types) bins bank e.count q src.word G g C b F s
  refine ⟨P₀,cut,A,p,hP,?_⟩
  intro P bits lev d k hd hpos level hk hcut Data instData V E seeds W w field seed vol den fits run hv hn hs he hw
  obtain ⟨f,gate,read⟩ := build (P := P) (bits := bits) lev d k hd hpos level hk hcut V E seeds W w
    field seed den fits run hv hn hs he hw
  refine ⟨f,?_,read⟩
  intro T hV hE width data
  have hdepth := depth_le_clog_tiles (Cube D) (lev+1)
  have hseed : Fintype.card (Seed src.bins lev) = seeds := by
    simpa only [Fintype.card_fin] using Fintype.card_congr ((seedLevel level).trans seed)
  have hvol : seeds = vol*bins := by simpa only [Seed,Fintype.card_prod] using hseed.symm
  have words : Fintype.card (Words (Seed src.bins lev) e.count w) = seeds*e.count*w := by
    simp only [Words,Fintype.card_prod,Fintype.card_fin,hseed,Nat.mul_assoc]
  obtain ⟨l,hd',hkey,hterms,ineq⟩ := cost k V E w (Fintype.card Data) lev d vol T seeds hV hE width
    hdepth level data hvol
  have hg := gate T l hE width hd' hkey hterms
  rw [words]
  exact (Nat.add_le_add_right (Nat.add_le_add_right hg (2*k+4)) _).trans ineq

end Packing.SelectedNodeCost

end BorderVNP
end Computability
end OAI
