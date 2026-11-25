import OAI.Computability.BorderVNP.ShortenPublicSegmentHistogram
import OAI.Computability.BorderVNP.ShortenPublicSegmentBudget

/-!
# Work of the finite sequence of public shortening rounds

The joint congruence threshold and gate polynomial are taken before the
level, the number of copies, and the profile-dependent public arrays. The
number of sites, cables, and tiles is the only linear factor. This includes
both the allocator's actual integer histogram and every moved cable address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.Frame Cover.AddressCircuit Epoch Catalog Hecke TeamScales Filter

variable {J : Type*} [Fintype J] {D q : ℕ} {h η : ℝ} (enum : Fin q ≃ Cube D)
variable (S : J → Finset (HyperbolicHost (Cube D))) (B : ∀ j, PreparedBins D (S j) h η)
variable {M : J → Type*} [∀ j, Fintype (M j)] [∀ j, DecidableEq (M j)]
variable (nWord : J → ℕ) (perm : ∀ j, M j → Equiv.Perm (Cube D))
variable (word : ∀ j, M j → ProductSample (lattice 1) elliptic (Cube D) (nWord j))

/-- Joint polynomial gate bound for any finite sequence of prepared catalogs. -/
theorem finite_histogram_frames :
    ∃ cut F p : ℕ, ∀ j (d : ℕ) (hd : 1 ≤ d), let l := d+2*nWord j
      let deep := l+2*nWord j
      let tiles := Fintype.card (Cube D → Deck l)
      let bins := Fintype.card (B j).Bin
      cut ≤ deep → ∀ (Data : Type*) [Fintype Data] (V E k w copies L : ℕ), V ≤ 2^k →
        1 ≤ L → deep+1 ≤ L → Nat.clog 2 (V+2*E)+k+Fintype.card Data+1 ≤ L →
        Nat.clog 2 (E+tiles*bins)+(Nat.clog 2 bins+keyWidth q l)+w+1 ≤ L →
        ∀ (field : FieldBit (↥(S j)) (Cube D) deep → Data) (home : Fin E → Fin copies),
        ∃ f, f.size ≤ (V+E+tiles+1)*F*L^p ∧
          HistogramRows (B j) enum (perm j) (word j) hd field home (V := V) (k := k) (w := w) f := by
  classical
  choose cut A a C c H b run using fun j => rawHistogram_frames (B j) enum (perm j) (word j)
  choose F p cost using fun j => histogramCost_polylog (A j) (a j) (C j) (c j) (H j) (b j)
    (Fintype.card (B j).types) (Fintype.card (B j).Bin)
  refine ⟨Finset.univ.sup cut,Finset.univ.sup F,Finset.univ.sup p,?_⟩
  intro j d hd l deep tiles bins hcut Data inst V E k w copies L fit hL hdeep hr hw field home
  obtain ⟨f,hf,sem⟩ := run j d hd ((Finset.le_sup (Finset.mem_univ j)).trans hcut)
    Data V E k w copies fit field home
  have hdl : d+1 ≤ L := (show d+1 ≤ deep+1 by dsimp [deep,l]; omega).trans hdeep
  have hs := cost j V E k d deep (Fintype.card Data) tiles (keyWidth q l) w L hL hdeep hdl hr hw
  refine ⟨f,hf.trans (hs.trans ?_),sem⟩
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Finset.le_sup (Finset.mem_univ j)))
    (Nat.pow_le_pow_right hL (Finset.le_sup (Finset.mem_univ j)))

/-- The public gate count, including epochs and teams, fits the exponent
of Proposition 7.2 under the physical descriptor, tile and word caps. -/
theorem eventually_histogram_work {α τ growth : ℝ} {fan : ℕ} (hα : α < 1/1000)
    (hτ : 0 < τ) (hτ' : τ < α/100) (hfan : 1 ≤ fan) (hteams : τ*Real.logb 2 fan ≤ α)
    (hg : 1 ≤ growth) (hsmall : τ*Real.logb 2 growth ≤ α/10) (u : ℕ) :
    ∃ cut : ℕ, ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ Z : ℕ,
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      ∀ j (d : ℕ) (hd : 1 ≤ d), let l := d+2*nWord j
        let deep := l+2*nWord j
        let tiles := Fintype.card (Cube D → Deck l)
        let bins := Fintype.card (B j).Bin
        let L := Z*logWidth r n^u
        cut ≤ deep → ∀ (Data : Type*) [Fintype Data] (V E k w copies : ℕ), V ≤ 2^k →
          (V+E+tiles+1 : ℝ) ≤ A*(r*(n : ℝ)^(9/10 : ℝ))*(growth^epochs τ n * TeamScales.width n α) →
          deep+1 ≤ L → Nat.clog 2 (V+2*E)+k+Fintype.card Data+1 ≤ L →
          Nat.clog 2 (E+tiles*bins)+(Nat.clog 2 bins+keyWidth q l)+w+1 ≤ L →
          ∀ (field : FieldBit (↥(S j)) (Cube D) deep → Data) (home : Fin E → Fin copies),
            ∃ f, HistogramRows (B j) enum (perm j) (word j) hd field home (V := V) (k := k) (w := w) f ∧
              (epochs τ n : ℝ)*teams α τ fan n*f.size < r*(n : ℝ)^(93/100 : ℝ) := by
  obtain ⟨cut,F,p,rows⟩ := finite_histogram_frames enum S B nWord perm word
  obtain ⟨ω,hω,resources⟩ := Packing.eventually_sparse_resources hα hτ hτ' hfan hteams hg hsmall (u*p)
  refine ⟨cut,ω,hω,?_⟩
  intro A hA Z
  filter_upwards [resources 1 (by norm_num), resources (A*F*(Z:ℝ)^p) (by positivity)] with n localCap budget
  intro r hr hmax j d hd l deep tiles bins L hcut Data inst V E k w copies fit hcap hdeep hrw hsw field home
  obtain ⟨f,hs,sem⟩ := rows j d hd hcut Data V E k w copies L fit (by omega) hdeep hrw hsw field home
  refine ⟨f,sem,?_⟩
  have hc := (localCap r hr hmax).2.1
  simp only [one_mul] at hc
  have vol : growth^epochs τ n*(TeamScales.width n α : ℝ) ≤ (n : ℝ)^(1/100 : ℝ) :=
    hc.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have size : (f.size : ℝ) ≤ (V+E+tiles+1 : ℝ)*F*((Z : ℝ)*(logWidth r n : ℝ)^u)^p := by
    exact_mod_cast hs
  calc
    _ ≤ (epochs τ n : ℝ)*teams α τ fan n*((A*(r*(n : ℝ)^(9/10 : ℝ))*(n : ℝ)^(1/100 : ℝ))*F*
        ((Z : ℝ)*(logWidth r n : ℝ)^u)^p) := by
      have cap := hcap.trans (mul_le_mul_of_nonneg_left vol (by positivity))
      gcongr
      exact size.trans (by gcongr)
    _ = (A*F*(Z : ℝ)^p)*(epochs τ n : ℝ)*teams α τ fan n*(r*(n : ℝ)^(9/10 : ℝ))*
        (n : ℝ)^(1/100 : ℝ)*(logWidth r n : ℝ)^(u*p) := by rw [mul_pow,←pow_mul]; ring
    _ < _ := (budget r hr hmax).2.2

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
