import OAI.Computability.BorderVNP.ShortenPublicSegmentStage
import OAI.Computability.BorderVNP.ShortenPublicPopulationBudget
import OAI.Computability.BorderVNP.PackedResources

/-!
# Sparse work bound for the public endpoint join and geometric reader

Each of the two endpoint requests per cable is paid for once. The normalized
point tag is a fixed catalog field, the quaternion tile words are linear in
the depth, and optional public payloads may add polynomially many address
bits. The gate bound stays linear in the padded site and cable capacities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.AddressCircuit Epoch Catalog PublicPopulation TeamScales Filter
open scoped Classical

/-- Exact number of wires holding a public catalogued position. -/
theorem card_fieldBit (T I : Type*) [Fintype T] [Fintype I] (l : ℕ) :
    Fintype.card (FieldBit T I l) = Fintype.card T + 90*Fintype.card I*(l+1) := by
  simp [FieldBit,StackFrame.Slots,AddressCircuit.width]
  ring

/-- The endpoint join and tag reader use linear work in the number of stored
rows up to a polynomial in the binary-field widths and congruence depth. -/
theorem readCost_polylog (A a T : ℕ) :
    ∃ C e : ℕ, ∀ V E k l data L : ℕ, 1 ≤ L → l+1 ≤ L →
      Nat.clog 2 (V+2*E)+k+data+1 ≤ L →
      300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+data+1)^3 + (1+E*(A*(l+1)^a+2*T+3)) ≤
        (V+E+1)*C*L^e := by
  refine ⟨600+A+2*T+4,max 3 a,?_⟩
  intro V E k l data L hL hdepth hword
  let N := V+E+1
  let p := max 3 a
  have lanes : V+2*E+1 ≤ 2*N := by dsimp [N]; omega
  have eN : E ≤ N := by dsimp [N]; omega
  have oneN : 1 ≤ N := by dsimp [N]; omega
  have one : 1 ≤ L^p := Nat.one_le_pow _ _ hL
  have hsort := Nat.mul_le_mul (Nat.mul_le_mul_left 300 lanes)
    ((Nat.pow_le_pow_left hword 3).trans (Nat.pow_le_pow_right hL (le_max_left 3 a)))
  have hrow := Nat.mul_le_mul eN (Nat.mul_le_mul_left A
    ((Nat.pow_le_pow_left hdepth a).trans (Nat.pow_le_pow_right hL (le_max_right 3 a))))
  have hpad : E*(2*T+3) ≤ N*(2*T+3)*L^p :=
    (Nat.mul_le_mul_right _ eN).trans (Nat.le_mul_of_pos_right _ one)
  have hone : 1 ≤ N*L^p := Nat.mul_pos oneN one
  change _ ≤ N*(600+A+2*T+4)*L^p
  nlinarith only [hsort,hrow,hpad,hone]

/-- The moved-row emission and full allocator histogram fit the same linear
row-volume bound as the public join. The sort term includes one query for
each legal tile and each relative bin. -/
theorem histogramCost_polylog (A a C c H b T bins : ℕ) :
    ∃ F e : ℕ, ∀ V E k d deep data tiles key w L : ℕ, 1 ≤ L → deep+1 ≤ L → d+1 ≤ L →
      Nat.clog 2 (V+2*E)+k+data+1 ≤ L →
      let v := E+tiles*bins
      let r := Nat.clog 2 bins
      Nat.clog 2 v+(r+key)+w+1 ≤ L →
      (300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+data+1)^3 + (1+E*(A*(deep+1)^a+2*T+3))) +
        ((1+E*(H*(d+1)^b)) + (1+E*(C*(d+1)^c) +
          (E*r*(2*bins+1)+2*(v+1)*laneCost (Nat.clog 2 v) (r+key) w))) ≤ (V+E+tiles+1)*F*L^e := by
  obtain ⟨F,e,read⟩ := readCost_polylog A a T
  let r := Nat.clog 2 bins
  let p := max (max e 3) (max b c)
  refine ⟨F+2+H+C+r*(2*bins+1)+400*(bins+1),p,?_⟩
  intro V E k d deep data tiles key w L hL hdeep hd hr v _ hw
  let N := V+E+tiles+1
  have en : E ≤ N := by dsimp [N]; omega
  have hbase : V+E+1 ≤ N := by dsimp [N]; omega
  have hn : 1 ≤ N := by dsimp [N]; omega
  have h1 := Nat.one_le_pow p L hL
  have hOne : 1 ≤ N*L^p := Nat.mul_pos hn h1
  have hpow (u : ℕ) (hu : u ≤ p) := Nat.pow_le_pow_right hL hu
  have hread := (read V E k deep data L hL hdeep hr).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_right F hbase) (hpow e (by dsimp [p]; omega)))
  have row (Q u : ℕ) (hu : u ≤ p) : E*(Q*(d+1)^u) ≤ N*Q*L^p := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul en (Nat.mul_le_mul_left Q ((Nat.pow_le_pow_left hd u).trans (hpow u hu)))
  have hH := row H b (by dsimp [p]; omega)
  have hC := row C c (by dsimp [p]; omega)
  have ht : E*r*(2*bins+1) ≤ N*(r*(2*bins+1))*L^p :=
    (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ en : E*r*(2*bins+1) ≤ N*(r*(2*bins+1))).trans
      (Nat.le_mul_of_pos_right _ h1)
  have vv : v+1 ≤ N*(bins+1) := by dsimp [v,N]; nlinarith
  have lc := (laneCost_le (Nat.clog 2 v) (r+key) w).trans
    (Nat.mul_le_mul_left 200 ((Nat.pow_le_pow_left hw 3).trans (hpow 3 (by dsimp [p]; omega))))
  have hs := Nat.mul_le_mul (Nat.mul_le_mul_left 2 vv) lc
  change _ ≤ N*(F+2+H+C+r*(2*bins+1)+400*(bins+1))*L^p
  nlinarith only [hread,hH,hC,ht,hs,hOne]

variable {D q : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable (enum : Fin q ≃ Cube D)

/-- A common threshold and work polynomial apply at every one of a finite
family of stages, even when the catalogs are recursively prepared. -/
theorem finite_reconstruction_cost {J : Type*} [Fintype J] (S : J → Finset (HyperbolicHost (Cube D)))
    (B : ∀ j, PreparedBins D (S j) h η) :
    ∃ cut C e : ℕ, ∀ j l (hl : 0 < l), cut ≤ l → ∀ (Data : Type*) [Fintype Data]
      (V E k w L : ℕ), V ≤ 2^k → 1 ≤ L → l+1 ≤ L →
      Nat.clog 2 (V+2*E)+k+Fintype.card Data+1 ≤ L →
      ∀ field : FieldBit (↥(S j)) (Cube D) l → Data,
      ∃ g, g.size ≤ (V+E+1)*C*L^e ∧ Reconstructs (B j) enum hl field (V := V) (E := E) (k := k) (w := w) g := by
  choose cut A a g using fun j => reconstruct_frames (B j) enum
  choose C e cost using fun j => readCost_polylog (A j) (a j) (Fintype.card (B j).types)
  refine ⟨Finset.univ.sup cut,Finset.univ.sup C,Finset.univ.sup e,?_⟩
  intro j l hl hcut Data inst V E k w L fit hL hd hw field
  obtain ⟨f,hf,sem⟩ := g j l hl ((Finset.le_sup (Finset.mem_univ j)).trans hcut) Data V E k w fit field
  exact ⟨f,hf.trans ((cost j V E k l (Fintype.card Data) L hL hd hw).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Finset.le_sup (Finset.mem_univ j)))
      (Nat.pow_le_pow_right hL (Finset.le_sup (Finset.mem_univ j))))),sem⟩

/-- The actual circuit fits the public reconstruction exponent over all teams
and epochs, under the sparse row caps and binary field widths. -/
theorem eventually_reconstruction_work {J : Type*} [Fintype J]
    (S : J → Finset (HyperbolicHost (Cube D))) (B : ∀ j, PreparedBins D (S j) h η)
    {α τ growth : ℝ} {fan : ℕ} (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100)
    (hfan : 1 ≤ fan) (hteams : τ*Real.logb 2 fan ≤ α) (hg : 1 ≤ growth)
    (hsmall : τ*Real.logb 2 growth ≤ α/10) (u : ℕ) :
    ∃ cut : ℕ, ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ Z : ℕ,
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      ∀ j l (hl : 0 < l), cut ≤ l → ∀ (Data : Type*) [Fintype Data] (V E k w : ℕ),
        V ≤ 2^k → (V+E+1 : ℝ) ≤ A*(r*(n : ℝ)^(9/10 : ℝ))*(growth^epochs τ n * width n α) →
        l+1 ≤ Z*logWidth r n^u → Nat.clog 2 (V+2*E)+k+Fintype.card Data+1 ≤ Z*logWidth r n^u →
        ∀ field : FieldBit (↥(S j)) (Cube D) l → Data,
          ∃ g, Reconstructs (B j) enum hl field (V := V) (E := E) (k := k) (w := w) g ∧
            (epochs τ n : ℝ)*teams α τ fan n*g.size < r*(n : ℝ)^(93/100 : ℝ) := by
  obtain ⟨cut,C,e,frames⟩ := finite_reconstruction_cost enum S B
  obtain ⟨ω,hω,resources⟩ := Packing.eventually_sparse_resources hα hτ hτ' hfan hteams hg hsmall (u*e)
  refine ⟨cut,ω,hω,?_⟩
  intro A hA Z
  filter_upwards [resources 1 (by norm_num),resources (A*C*(Z:ℝ)^e) (by positivity)] with n hlocal htotal
  intro r hr hmax j l hl hcut Data inst V E k w fit hcap hd hw field
  let L := Z*logWidth r n^u
  obtain ⟨f,hs,sem⟩ := frames j l hl hcut Data V E k w L fit (by dsimp [L]; omega) hd hw field
  refine ⟨f,sem,?_⟩
  have hrw := (hlocal r hr hmax).2.1
  simp only [one_mul] at hrw
  have hvol : growth^epochs τ n*(width n α : ℝ) ≤ (n : ℝ)^(1/100 : ℝ) :=
    hrw.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hsz : (f.size : ℝ) ≤ (V+E+1 : ℝ)*C*((Z : ℝ)*(logWidth r n : ℝ)^u)^e := by
    exact_mod_cast hs
  calc
    _ ≤ (epochs τ n : ℝ)*teams α τ fan n*((A*(r*(n : ℝ)^(9/10 : ℝ))*(n : ℝ)^(1/100 : ℝ))*C*
        ((Z : ℝ)*(logWidth r n : ℝ)^u)^e) := by
      have cap := hcap.trans (mul_le_mul_of_nonneg_left hvol (by positivity))
      gcongr
      exact hsz.trans (by gcongr)
    _ = (A*C*(Z : ℝ)^e)*(epochs τ n : ℝ)*teams α τ fan n*(r*(n : ℝ)^(9/10 : ℝ))*
        (n : ℝ)^(1/100 : ℝ)*(logWidth r n : ℝ)^(u*e) := by rw [mul_pow,←pow_mul]; ring
    _ < _ := (htotal r hr hmax).2.2

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
