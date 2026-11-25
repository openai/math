import OAI.LinearAlgebra.SpectralBooks.WireIdentity
import OAI.LinearAlgebra.SpectralBooks.Alternative
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum

namespace OAI
/-! # Local wire replacement for multidirectional adaptive probing

A failed joint price test on a connected ball yields an ordinary sum over
the ground field. Demands and replacement options are indexed separately,
so several commodities and catalysts can occupy the same pair of sites. -/

noncomputable section

open scoped BigOperators Classical NNReal
open LinearAlgebra.SpectralBooks
open LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph

namespace Hierarchy.Probe

variable {k : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]

abbrev Spectrum (F : Type*) [Field F] (k : ℕ) [Nonempty (Fin k)] :=
  normalizedSpectrum (S := TensorClass.{0} (Fin k) F) (· ≤ ·)

def distance (φ : Spectrum F k) (e : Chord k) : ℝ :=
  rawWireDistance φ 1 e.1.1 e.1.2

def optionWidths (edge : E → Chord k) (count : E → ℕ) : Widths k :=
  ∑ j, Finsupp.single (edge j) (count j)

def demandWidths (edge : E → Chord k) (req : A → E) : Widths k :=
  optionWidths (edge ∘ req) (fun _ => 1)

/-- The available options connect the sites of the ball by undirected paths. -/
def Connected (edge : E → Chord k) : Prop :=
  ∀ x y : Fin k, Relation.EqvGen (fun a b => ∃ e, (edge e).1 = (a,b)) x y

/-- No spectral point at any nonnegative common scale realizes all demand
prices while respecting the upper prices on every available option. -/
def Failed (F : Type*) [Field F] (edge : E → Chord k) (req : A → E) (cost : E → ℝ) : Prop :=
  ¬ ∃ (φ : Spectrum F k) (t : ℝ), 0 ≤ t ∧
    (∀ e, t * distance φ (edge e) ≤ cost e) ∧
    ∀ a, t * distance φ (edge (req a)) = cost (req a)

/-- On a singleton ball every raw demand is supplied by a single local
table from the scalar unit, with no communication. -/
theorem singleton_supply (T : Raw.{0} (Fin 1) F) : T.Restricts (Raw.one (Fin 1) F) := by
  have h : (id : Fin 1 → Fin 1) = fun _ => 0 := Subsingleton.elim _ _
  have unit : (T.group id).Restricts (Raw.one (Fin 1) F) := by
    rw [h]
    exact T.group_const_restricts_one 0
  exact restrict_trans T.group_id_equivalent.2 unit

omit [Fintype E] in
private theorem failed_positive [Nonempty E] (edge : E → Chord k) (req : A → E) (cost : E → ℝ)
    (nonneg : ∀ e, 0 ≤ cost e) (failed : Failed F edge req cost) :
    0 < ∑ a, cost (req a) := by
  by_contra! ht
  let e := edge (Classical.arbitrary E)
  let : Nontrivial (Fin k) := ⟨e.1.1,e.1.2, e.2.ne⟩
  have hz (a : A) : cost (req a) = 0 := le_antisymm
    ((Finset.single_le_sum (fun a _ => nonneg (req a)) (Finset.mem_univ a)).trans ht) (nonneg _)
  refine failed ⟨(spectrum_nonempty.{0} (Fin k) F).to_subtype.some, 0, le_rfl, ?_, ?_⟩
  · intro j
    simpa only [zero_mul] using nonneg j
  · intro a
    simp only [zero_mul,hz]

theorem distance_continuous (e : Chord k) :
    Continuous (fun φ : Spectrum F k => distance φ e) := by
  have hn := graphClass_ne_zero F (unitChord e)
  rw [graphClass_unitChord] at hn
  simpa only [distance,rawWireDistance,rawLogPrice,one_mul,wire] using
    (continuous_log_price (one_le_of_ne_zero hn) :
      Continuous (fun φ : Spectrum F k => Real.logb 2 (φ.val (wire F e) : ℝ)))

theorem connected_positive (edge : E → Chord k) (conn : Connected edge)
    (φ : Spectrum F k) : ∃ j, 0 < distance φ (edge j) := by
  by_contra! hn
  have eqzero (x y : Fin k) : rawWireDistance φ 1 x y = 0 := by
    induction conn x y with
    | rel a b hab =>
      obtain ⟨j,hj⟩ := hab
      have z := le_antisymm (hn j) (rawLogPrice_nonneg φ zero_le_one _)
      simpa only [distance,hj] using z
    | refl a => exact rawWireDistance_self φ 1 zero_le_one a
    | symm a b _ ih => rw [rawWireDistance_symm,ih]
    | trans a b c _ _ hab hbc =>
      exact le_antisymm (by simpa only [hab,hbc,zero_add] using
        rawWireDistance_triangle φ 1 zero_le_one a b c) (rawLogPrice_nonneg φ zero_le_one _)
  let T := Raw.diagonal (Fin k) F (Fin 2)
  let v : Fin k := Classical.arbitrary _
  have z := rawLogPrice_eq_of_collapsed φ 1 zero_le_one T id (fun _ => v)
    (fun i => eqzero i v)
  rw [rawLogPrice_const φ 1 zero_le_one] at z
  have he := ofRaw_eq_iff.mpr (Raw.group_id_equivalent T)
  have two : φ.val (2 : TensorClass.{0} (Fin k) F) = 2 :=
    map_ofNat (normalizedSpectrum.toRingHom φ) 2
  simp only [rawLogPrice,he,T,ofRaw_diagonal_fin_eq_natCast,Nat.cast_ofNat,two,
    NNReal.coe_ofNat,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),one_mul,one_ne_zero] at z

private theorem separation (edge : E → Chord k) (req : A → E) (cost : E → ℝ)
    (conn : Connected edge) (failed : Failed F edge req cost)
    (pos : 0 < ∑ a, cost (req a)) (φ : Spectrum F k) :
    ∃ j, (∑ a, distance φ (edge (req a))) * cost j <
      (∑ a, cost (req a)) * distance φ (edge j) := by
  let D := ∑ a, distance φ (edge (req a))
  let L := ∑ a, cost (req a)
  have hn : 0 ≤ D := Finset.sum_nonneg fun _ _ => rawLogPrice_nonneg φ zero_le_one _
  rcases hn.eq_or_lt with hz | hd
  · obtain ⟨j,hj⟩ := connected_positive edge conn φ
    exact ⟨j,by change D * _ < L * _; rw [←hz,zero_mul]; exact mul_pos pos hj⟩
  by_contra! bad
  have bounds (j : E) : L/D * distance φ (edge j) ≤ cost j := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hd).mpr ((bad j).trans_eq (mul_comm D (cost j)))
  apply failed
  refine ⟨φ,L/D,(div_pos pos hd).le,bounds,?_⟩
  have total : ∑ a, L/D * distance φ (edge (req a)) = ∑ a, cost (req a) := by
    rw [← Finset.mul_sum]
    change L / D * D = L
    exact div_mul_cancel₀ _ hd.ne'
  exact fun a => (Finset.sum_eq_sum_iff_of_le (fun i _ => bounds (req i))).mp total a
    (Finset.mem_univ a)

private theorem cheap_ratios [Nonempty E] (edge : E → Chord k) (req : A → E)
    (cost : E → ℝ) (nonneg : ∀ e, 0 ≤ cost e) (conn : Connected edge)
    (failed : Failed F edge req cost) (pos : 0 < ∑ a, cost (req a)) :
    ∃ (ratio : E → ℚ) (B : ℝ), B < ∑ a, cost (req a) ∧
      (∀ e, 0 < ratio e ∧ (ratio e : ℝ) * cost e ≤ B) ∧
      ∀ φ : Spectrum F k, ∃ e,
        (∑ a, distance φ (edge (req a))) < (ratio e : ℝ) * distance φ (edge e) := by
  let : CompactSpace (Spectrum F k) := isCompact_iff_compactSpace.mp isCompact_spectrum
  let D (φ : Spectrum F k) := ∑ a, distance φ (edge (req a))
  let L := ∑ a, cost (req a)
  have cont : Continuous D := continuous_finsetSum _ (fun a _ => distance_continuous _)
  let U : Set (ℝ × Spectrum F k) :=
    ⋃ j, {p | D p.2 * (cost j + p.1) < L * distance p.2 (edge j)}
  have op : IsOpen U := isOpen_iUnion fun j => isOpen_lt
    ((cont.comp continuous_snd).mul (continuous_const.add continuous_fst))
    (continuous_const.mul ((distance_continuous (edge j)).comp continuous_snd))
  have incl : ({0} : Set ℝ) ×ˢ (Set.univ : Set (Spectrum F k)) ⊆ U := by
    rintro ⟨t,φ⟩ ⟨(rfl : t=0),-⟩
    obtain ⟨j,hj⟩ := separation edge req cost conn failed pos φ
    exact Set.mem_iUnion_of_mem j (by simpa [D,L] using hj)
  obtain ⟨u,v,hu,_,hzero,hall,hprod⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ op incl
  obtain ⟨ε,hε,hmem⟩ := Metric.isOpen_iff.mp hu 0 (hzero rfl)
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  have inside : δ ∈ u := hmem (by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ] using half_lt_self hε)
  let len (j : E) := cost j + δ
  have plen (j : E) : 0 < len j := add_pos_of_nonneg_of_pos (nonneg j) hδ
  have cover (φ : Spectrum F k) : ∃ j, D φ < (L / len j) * distance φ (edge j) := by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hprod (Set.mk_mem_prod inside (hall (Set.mem_univ φ))))
    exact ⟨j,by rw [div_mul_eq_mul_div]; exact (lt_div_iff₀ (plen j)).mpr hj⟩
  obtain ⟨r,hr,rc⟩ := exists_rational_wire_widths (fun j => L / len j)
    (fun j => div_pos pos (plen j)) (fun j φ => distance φ (edge j)) D
    (fun j => distance_continuous _) cont (fun _ φ => rawLogPrice_nonneg φ zero_le_one _) cover
  obtain ⟨j,_,hmax⟩ := Finset.univ.exists_max_image (fun i => (r i : ℝ)*cost i) Finset.univ_nonempty
  refine ⟨r,_,?_,fun i => ⟨(hr i).1,hmax i (Finset.mem_univ _)⟩,rc⟩
  apply lt_of_le_of_lt _ ((lt_div_iff₀ (plen j)).mp (hr j).2)
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ.le) (by exact_mod_cast (hr j).1.le)

private theorem price_widths (edge : E → Chord k) (count : E → ℕ) (φ : Spectrum F k) :
    ∑ e : Chord k, ((optionWidths edge count) e : ℝ) * distance φ e =
      ∑ j, (count j : ℝ) * distance φ (edge j) := by
  simp only [optionWidths,Finsupp.finsetSum_apply,Nat.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (edge j)]
  · simp
  · intro e _ h
    simp [Finsupp.single_eq_of_ne h]
  · simp

/-- The failed ball has a strict cost saving shared by every summand. At any
prescribed selector rate and minimum width, this gives an exact coefficient
identity in the original demand ports. Each summand has a local restriction
from the indicated widths of the replacement options. -/
theorem exists_local_replacement [Nonempty E]
    (edge : E → Chord k) (req : A → E) (cost : E → ℝ)
    (nonneg : ∀ e, 0 ≤ cost e) (conn : Connected edge)
    (failed : Failed F edge req cost) :
    ∃ B : ℝ, B < ∑ a, cost (req a) ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η*b ∧
      let R := raw F (b • demandWidths edge req)
      ∃ l : ℕ, l ≤ 2^s ∧ ∃ z : Fin l → (∀ i, R.Leg i) → F,
        R.coeff = ∑ t, z t ∧ ∀ t, ∃ count : E → ℕ,
          (∑ j, (count j : ℝ)*cost j) ≤ b*B ∧
          ({R with coeff := z t} : Raw (Fin k) F).Restricts (raw F (optionWidths edge count)) := by
  obtain ⟨r,B,saving,hr,cover⟩ := cheap_ratios edge req cost nonneg conn failed
    (failed_positive edge req cost nonneg failed)
  obtain ⟨m,hm,bits,hbits⟩ := exists_common_wire_width r (fun j => (hr j).1)
  have scaled (j : E) : (bits j : ℝ) = (m : ℝ)*(r j : ℝ) := by
    exact_mod_cast (hbits j).2
  let base := m • demandWidths edge req
  let opt (j : E) : Widths k := Finsupp.single (edge j) (bits j)
  have hcover (φ : Spectrum F k) : ∃ j,
      (∑ e : Chord k, (base e : ℝ)*distance φ e) ≤
      ∑ e : Chord k, (opt j e : ℝ)*distance φ e := by
    obtain ⟨j,hj⟩ := cover φ
    refine ⟨j,?_⟩
    have target : (∑ e : Chord k, ((demandWidths edge req) e : ℝ)*distance φ e) =
        ∑ a, distance φ (edge (req a)) := by
      simpa only [demandWidths,Function.comp_apply,Nat.cast_one,one_mul] using
        price_widths (edge ∘ req) (fun _ => 1) φ
    have source : (∑ e : Chord k, (opt j e : ℝ)*distance φ e) =
        (bits j : ℝ)*distance φ (edge j) := by
      rw [Finset.sum_eq_single (edge j)]
      · simp [opt]
      · intro e _ he
        simp [opt,Finsupp.single_eq_of_ne he]
      · simp
    rw [source,scaled,mul_assoc]
    simp only [base,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_mul,mul_assoc,← Finset.mul_sum,target]
    exact mul_le_mul_of_nonneg_left hj.le (Nat.cast_nonneg m)
  refine ⟨B,saving,?_⟩
  intro η hη N
  obtain ⟨b,s,hb,hs,identity⟩ := exists_finite_wire_tile F base opt hcover hη N
  have eqbase : b • base = (b*m) • demandWidths edge req := by
    exact smul_smul b m _
  dsimp only at identity
  rw [eqbase] at identity
  obtain ⟨l,hl,z,hz,terms⟩ := identity
  refine ⟨b*m,s,hb.trans_le (Nat.le_mul_of_pos_right _ hm),?_,l,hl,z,hz,?_⟩
  · exact hs.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Nat.le_mul_of_pos_right b hm) hη.le)
  intro t
  obtain ⟨n,hn,rest⟩ := terms t
  refine ⟨fun j => n j * bits j,?_,?_⟩
  · calc
      _ = ∑ j, (n j : ℝ)*((bits j : ℝ)*cost j) := by simp only [Nat.cast_mul,mul_assoc]
      _ ≤ ∑ j, (n j : ℝ)*((m : ℝ)*B) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [scaled,mul_assoc]
        exact mul_le_mul_of_nonneg_left (hr j).2 (Nat.cast_nonneg m)
      _ = ((b*m : ℕ) : ℝ)*B := by
        rw [← Finset.sum_mul,← Nat.cast_sum,hn,Nat.cast_mul,mul_assoc]
  · simpa only [optionWidths,opt,Finsupp.smul_single,nsmul_eq_mul,Nat.cast_id] using rest

end Hierarchy.Probe

end

end OAI
