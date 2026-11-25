import OAI.Hierarchy.ProbeLocalReplacement

namespace OAI
/-! # The discrepancy of a connected spectral ball

The spectral point and its scale are optimized jointly. Connectedness
bounds the scale of all competitive trials uniformly, including when some
of the proposed prices vanish. -/

noncomputable section
namespace Hierarchy.Probe

open scoped Classical BigOperators NNReal
open LinearAlgebra.SpectralBooks
open LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph

variable {k : ℕ} {E A : Type*} (F : Type*) [Field F] [Nonempty (Fin k)]
  [Fintype E] [Nonempty E] [Fintype A]

private def errAt (edge : E → Chord k) (req : A → E) (p : E → ℝ)
    (φ : Spectrum F k) (t : ℝ) : E ⊕ A → ℝ
  | .inl e => max 0 (t * distance φ (edge e) - p e)
  | .inr a => |t * distance φ (edge (req a)) - p (req a)|

def testError (edge : E → Chord k) (req : A → E) (p : E → ℝ) (φ : Spectrum F k) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (errAt F edge req p φ t)

def discrepancy (edge : E → Chord k) (req : A → E) (p : E → ℝ) : ℝ :=
  sInf (Set.range (fun z : Spectrum F k × ℝ≥0 => testError F edge req p z.1 z.2))

private theorem entry_le (edge : E → Chord k) (req : A → E) (p : E → ℝ)
    (φ : Spectrum F k) (t : ℝ) (i : E ⊕ A) :
    errAt F edge req p φ t i ≤ testError F edge req p φ t :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem testError_nonneg (edge : E → Chord k) (req : A → E) (p : E → ℝ)
    (φ : Spectrum F k) (t : ℝ) : 0 ≤ testError F edge req p φ t :=
  (le_max_left _ _).trans (entry_le F edge req p φ t (.inl (Classical.arbitrary E)))

private theorem error_continuous (edge : E → Chord k) (req : A → E) (p : E → ℝ) :
    Continuous (fun z : Spectrum F k × ℝ => testError F edge req p z.1 z.2) := by
  apply Continuous.finset_sup'_apply
  intro i _
  cases i with
  | inl e =>
    change Continuous (fun z : Spectrum F k × ℝ => max 0 (z.2 * distance z.1 (edge e) - p e))
    exact continuous_const.max
      ((continuous_snd.mul ((distance_continuous (edge e)).comp continuous_fst)).sub continuous_const)
  | inr a =>
    change Continuous (fun z : Spectrum F k × ℝ => |z.2 * distance z.1 (edge (req a)) - p (req a)|)
    exact ((continuous_snd.mul ((distance_continuous (edge (req a))).comp continuous_fst)).sub
      continuous_const).abs

theorem discrepancy_le (edge : E → Chord k) (req : A → E) (p : E → ℝ)
    (φ : Spectrum F k) {t : ℝ} (ht : 0 ≤ t) :
    discrepancy F edge req p ≤ testError F edge req p φ t := by
  apply csInf_le
  · exact ⟨0,by rintro _ ⟨z,rfl⟩; exact testError_nonneg F edge req p z.1 z.2⟩
  · exact ⟨(φ,⟨t,ht⟩),rfl⟩

/-- Some available link detects a positive scale, with a common lower bound
over all normalized spectral points on the connected format. -/
theorem connected_scale (edge : E → Chord k) (conn : Connected edge) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ φ : Spectrum F k, ∃ e : E, μ ≤ distance φ (edge e) := by
  let e := edge (Classical.arbitrary E)
  let : Nontrivial (Fin k) := ⟨e.1.1,e.1.2,e.2.ne⟩
  let : Nonempty (Spectrum F k) := (spectrum_nonempty.{0} (Fin k) F).to_subtype
  let : CompactSpace (Spectrum F k) := isCompact_iff_compactSpace.mp isCompact_spectrum
  let peak (φ : Spectrum F k) := Finset.univ.sup' Finset.univ_nonempty (fun e => distance φ (edge e))
  have hc : Continuous peak := Continuous.finset_sup'_apply _ (fun e _ => distance_continuous _)
  obtain ⟨φ₀,_,low⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨e₀,h₀⟩ := connected_positive edge conn φ₀
  refine ⟨peak φ₀,h₀.trans_le (Finset.le_sup' (fun i => distance φ₀ (edge i)) (Finset.mem_univ e₀)),fun φ => ?_⟩
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset E).Nonempty)
    (fun i => distance φ (edge i))
  exact ⟨j,(isMinOn_iff.mp low φ (Set.mem_univ φ)).trans_eq hj⟩

/-- The least maximum discrepancy is attained by a genuine spectral price
system, possibly at zero scale. -/
theorem discrepancy_attained (edge : E → Chord k) (req : A → E) (p : E → ℝ)
    (conn : Connected edge) :
    ∃ (φ : Spectrum F k) (t : ℝ), 0 ≤ t ∧ discrepancy F edge req p = testError F edge req p φ t := by
  let e := edge (Classical.arbitrary E)
  let : Nontrivial (Fin k) := ⟨e.1.1,e.1.2,e.2.ne⟩
  let φ₀ := (spectrum_nonempty.{0} (Fin k) F).to_subtype.some
  let : CompactSpace (Spectrum F k) := isCompact_iff_compactSpace.mp isCompact_spectrum
  obtain ⟨μ,hμ,peak⟩ := connected_scale F edge conn
  let r := testError F edge req p φ₀ 0
  let C := max 0 (Finset.univ.sup' Finset.univ_nonempty p)
  let T := (C+r)/μ
  have hr : 0 ≤ r := testError_nonneg F edge req p φ₀ 0
  have hC : 0 ≤ C := le_max_left _ _
  have hT : 0 ≤ T := div_nonneg (add_nonneg hC hr) hμ.le
  let K : Set (Spectrum F k × ℝ) := Set.univ ×ˢ Set.Icc 0 T
  have zero : (φ₀,(0:ℝ)) ∈ K := ⟨Set.mem_univ _,le_rfl,hT⟩
  have compact : IsCompact K := isCompact_univ.prod isCompact_Icc
  obtain ⟨q,hq,minimal⟩ := compact.exists_isMinOn ⟨_,zero⟩ (error_continuous F edge req p).continuousOn
  have best (ψ : Spectrum F k) (u : ℝ) (hu : 0 ≤ u) :
      testError F edge req p q.1 q.2 ≤ testError F edge req p ψ u := by
    by_cases huT : u ≤ T
    · exact isMinOn_iff.mp minimal _ (show (ψ,u) ∈ K from ⟨Set.mem_univ _,hu,huT⟩)
    obtain ⟨i,hi⟩ := peak ψ
    have grow : C+r < u*μ := (div_lt_iff₀ hμ).mp (lt_of_not_ge huT)
    have hpc : p i ≤ C := (Finset.le_sup' _ (Finset.mem_univ i)).trans (le_max_right _ _)
    have up : r ≤ u*distance ψ (edge i)-p i := by
      linarith only [grow,hpc,mul_le_mul_of_nonneg_left hi hu]
    exact (isMinOn_iff.mp minimal _ zero).trans (up.trans
      ((le_max_right _ _).trans (entry_le F edge req p ψ u (.inl i))))
  refine ⟨q.1,q.2,hq.2.1,le_antisymm (discrepancy_le F edge req p q.1 hq.2.1) ?_⟩
  apply le_csInf
  · exact ⟨_,⟨(φ₀,0),rfl⟩⟩
  · rintro _ ⟨z,rfl⟩
    exact best z.1 z.2 z.2.property

private theorem error_le_add (edge : E → Chord k) (req : A → E) (p q : E → ℝ)
    {δ : ℝ} (close : ∀ e, |p e-q e| ≤ δ) (φ : Spectrum F k) (t : ℝ) :
    testError F edge req p φ t ≤ testError F edge req q φ t + δ := by
  apply Finset.sup'_le
  intro i _
  cases i with
  | inl e =>
    have h := entry_le F edge req q φ t (.inl e)
    change max 0 (_-q e) ≤ _ at h
    change max 0 (_-p e) ≤ _
    apply max_le
    · exact add_nonneg (testError_nonneg F edge req q φ t) ((abs_nonneg _).trans (close e))
    · linarith only [(le_max_right _ _).trans h,(abs_le.mp (close e)).1]
  | inr a =>
    have h := entry_le F edge req q φ t (.inr a)
    change |_-q (req a)| ≤ _ at h
    change |_-p (req a)| ≤ _
    apply abs_le.mpr
    constructor <;> linarith only [(abs_le.mp h).1,(abs_le.mp h).2,
      (abs_le.mp (close (req a))).1,(abs_le.mp (close (req a))).2]

/-- Perturbing every proposed price by at most `δ` changes the optimized
discrepancy by at most `δ`. -/
theorem discrepancy_lipschitz (edge : E → Chord k) (req : A → E) (conn : Connected edge)
    (p q : E → ℝ) {δ : ℝ} (close : ∀ e, |p e-q e| ≤ δ) :
    |discrepancy F edge req p - discrepancy F edge req q| ≤ δ := by
  obtain ⟨φ,t,ht,pt⟩ := discrepancy_attained F edge req p conn
  obtain ⟨ψ,u,hu,qu⟩ := discrepancy_attained F edge req q conn
  have l := (discrepancy_le F edge req p ψ hu).trans (error_le_add F edge req p q close ψ u)
  have r := (discrepancy_le F edge req q φ ht).trans (error_le_add F edge req q p
    (fun e => by rw [abs_sub_comm]; exact close e) φ t)
  rw [← pt] at r
  rw [← qu] at l
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A positive minimum is exactly the failure condition used to obtain the
local coefficient identity. -/
theorem failed_iff_discrepancy_pos (edge : E → Chord k) (req : A → E)
    (conn : Connected edge) (p : E → ℝ) :
    Failed F edge req p ↔ 0 < discrepancy F edge req p := by
  constructor
  · intro fail
    obtain ⟨φ,t,ht,hm⟩ := discrepancy_attained F edge req p conn
    by_contra! nonpos
    rw [hm] at nonpos
    refine fail ⟨φ,t,ht,fun e => ?_,fun a => ?_⟩
    · apply sub_nonpos.mp
      exact (le_max_right _ _).trans ((entry_le F edge req p φ t (.inl e)).trans nonpos)
    · apply sub_eq_zero.mp
      apply abs_nonpos_iff.mp
      exact (entry_le F edge req p φ t (.inr a)).trans nonpos
  · rintro pos ⟨φ,t,ht,upper,exactD⟩
    have z : testError F edge req p φ t ≤ 0 := by
      apply Finset.sup'_le
      intro i _
      cases i with
      | inl e => exact max_le le_rfl (sub_nonpos.mpr (upper e))
      | inr a => simp [errAt,exactD a]
    exact (not_lt_of_ge ((discrepancy_le F edge req p φ ht).trans z)) pos

/-- The normalized maximum norm on the finite list of options has Lipschitz
constant one, including at proposed prices equal to zero. -/
theorem discrepancy_one_lipschitz (edge : E → Chord k) (req : A → E) (conn : Connected edge) :
    LipschitzWith 1 (discrepancy F edge req) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  apply discrepancy_lipschitz F edge req conn p q
  intro e
  simpa only [Real.dist_eq] using dist_le_pi_dist p q e

/-- On a compact price box the points failing by a fixed tolerance form
a compact parameter space for a finite catalogue of replacements. -/
theorem compact_failed_tests (edge : E → Chord k) (req : A → E) (conn : Connected edge)
    {P : Set (E → ℝ)} (hP : IsCompact P) (ε : ℝ) :
    IsCompact (P ∩ {p | ε ≤ discrepancy F edge req p}) :=
  hP.inter_right (isClosed_le continuous_const (discrepancy_one_lipschitz F edge req conn).continuous)

/-- At a requested precision a compact set of price arrays admits finite
lookup advice with rational entries. A center within half the requested
precision gives an answer within the full precision. -/
theorem finite_discrepancy_advice (edge : E → Chord k) (req : A → E) (conn : Connected edge)
    {P : Set (E → ℝ)} (compact : IsCompact P) {ε : ℝ} (pos : 0 < ε) :
    ∃ (S : Finset (E → ℝ)) (table : S → ℚ), (∀ c : S, (c : E → ℝ) ∈ P) ∧
      ∀ p ∈ P, (∃ c : S, dist p c.val < ε/2) ∧
        ∀ c : S, dist p c.val < ε/2 → |discrepancy F edge req p - (table c : ℝ)| < ε := by
  obtain ⟨s,sub,finite,cover⟩ := finite_cover_balls_of_compact compact (half_pos pos)
  let S := finite.toFinset
  let d := discrepancy F edge req
  choose table lower upper using fun c : S =>
    exists_rat_btwn (show d c.val-ε/2 < d c.val+ε/2 by linarith)
  refine ⟨S,table,fun c => sub (finite.mem_toFinset.mp c.property),?_⟩
  intro p hp
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (cover hp)
  obtain ⟨mem,hit⟩ := Set.mem_iUnion.mp hc
  refine ⟨⟨⟨c,finite.mem_toFinset.mpr mem⟩,hit⟩,?_⟩
  intro j near
  have moves := (discrepancy_one_lipschitz F edge req conn).dist_le_mul p j.val
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at moves
  change |d p - d j.val| ≤ dist p j.val at moves
  apply abs_lt.mpr
  constructor <;> linarith only [(abs_le.mp moves).1,(abs_le.mp moves).2,near,lower j,upper j]

/-- Both the centers and the entries of a finite lookup table may be
rational. Any matching row returns the requested accuracy. -/
theorem rational_discrepancy_lookup (edge : E → Chord k) (req : A → E) (conn : Connected edge)
    {P : Set (E → ℝ)} (compact : IsCompact P) {ε : ℝ} (pos : 0 < ε) :
    ∃ (n : ℕ) (center : Fin n → E → ℚ) (value : Fin n → ℚ), ∀ p ∈ P,
      (∃ j, dist p (fun e => (center j e : ℝ)) < ε/2) ∧ ∀ j,
        dist p (fun e => (center j e : ℝ)) < ε/2 →
          |discrepancy F edge req p - (value j : ℝ)| < ε := by
  have eps : 0 < ε/8 := by linarith
  obtain ⟨s,_,finite,cover⟩ := finite_cover_balls_of_compact compact eps
  let S := finite.toFinset
  let a (i : Fin (Fintype.card S)) : E → ℝ := ((Fintype.equivFin S).symm i).val
  let d := discrepancy F edge req
  choose q lower upper using fun (i : Fin (Fintype.card S)) (e : E) =>
    exists_rat_btwn (show a i e - ε/8 < a i e + ε/8 by linarith)
  choose v vlo vhi using fun (i : Fin (Fintype.card S)) =>
    exists_rat_btwn (show d (a i) - ε/8 < d (a i) + ε/8 by linarith)
  have near i : dist (a i) (fun e => (q i e : ℝ)) < ε/8 := by
    apply (dist_pi_lt_iff eps).mpr
    intro e
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith only [lower i e,upper i e]
  refine ⟨_,q,v,?_⟩
  intro p hp
  constructor
  · obtain ⟨x,hx⟩ := Set.mem_iUnion.mp (cover hp)
    obtain ⟨hx,hit⟩ := Set.mem_iUnion.mp hx
    let j : S := ⟨x,finite.mem_toFinset.mpr hx⟩
    let i := Fintype.equivFin S j
    have same : a i = x := congrArg Subtype.val ((Fintype.equivFin S).symm_apply_apply j)
    change dist p x < ε/8 at hit
    rw [← same] at hit
    refine ⟨i,?_⟩
    linarith only [dist_triangle p (a i) (fun e => (q i e : ℝ)),hit,near i,pos]
  · intro i hit
    have m := (discrepancy_one_lipschitz F edge req conn).dist_le_mul p (a i)
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at m
    change |d p - d (a i)| ≤ dist p (a i) at m
    have t := dist_triangle p (fun e => (q i e : ℝ)) (a i)
    rw [dist_comm (fun e => (q i e : ℝ)) (a i)] at t
    apply abs_lt.mpr
    constructor <;> linarith only [(abs_le.mp m).1,(abs_le.mp m).2,t,hit,near i,vlo i,vhi i,pos]


end Hierarchy.Probe
end

end OAI
