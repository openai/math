import OAI.Computability.BorderVNP.TransmissionJointLiteral
import OAI.Computability.BorderVNP.TeamContractionWireScale
import OAI.Computability.BorderVNP.TeamSiteConsistencyScale

/-!
# Fitting the real fixed processor code, public header and interior ports

All fixed code and metadata, the distributed advice bit, and the arbitrary
free suffix occupy the manuscript's single literal of length t₀. Its duplicate
pin field and the direct exterior links form exactly the native input stride.
The physical comparator ports, including both possible virtual sorting lanes,
fit with these inputs uniformly throughout the prescribed range of team sizes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine TeamScales Wires Filter
open TeamTapeInputRoute (comparisonSize)

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)

/-- Free coordinates after the program, all encoded parameters and the designated advice bit. -/
noncomputable def siteFree (α : ℝ) (teams w n : ℕ) : ℕ :=
  literal α n - freeStart P lib teams w n

private theorem log_width (teams n : ℕ) : logWidth teams n = Nat.clog 2 (2*n*teams) := by
  unfold logWidth
  rw [← Real.natCeil_logb_natCast]
  norm_cast

private theorem log_dominates {teams n : ℕ} (ht : 0 < teams) (hn : 0 < n) :
    1 ≤ logWidth teams n ∧ Nat.clog 2 (n+1) ≤ logWidth teams n ∧ Nat.clog 2 teams ≤ logWidth teams n := by
  rw [log_width]
  have h : 2*n ≤ 2*n*teams := Nat.le_mul_of_pos_right _ ht
  have t : teams ≤ 2*n*teams := Nat.le_mul_of_pos_left _ (by omega)
  exact ⟨Nat.clog_pos (by decide) (by omega), Nat.clog_mono_right _ (by omega), Nat.clog_mono_right _ t⟩

/-- Explicit cost of the true finite program prefix and every public parameter in its
literal. The logarithm includes the incoming PC and both sorting roles. -/
theorem freeStart_le (teams w n : ℕ) (ht : 0 < teams) (hn : 0 < n) (wide : logWidth teams n ≤ w) :
    freeStart P lib teams w n ≤ ((programPrefix (TeamSite.Processor.machine P lib)).length + k + reg + 48)*w := by
  obtain ⟨hL,hnlog,htlog⟩ := log_dominates ht hn
  have h₁ : Nat.clog 2 (n+1) ≤ w := hnlog.trans wide
  have h₂ : Nat.clog 2 teams ≤ w := htlog.trans wide
  have hw : 1 ≤ w := hL.trans wide
  let len := (programPrefix (TeamSite.Processor.machine P lib)).length
  have hp : len ≤ len*w := Nat.le_mul_of_pos_right _ hw
  rw [freeStart_eq]
  unfold entryLiteral cutWidth setupWidth prefixCapacity
  change len + (4*Nat.clog 2 (n+1)+2 + ((2*(w+1)+1 + (2*Nat.clog 2 (n+1)+1)) +
    ((k+8)*w+2 + (1+(reg+2)*w) + (2*Nat.clog 2 (n+1)+1) + 2*(2*Nat.clog 2 teams+1)+1+1))) ≤
    (len+k+reg+48)*w
  nlinarith

/-- Reducing the team-size exponent preserves every previous large-input bound. -/
theorem admissible_smaller {n teams : ℕ} {u v : ℝ} (hn : 1 ≤ n) (huv : u ≤ v)
    (h : (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^u)) : (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^v) :=
  h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) huv))

/-- One team-size exponent accommodates arbitrary fixed code overheads in the reserved
literal and arbitrary constant multiples of the physical bit-port budget. -/
theorem exists_common_exponent (D : ℕ) {α ξ : ℝ} (hα : α < 3) (hξ : 0 < ξ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams →
      (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
      c*logWidth teams n^D ≤ literal α n ∧ c*block ξ n*logWidth teams n^(D+2) ≤ n := by
  let γ := (1-α/3)/2
  obtain ⟨u,hu,hp⟩ := exists_polylog_budget D (show 0 < γ by dsimp [γ]; linarith)
  obtain ⟨v,hv,hs⟩ := eventually_sorting_links (D+2) hξ
  refine ⟨min u v,lt_min hu hv,fun c => ?_⟩
  filter_upwards [hp,hs c,eventually_ge_atTop 1,
    eventually_rpow_gap (show γ < 1-α/3 by dsimp [γ]; linarith) c] with n hl hsort hn hgap
  intro teams ht bound
  have a := hl teams ht (admissible_smaller hn (min_le_left _ _) bound)
  refine ⟨?_,hsort teams ht (admissible_smaller hn (min_le_right _ _) bound)⟩
  apply Nat.le_floor
  push_cast
  exact (mul_le_mul_of_nonneg_left a (by positivity)).trans hgap

/-- Uniform geometric and input-layout facts used by the actual compiler and validator.
The literal has the exact prescribed length, and at least half is available for the
two shared geometry stripes and original private descriptions. -/
structure SiteGeometry (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
    (α ξ : ℝ) (teams n other w e : ℕ) : Prop where
  /-- Word arithmetic, global sort addresses and the exact manuscript clock fit. -/
  baseline : TeamSiteConsistency.Geometry teams n pc w (block ξ n) (width n (1/2)) (ticks ξ teams n) e
  /-- Every real processor and virtual sorter index can be decoded at input length n. -/
  dimensions : 2+e+Nat.clog 2 teams ≤ n
  /-- The widened paired read/write sorter uses words of at most n bits. -/
  widened : w+1 ≤ n
  /-- The actual comparator portion, including every Batcher layer, fits the public input. -/
  comparators : comparisonSize (Nat.clog 2 teams) e (w+1) ≤ n
  /-- Free suffix in the actual literal, after the advice bit and code. -/
  reserved : 2*freeStart P lib teams w n ≤ literal α n
  /-- Exact complete literal, including the encoded finite machine's program prefix. -/
  literalSize : entryLiteral (TeamSite.Processor.machine P lib) (w+1) n
    (prefixCapacity teams k reg w n+1+siteFree P lib α teams w n) = literal α n
  /-- The initialized field order is literal, exterior, then the optional pin copy. -/
  stride : entryStride (TeamSite.Processor.machine P lib) (w+1) n
    (prefixCapacity teams k reg w n+1+siteFree P lib α teams w n) other (link ξ (other+1) n) =
    2*literal α n+other*link ξ (other+1) n
  /-- All three fields together require at most three local logical blocks. -/
  localInput : 2*literal α n+other*link ξ (other+1) n ≤ 3*block ξ n
  /-- The actual per-site parser, its pin input and the interior wiring fit in n physical slots. -/
  fits : Fits P lib teams w (siteFree P lib α teams w n) other (link ξ (other+1) n) n e

/-- Choose the polynomial logarithmic word exponent before the admissible team exponent.
Every fixed RAM program then has one large-input threshold, uniform in positive team
size, number of exterior teams, all fixed pins and all actual interior assignments. -/
theorem eventually_siteGeometry (D : ℕ) {α ξ : ℝ} (hα : α < 3) (hξ : 0 < ξ)
    (hsmall : ξ < 3/2) (horder : ξ ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
      (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g),
      ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
      ∀ other : ℕ, SiteGeometry P lib α ξ teams n other (logWidth teams n^(D+1)) (sortExponent (block ξ n)) := by
  obtain ⟨ω,hω,cap⟩ := exists_common_exponent (D+1) hα hξ
  refine ⟨ω,hω,?_⟩
  intro pc reg k routines m g Q Γ inst P lib
  let len := (programPrefix (TeamSite.Processor.machine P lib)).length
  let C := 2*(len+k+reg+48) + (2*reg+700)
  filter_upwards [cap C,TeamSiteConsistency.eventually_setupGeometry hξ hsmall pc D,
    eventually_ge_atTop 1] with n hcap hgeo hn
  intro teams hr hrmax other
  let L := logWidth teams n
  let w := L^(D+1)
  let H := block ξ n
  let e := sortExponent H
  let V := H*L^(D+1+2)
  obtain ⟨prefixBound,slots⟩ := hcap teams hr hrmax
  change C*w ≤ literal α n at prefixBound
  change C*H*L^(D+1+2) ≤ n at slots
  rw [Nat.mul_assoc] at slots
  change C*V ≤ n at slots
  have geo := hgeo teams hr
  obtain ⟨hL,_,hd⟩ := log_dominates hr hn
  have hH : 0 < H := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n : ℝ))
      (show 0 ≤ 1-ξ/3 by linarith)
  have hwide : L ≤ w := by
    change L ≤ L^(D+1)
    simpa only [pow_one] using Nat.pow_le_pow_right hL (show 1 ≤ D+1 by omega)
  have hPow : w ≤ L^(D+1+2) := Nat.pow_le_pow_right hL (by omega)
  have hwV : w ≤ V := hPow.trans (Nat.le_mul_of_pos_left _ hH)
  have hV : 1 ≤ V := (hL.trans hwide).trans hwV
  have hHV : H ≤ V := Nat.le_mul_of_pos_right _ (pow_pos hL _)
  have hp := freeStart_le P lib teams w n hr hn hwide
  have hpre : 2*freeStart P lib teams w n ≤ literal α n := by
    apply (Nat.mul_le_mul_left 2 hp).trans
    change 2*((len+k+reg+48)*w) ≤ _
    rw [← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right w (by dsimp [C]; omega)).trans prefixBound
  let a := siteFree P lib α teams w n
  have literalEq : entryLiteral (TeamSite.Processor.machine P lib) (w+1) n (prefixCapacity teams k reg w n+1+a) = literal α n := by
    have base := freeStart_eq (r := teams) (w := w) P lib n
    unfold entryLiteral at base ⊢
    dsimp only [a,siteFree]; omega
  have strideEq : entryStride (TeamSite.Processor.machine P lib) (w+1) n
      (prefixCapacity teams k reg w n+1+a) other (link ξ (other+1) n) = 2*literal α n+other*link ξ (other+1) n := by
    simp only [entryStride,literalEq]
  have fields : 2*literal α n+other*link ξ (other+1) n ≤ 3*H := by
    simpa only [Nat.add_sub_cancel] using input_fields_le hn hξ.le horder (other+1)
  have inner : innerWidth teams reg w e (w+1) ≤ (2*reg+686)*V := by
    simpa only [w,L,V,H,e,Nat.mul_assoc] using innerWidth_bound hr hn hH reg (D+1)
  have portBound : 3*H + innerWidth teams reg w e (w+1) ≤ n := by
    refine (Nat.add_le_add (Nat.mul_le_mul_left 3 hHV) inner).trans ?_
    rw [← Nat.add_mul]
    exact (Nat.mul_le_mul_right V (by dsimp [C]; omega)).trans slots
  have hE : 2^e ≤ 4*H := (TeamSorting.padding_lt_twice (show 0 < 2*H by omega)).le.trans_eq (by ring)
  have ee : e ≤ 2^e := Nat.lt_two_pow_self.le
  have ddim : Nat.clog 2 teams ≤ V := (hd.trans hwide).trans hwV
  have slack : 10*V ≤ n := (Nat.mul_le_mul_right _ (by dsimp [C]; omega : 10 ≤ C)).trans slots
  change SiteGeometry P lib α ξ teams n other w e
  refine ⟨geo,by omega,by omega,?_,hpre,literalEq,strideEq,fields,?_⟩
  · have hi := (Nat.le_add_left _ _).trans portBound
    unfold innerWidth at hi
    omega
  · unfold Fits
    rw [strideEq]
    exact (Nat.add_le_add_right fields _).trans portBound

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
