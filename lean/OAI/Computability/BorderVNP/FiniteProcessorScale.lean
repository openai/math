import OAI.Computability.BorderVNP.FiniteProcessorInstallation
import OAI.Computability.BorderVNP.FiniteLiteral
import OAI.Computability.BorderVNP.TeamProcessorUniform

/-! # Finite-field team simulation uniformly over all admissible team sizes

The admissible team exponent precedes the program and field. Each fixed
field processor has a common length threshold for all team counts, exterior
wiring, advice, private input pins and physical interior assignments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP BurstRAM UniversalMachine TeamContraction TeamContraction.ProcessorSlots TeamSite
open TeamSiteConsistency TeamSiteEvents TeamTapeHandoff TeamScales Filter
open scoped BigOperators Classical
open private log_dominates from OAI.Computability.BorderVNP.TeamProcessorLiteralScale

/-- Number of freely supplied literal bits after the actual field program and its
physical register and handoff metadata. -/
noncomputable def freeWidth (physical : Program) (α : ℝ) (args regs teams w n : ℕ) :=
  literal α n - freeStartWith physical teams args regs w n

private theorem start_le (physical : Program) (args regs teams w n : ℕ) (hr : 0 < teams)
    (hn : 0 < n) (wide : logWidth teams n ≤ w) :
    freeStartWith physical teams args regs w n ≤ ((programPrefix physical).length+args+regs+48)*w := by
  obtain ⟨hL,hnlog,htlog⟩ := log_dominates hr hn
  have h₁ : Nat.clog 2 (n+1) ≤ w := hnlog.trans wide
  have h₂ : Nat.clog 2 teams ≤ w := htlog.trans wide
  have hw : 1 ≤ w := hL.trans wide
  let len := (programPrefix physical).length
  have hp : len ≤ len*w := Nat.le_mul_of_pos_right _ hw
  unfold freeStartWith FiniteBoot.offset entryLiteral cutWidth setupWidth prefixCapacity
  change len + (4*Nat.clog 2 (n+1)+2 + ((2*(w+1)+1+(2*Nat.clog 2 (n+1)+1))+
    ((args+8)*w+2+(1+(regs+2)*w)+(2*Nat.clog 2 (n+1)+1)+2*(2*Nat.clog 2 teams+1)+1+1))) ≤ (len+args+regs+48)*w
  nlinarith

/-- The charged word geometry, exact length and free suffix of the true field literal. -/
structure Scale (physical : Program) (pc regs args : ℕ) (α ξ : ℝ) (teams n other w e : ℕ) : Prop where
  /-- Real RAM, sorter and chronological cutoff. -/
  baseline : Geometry teams n pc w (block ξ n) (width n (1/2)) (ticks ξ teams n) e
  /-- Decodability of virtual owners and layers. -/
  dimensions : 2+e+Nat.clog 2 teams ≤ n
  /-- Space for the widened memory records. -/
  widened : w+1 ≤ n
  /-- Size of the actual sorter-message slice. -/
  comparators : TeamTapeInputRoute.comparisonSize (Nat.clog 2 teams) e (w+1) ≤ n
  /-- At least half the literal remains available after the true field prefix. -/
  reserved : 2*freeStartWith physical teams args regs w n ≤ literal α n
  /-- Length of the true field literal. -/
  literalSize : entryLiteral physical (w+1) n (prefixCapacity teams args regs w n+1+freeWidth physical α args regs teams w n) = literal α n
  /-- Per-site input capacity. -/
  localInput : 2*literal α n+other*link ξ (other+1) n ≤ 3*block ξ n
  /-- The true word strides and the prescribed shared interior edges fit. -/
  fits : fitsWith physical regs args teams w (freeWidth physical α args regs teams w n) other (link ξ (other+1) n) n e

variable {pc reg k a m g teams n other w e : ℕ} {Q Γ : Type} [Fintype Q] {F : Type*} [Field F] [Fintype F] {α ξ : ℝ}
variable (P : TeamOpcode.Program pc reg k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)

/-- Replace the fixed finite processor description while retaining the same RAM and
sorter geometry. The new description and its complete startup header fit the literal. -/
theorem Scale.of_reserved (physical : Program) (geo : SiteGeometry P lib α ξ teams n other w e)
    (reserved : 2*freeStartWith physical teams k reg w n ≤ literal α n) :
    Scale physical pc reg k α ξ teams n other w e := by
  let free := freeWidth physical α k reg teams w n
  have litEq : entryLiteral physical (w+1) n (prefixCapacity teams k reg w n+1+free) = literal α n := by
    unfold freeWidth freeStartWith FiniteBoot.offset entryLiteral at *
    dsimp only [free,freeWidth,freeStartWith,FiniteBoot.offset,entryLiteral]
    omega
  have fit := geo.fits
  unfold Fits at fit
  rw [geo.stride] at fit
  refine ⟨geo.baseline,geo.dimensions,geo.widened,geo.comparators,reserved,litEq,geo.localInput,?_⟩
  unfold fitsWith entryStride
  rw [litEq]
  exact fit

variable (geo : Scale (machine P lib weights) pc reg k α ξ teams n other w e)

/-- Install arbitrary data after the true field processor's fixed prefix. -/
noncomputable def Scale.data (publicWords : Fin (other+1) → Fin k → Word w)
    (registers : Fin (other+1) → Fin reg → Word w) (advice : Fin (other+1) → Fin teams → Bool)
    (free : Fin (other+1) → Fin teams → Fin (freeWidth (machine P lib weights) α k reg teams w n) → Bool) :
    SiteData other teams reg k w (freeWidth (machine P lib weights) α k reg teams w n) :=
  ⟨publicWords,⟨block ξ n,geo.baseline.blockWord⟩,⟨ticks ξ teams n,geo.baseline.tickWord⟩,
    ⟨width n (1/2),geo.baseline.capWord⟩,registers,advice,free⟩

/-- All legal fields of the exact fixed-width site geometry admit the field-valued
native execution and its physical path correspondence, with arbitrary constants. -/
def AtScale (hr : 0 < teams) : Prop :=
  ∀ (pub : Fin (other+1) → Fin k → Word w) (regs : Fin (other+1) → Fin reg → Word w)
    (advice : Fin (other+1) → Fin teams → Bool)
    (free : Fin (other+1) → Fin teams → Fin (freeWidth (machine P lib weights) α k reg teams w n) → Bool),
    (∀ j vs, vs.length ≤ width n (1/2) → (lib j).bounded (n^25+1) (vs : List (Word w))) →
    ∀ {d : ℕ} (u : Fin (other+1)) (pin : Fin d → Bool) (ext : Exterior other teams (link ξ (other+1) n) → Bool)
      (ib hb sb : ℕ),
      let S := Scale.data P lib weights geo pub regs advice free
      let G := wiringWith (machine P lib weights) P S d (link ξ (other+1) n) n e geo.fits
      let rows := (G.processorFields u pin ext ib hb sb).row
      ∃ own : ∀ j, (rows j).length ≤ 3*S.block.val,
        let M := geo.baseline.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩ (n^25) rows own
        FieldTeam.fieldValue G F pin ext u = nativeSum M lib weights (n^25+1) ∧
          SpellingBijection M G lib pin ext u ∧ CheckedDictionary M G lib pin u ext ∧ RowValues M lib weights G pin ext u (n^25+1)

set_option maxHeartbeats 1000000 in
/-- Finite-field form of the team simulation of Lemma 7.1. The team-size exponent
is chosen before the finite field, RAM, private routines and all field return values.
The interior-bit budget is sublinear uniformly over these positive team sizes. -/
theorem lemma7_1 (D logDegree : ℕ) {α ξ γ : ℝ} (hα : α < 3) (hξ : 0 < ξ)
    (hsmall : ξ < 3/2) (horder : ξ ≤ α) (hγ : 0 < γ) :
    ∃ ω : ℝ, 0 < ω ∧
      (∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams:ℝ) ≤ (2:ℝ)^((n:ℝ)^ω) →
        (logWidth teams n:ℝ)^logDegree ≤ (n:ℝ)^γ) ∧
      (∀ reg c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams:ℝ) ≤ (2:ℝ)^((n:ℝ)^ω) →
        let w := logWidth teams n^(D+1)
        c*Wires.innerWidth teams reg w (Wires.sortExponent (block ξ n)) (w+1) ≤ n) ∧
      (∀ {pc reg k a m g : ℕ} {Q Γ : Type} [Fintype Q] {F : Type*} [Field F] [Fintype F]
        (P : TeamOpcode.Program pc reg k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a),
        ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, ∀ hr : 0 < teams, (teams:ℝ) ≤ (2:ℝ)^((n:ℝ)^ω) →
        ∀ other : ℕ, ∃ geo : Scale (machine P lib weights) pc reg k α ξ teams n other (logWidth teams n^(D+1))
          (Wires.sortExponent (block ξ n)), AtScale P lib weights geo hr) := by
  obtain ⟨v,hv,logs,ports,sites⟩ := uniform_installation D logDegree hα hξ hsmall horder hγ
  obtain ⟨u,hu,cap⟩ := exists_common_exponent (D+1) hα hξ
  refine ⟨min u v,lt_min hu hv,?_,?_,?_⟩
  · filter_upwards [logs,eventually_ge_atTop 1] with n h hn
    exact fun r hr hh => h r hr (admissible_smaller hn (min_le_right ..) hh)
  · intro reg c
    filter_upwards [ports reg c,eventually_ge_atTop 1] with n h hn
    exact fun r hr hh => h r hr (admissible_smaller hn (min_le_right ..) hh)
  · intro pc reg k a m g Q Γ _ F _ _ P lib weights
    let physical := machine P lib weights
    let C := 2*((programPrefix physical).length+k+reg+48)
    filter_upwards [sites P lib,cap C,eventually_installed P lib weights,eventually_ge_atTop 1] with n atSite room installed hn
    intro teams hr batch other
    let W := logWidth teams n^(D+1)
    let E := Wires.sortExponent (block ξ n)
    obtain ⟨orig,_⟩ := atSite teams hr (admissible_smaller hn (min_le_right ..) batch) other
    have budget := (room teams hr (admissible_smaller hn (min_le_left ..) batch)).1
    have hL := (log_dominates hr hn).1
    have hwide : logWidth teams n ≤ W := by simpa only [pow_one] using Nat.pow_le_pow_right hL (show 1 ≤ D+1 by omega)
    have hpre := Nat.mul_le_mul_left 2 (start_le physical k reg teams W n hr hn hwide)
    have hreserved : 2*freeStartWith physical teams k reg W n ≤ literal α n := hpre.trans (by rwa [← Nat.mul_assoc])
    let geo := Scale.of_reserved P lib physical orig hreserved
    refine ⟨geo,?_⟩
    intro pub regs advice free bounded d team pin ext ib hb sb S G rows
    have own (j : Fin teams) : (rows j).length ≤ 3*S.block.val := by
      have size := (G.processorFields team pin ext ib hb sb).row_length j
      let lit := entryLiteral physical (W+1) n (prefixCapacity teams k reg W n+1+freeWidth physical α k reg teams W n)
      change (rows j).length = lit+((other+1)-1)*link ξ (other+1) n+lit at size
      have he : lit = literal α n := geo.literalSize
      rw [size,he,Nat.add_sub_cancel]
      exact (show literal α n+other*link ξ (other+1) n+literal α n = 2*literal α n+other*link ξ (other+1) n by ring) ▸ geo.localInput
    refine ⟨own,?_⟩
    have hH : block ξ n ≤ n := by have h1 := geo.baseline.rowCapacity; have h2 := geo.baseline.localSort; omega
    exact installed other teams W _ d _ E S geo.fits hr geo.baseline geo.widened geo.dimensions geo.comparators hH
      bounded team pin ext ib hb sb own

end FieldProcessor

end BorderVNP
end Computability
end OAI
