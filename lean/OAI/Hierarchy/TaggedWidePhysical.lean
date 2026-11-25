import OAI.Hierarchy.TaggedWideStep
import OAI.Hierarchy.TaggedWideDyadicMenu
import OAI.Hierarchy.TaggedWideElectrical
import OAI.Hierarchy.TaggedPruneCount

namespace OAI
/-! # Joining cofinal dyadic slot allocations to their routed physical host -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst CatalystSubstitution ThreeFlat TaggedPrune Filter Real
open scoped BigOperators

/-- The two compaction tags and the activity flag fit the actual dyadic
payload uniformly over the parent width interval. This discharges the
metadata premise of the physical shorter lane at every installed type. -/
theorem DyadicGeometry.metadata {κ A δ ξ : ℝ} {n : ℕ} (g : DyadicGeometry κ A n)
    (u : ℝ → ℝ) (hκ : 0<κ) (hA : 1<A) :
    let m := g.menu u δ ξ
    ∀ᶠ x in WideParent.large κ A,∀ i,1+m.height i x+m.height i x ≤ m.payload i x := by
  intro m
  have large : Tendsto (fun x : WideParent κ A => (x.h:ℝ)) (WideParent.large κ A) atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  obtain ⟨_,smaller⟩ := eventually_wide_formats hκ hA WideParent.h WideParent.w
    m.height m.payload m.T m.Y m.ratios m.tall m.heightRatio m.widthRatio
    (Eventually.of_forall (@WideParent.formats κ A))
  apply eventually_all.mpr
  intro i
  obtain ⟨cut,works⟩ := TaggedShorterBudget.metadata_fits (g.index i).2 hκ (by norm_num : (0:ℝ)≤3)
  filter_upwards [smaller,large.eventually_ge_atTop cut] with x shorter high
  have hw := (le_logb_iff_rpow_le x.formats.1 (Nat.cast_pos.mpr x.formats.2.1)).mp x.formats.2.2.1
  have small := (shorter i).1
  have positive : 1<x.h := x.property.1.1
  have invoice : 1+m.height i x+m.height i x ≤ 3*x.h := by omega
  exact works x.h x.w (1+m.height i x+m.height i x) (g.index i).2 high hw
    (by exact_mod_cast invoice) le_rfl

/-- All shared control sorts can take their height from the actual padded
row count. No cost or gap for an induction hypothesis is assumed of the
protocol's physical evidence. -/
theorem dyadicLayout_of_parts {F : Type*} [Field F] {k n c M : ℕ} {u : ℝ → ℝ}
    {s κ A r ε baseline p q Q σ L δ η ξ P d : ℝ}
    (geometry : DyadicGeometry κ A n) (hu : TaggedWidthProfile.Admissible s u)
    (purchase : TaggedShorterBudget.Choice u A (ε/2) p q Q σ L δ η ξ)
    (hk : 0<k) (hM : 0<M) (hκ : 0<κ) (hr : 0≤r) (base : 0<baseline)
    (one : 1≤P) (degree : 0≤d) (rows : WideParent κ A → Fin c → ℕ)
    (counts : ∀ᶠ x in WideParent.large κ A, ∀ j,
      (rows x j:ℝ) ≤ P*((2:ℝ)^x.h*(log (x.h:ℝ))^d))
    (physical : ∀ᶠ x in WideParent.large κ A,
      let B := (geometry.menu u δ ξ).bank x
      let t := fun j => controlHeight x.h (rows x j)
      ∀ (Y : ∀ i,(B i).Output F k) (Z : ∀ j,Approximation F k (pins (t j) (t j))),
        ∃ b : PrunedBoard F k x.h x.w M (bankCalls B Y (controlCalls t Z)),
          (b.cost:ℝ) ≤ P*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^d) ∧
          (x.h:ℝ)*2^x.h+b.selectors ≤ P*((2:ℝ)^x.h*x.h*(log (x.h:ℝ))^d)) :
    Nonempty (WideLayout F k u κ A r ε baseline) := by
  classical
  let menu := geometry.menu u δ ξ
  let H (x : WideParent κ A) (j : Fin c) := controlHeight x.h (rows x j)
  let limit := WideParent.large κ A
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) limit atTop := tendsto_comap
  have highR : Tendsto (fun x : WideParent κ A => (x.h:ℝ)) limit atTop :=
    tendsto_natCast_atTop_atTop.comp high
  have hP : 0<P := zero_lt_one.trans_le one
  have price := geometry.paid hu hκ.le purchase
  have control : ∀ᶠ x in limit, ∀ j, x.h ≤ H x j ∧
      (H x j:ℝ) ≤ 2*x.h ∧ (2:ℝ)^(H x j) ≤ (2*P)*((2:ℝ)^x.h*(log (x.h:ℝ))^d) := by
    filter_upwards [counts,(tendsto_log_atTop.comp highR).eventually_ge_atTop 1,
      high.eventually (GapScale.eventual_polynomial 0 P d degree)] with x count loghi enough j
    have small : P*(2*(x.h:ℝ))^d ≤ (2:ℝ)^x.h := by simpa [gap] using enough
    have hh := x.formats.1
    let R := P*(log (x.h:ℝ))^d
    have Rone : 1 ≤ R := one_le_mul_of_one_le_of_one_le one (Real.one_le_rpow loghi degree)
    have Rs : R ≤ (2:ℝ)^x.h := (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith [(Real.log_le_self (Nat.cast_nonneg x.h))] :
        log (x.h:ℝ) ≤ 2*(x.h:ℝ)) degree) hP.le).trans small
    have nn : 0 < x.h := by exact_mod_cast (zero_lt_one.trans hh : 0<(x.h:ℝ))
    obtain ⟨lo,_,up,sz⟩ := control_padding nn Rone Rs (show (rows x j:ℝ) ≤ (2:ℝ)^x.h*R by
      apply (count j).trans_eq; dsimp [R]; ring)
    exact ⟨lo,by exact_mod_cast up,sz.trans_eq (by dsimp [R];ring)⟩
  let Zprice := (c:ℝ)*(2*P)*(2:ℝ)^(1+r)
  let ordinary := max P (baseline*Zprice)
  have bounds := high.eventually (TaggedPrune.eventually_half_gap hκ hP hk hM d)
  refine ⟨{
    toWideMenu := menu
    controls := c
    controlHeight := H
    fraction := 36*ξ
    exponent := 2
    ρ := 1/(2*(M:ℝ))
    ordinary := ordinary
    power := d
    fraction_pos := by linarith [purchase.xi_pos]
    exponent_pos := by norm_num
    outer_pos := by positivity
    ordinary_pos := hP.trans_le (le_max_left ..)
    allocation := price.mono (fun _ q => q.1)
    weighted := price.mono (fun _ q => q.2)
    taller := control.mono (fun _ x j => (x j).1)
    board := ?_ }⟩
  filter_upwards [physical,control,bounds] with x get quality discounted
  let B := menu.bank x
  let os (Y : ∀ i,(B i).Output F k) (Z : ∀ j,Approximation F k (pins (H x j) (H x j))) :=
    bankCalls B Y (controlCalls (H x) Z)
  dsimp only at get
  choose b cost entropy using get
  refine ⟨fun Y Z => WideHost.host (b Y Z).catalyst (b Y Z).localPart (os Y Z) (b Y Z).cuts,
    fun Y Z => ⟨?_,?_⟩⟩
  · rw [PrunedBoard.hostSize_eq]
    have q := control_work (H x) hr (by positivity : (0:ℝ)≤2*P) (by norm_num : (0:ℝ)≤2)
      x.formats.1 (fun j => (quality j).2.2) (fun j => (quality j).2.1)
    have lpos := (Real.log_pos x.formats.1).le
    have xprice : 0 ≤ (2:ℝ)^x.h*x.w*(log (x.h:ℝ))^d :=
      mul_nonneg (by positivity) (Real.rpow_nonneg lpos _)
    have cprice : 0 ≤ (2:ℝ)^x.h*(x.h:ℝ)^(1+r)*(log (x.h:ℝ))^d :=
      mul_nonneg (by positivity) (Real.rpow_nonneg lpos _)
    have cx := (cost Y Z).trans (mul_le_mul_of_nonneg_right (le_max_left P (baseline*Zprice)) xprice)
    have cz := (mul_le_mul_of_nonneg_left q base.le).trans_eq (mul_assoc baseline Zprice _).symm
    have fit := cz.trans (mul_le_mul_of_nonneg_right (le_max_right P (baseline*Zprice)) cprice)
    simpa only [mul_add] using add_le_add cx fit
  · let t := b Y Z
    have old := WideHost.old_gap t.catalyst t.encoding t.route t.links t.routing t.tables hM
      x.formats.2.1 hk t.localPart (os Y Z) t.cuts t.realizes
    apply Approximation.Gap.mono _ old
    have wide := (le_logb_iff_rpow_le x.formats.1 (Nat.cast_pos.mpr x.formats.2.1)).mp x.formats.2.2.1
    exact (show 1/(2*(M:ℝ))*(2:ℝ)^x.h*x.w=(2:ℝ)^x.h*x.w/(2*M) by ring).le.trans
      (discounted x.w t.selectors wide (entropy Y Z))

/-- Data obtained from the protocol compiler at fixed price and geometry.
The numerical sorting and recursive gap estimates are supplied by the
induction. The compiler is tested on the original physical site/selector
semantics, including invalid words and all idle modules. -/
structure ProtocolReadout (F : Type*) [Field F] (k : ℕ) (u : ℝ → ℝ) (κ A δ ξ : ℝ) where
  types : ℕ
  controls : ℕ
  M : ℕ
  M_pos : 0<M
  geometry : DyadicGeometry κ A types
  factor : ℝ
  exponent : ℝ
  one : 1≤factor
  degree : 0≤exponent
  rows : WideParent κ A → Fin controls → ℕ
  counts : ∀ᶠ x in WideParent.large κ A, ∀ j,
    (rows x j:ℝ) ≤ factor*((2:ℝ)^x.h*(log (x.h:ℝ))^exponent)
  physical : ∀ᶠ x in WideParent.large κ A,
    let B := (geometry.menu u δ ξ).bank x
    let t := fun j => controlHeight x.h (rows x j)
    ∃ b : StaticBoard F k x.h x.w M B t,
      (b.cost:ℝ) ≤ factor*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^exponent) ∧
      (x.h:ℝ)*2^x.h+b.selectors ≤ factor*((2:ℝ)^x.h*x.h*(log (x.h:ℝ))^exponent)

theorem widthReductions_of_protocol {F : Type*} [Field F] {k : ℕ} (hk : 0<k)
    {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (protocols : ∀ A : ℝ,1<A → TaggedShorterBudget.Cofinal (P A))
    (readout : ∀ {u : ℝ → ℝ} {κ A ε p q Q σ L δ η ξ : ℝ},
      TaggedWidthProfile.Admissible (profile F k 1) u → 0<κ → 1+κ≤A → 0<ε →
      P A p q Q σ L → TaggedShorterBudget.Choice u A (ε/2) p q Q σ L δ η ξ →
      Nonempty (ProtocolReadout F k u κ A δ ξ)) :
    WidthReductions F k := by
  apply widthReductions_of_cofinal_layouts protocols
  intro u κ A r ε baseline p q Q σ L δ η ξ hu hκ hA hr _ hε base hP purchase
  obtain ⟨m⟩ := readout hu hκ hA hε hP purchase
  exact dyadicLayout_of_parts m.geometry hu purchase hk m.M_pos hκ hr base m.one m.degree
    m.rows m.counts (by
      filter_upwards [m.physical] with x ready
      dsimp only at ready ⊢
      obtain ⟨board,cost,count⟩ := ready
      intro Y Z
      obtain ⟨b,price,selectors⟩ := board.install Y Z
      exact ⟨b,by simpa only [price] using cost,by simpa only [selectors] using count⟩)

end Hierarchy.Tagged

end
end OAI
