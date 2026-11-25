import OAI.Computability.BorderVNP.PackedHistoryGeometryRate
import OAI.Computability.BorderVNP.TransmissionChosenArenaRate
import OAI.Computability.BorderVNP.RoutingISATickBudget

/-! # Clock for the selected stretch reader's physical history prefix

The packet decoder, repeated broadcast reads, local pin guess, and guarded history
circuit share one team clock. The header length is bounded by the actual unordered
link allocation. The width of each guessed pin field is the complete literal size of
the wired program. The stretch exponent is fixed before the chart and the public frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP BurstRAM VerifierNetwork Filter
open TeamContraction TeamContraction.ProcessorSlots TeamScales RoutingISA RoutingISA.Pins
open GeometryAdvice PackedHistoryCircuit

private theorem rounded_exterior_clock {ξ : ℝ} (hx : 0 < ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 2000 * exterior ξ r n ≤ TeamScales.ticks ξ r n := by
  filter_upwards [eventually_rpow_gap (show 1-ξ < 1-ξ/2 by linarith) 2000] with n gap
  intro r
  apply Nat.le_floor
  have floor := Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)) (1-ξ))
  change ((width n (1-ξ)):ℝ) ≤ _ at floor
  simp only [exterior,Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ = (r:ℝ) * (2000 * (width n (1-ξ):ℝ)) := by ring
    _ ≤ (r:ℝ) * (2000 * (n:ℝ)^(1-ξ)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left gap (by positivity)

private theorem width_positive {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) : 1 ≤ logWidth r n := by
  have nn : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rr : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have two : 2 ≤ 2*(n:ℝ)*r := by nlinarith
  have log : (1:ℝ) ≤ Real.logb 2 (2*(n:ℝ)*r) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr two
  exact_mod_cast (show (1:ℝ) ≤ logWidth r n from log.trans (Nat.le_ceil _))

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {G : PaidIdentity K dim labels} {aux : ι → K} {q : ℕ}
variable {pc reg routines m g : ℕ} {Q Γ : Type} [Fintype Q]

set_option maxRecDepth 5000 in
set_option maxHeartbeats 5500000 in
/-- On the polylogarithmic word schedule, every sufficiently large stretch input fits
the genuine processor geometry and every charged terminal profile uses strictly less
than a quarter of the rounded team clock. All private chart and frame choices are made
after the common input-length threshold. -/
theorem eventually_chosen_profile_clock (D E : ℕ) {α ξ : ℝ} (hα : (95/100:ℝ)<1-α/3)
    (hx : 0<ξ) (order : ξ<α/3) :
    ∃ ω : ℝ, 0<ω ∧ ∀ (sched : StretchSchedule), sched.ρ ≤ ω →
      ∀ (f : ℕ → ℕ), PolynomiallyBounded f → ∀ (A C : ℕ) (H : ℝ), 0 ≤ H →
      ∀ (P : TeamOpcode.Program pc reg 32 routines) (lib : Fin routines → TeamSite.Macro Q Γ m g),
      ∀ᶠ n : ℕ in atTop, let r := stretch sched.ρ n
      let T := f (adviceScale sched.σ sched.ρ n)
      let teams := sched.teamsPred n
      let W := sched.word n
      let link := TeamScales.link ξ (teams+1) n
      let free := siteFree P lib α r W n
      let e := Wires.sortExponent (block ξ n)
      W = logWidth r n ^ (E+1) →
      ∃ geom : SiteGeometry P lib α ξ r n teams W e,
      ∀ {k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
        {R : CommonField G aux q k s ord} (chart : AdvisedBranch R) [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
        (reader : ChosenReader chart (teams+1) r (sched.multBits n) (sched.tally n) W (T+6)),
        reader.charge ≤ A*(T+1)^C →
        ∀ (L : Routing.WireLayout (teams+1) r link), 0 < L.header →
        ∀ {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V], ∀ {active reserve o b : ℕ} (history : Frame (X ⊕ Y) (V ⊕ Unit))
          (profile : Y ≃ Fin active) (fit : active ≤ reserve)
          (emit : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : X → Bool),
        1 ≤ b → b ≤ W →
        ((history.size+emit.size+3*(reserve-active)+3+reserve+o*b : ℕ):ℝ) ≤
          H*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^D →
        let arena := reader.startupArena (n := n) P lib free link L.header
        let table := geometryTable history profile fit emit x
        reader.packetBitCount ≤ r ∧ Allocation.stop arena.next reserve table.size o b W < 2^W ∧
        ∀ (S : SiteData teams r reg 32 W free) (valuation entry totals : Fin (teams+1) → ℕ)
          (ext : Fin (teams+1) → Fin 81 → Word W) (u : Fin (teams+1)),
        let places := fun v => ReaderPlacement.inArena arena (valuation v) (entry v) (totals v) (ext v)
        let B := reader.siteOperands P lib S places geom.fits L.header u
        let packet := reader.packetAt (places u)
        4*(jointBudget packet.bits.length W+B.broadcast.readTicks+2+
          (pinSetup.slots+17*B.layout.count+1+GeometryAdviceRate.ticks table.size reserve o b W)) <
          TeamScales.ticks ξ r n := by
  obtain ⟨wg,hg,geometry⟩ := eventually_profile_geometry D (E+1) hα
  have xa : ξ ≤ α := by linarith
  obtain ⟨ws,hs,sites⟩ := eventually_siteGeometry E (show α<3 by linarith)
    hx (show ξ<3/2 by linarith) xa
  refine ⟨min wg ws,lt_min hg hs,?_⟩
  intro sched rho f poly A C H hH P lib
  filter_upwards [sites P lib,geometry H 1 hH (by norm_num) (TeamSite.Processor.machine P lib) 32 reg,
    sched.eventually_nativePackets (G := G) (aux := aux) (q := q) f poly A C 1,
    sched.eventually_chosenArena (G := G) (aux := aux) (q := q) f poly A C hx xa P lib,
    eventually_literals_le order 17,rounded_exterior_clock hx,eventually_ge_atTop 1] with
    n site pay packets space literals clock hn
  intro r T teams W link free e word
  have nn : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have floor := Nat.floor_le (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ((n:ℝ)^sched.ρ))
  change (r:ℝ) ≤ 2^((n:ℝ)^sched.ρ) at floor
  have small (a : ℝ) (ha : sched.ρ ≤ a) : (r:ℝ) ≤ 2^((n:ℝ)^a) :=
    floor.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le nn ha))
  have hr : 1 ≤ r := Nat.le_floor (by
    norm_cast
    exact Real.one_le_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _))
  have geom : SiteGeometry P lib α ξ r n teams W e := word ▸ site r hr (small ws (rho.trans (min_le_right _ _))) teams
  refine ⟨geom,?_⟩
  intro k s ord R chart _ _ reader charge L hdr X Y V _ _ _ active reserve o b history profile fit emit x hb _ size arena table
  have wide : logWidth r n ≤ W := by rw [word,pow_succ]; exact Nat.le_mul_of_pos_left _ (pow_pos (width_positive hn hr) _)
  have hw : 1 ≤ W := (width_positive hn hr).trans wide
  have space' := space chart reader charge L e hdr geom wide
  have arenaRoom : arena.next+r*n < 2^W := space'.2.2
  have ceiling : arena.next < 2^W := (Nat.le_add_right _ _).trans_lt arenaRoom
  have pub := pay r W arena.next history profile fit emit x hr (small wg (rho.trans (min_le_left _ _))) hb hw
    size (by rw [word,Nat.cast_pow,one_mul])
  have stop : Allocation.stop arena.next reserve table.size o b W ≤ arena.next+r*n := pub.2.1
  refine ⟨space'.1,stop.trans_lt arenaRoom,?_⟩
  intro S valuation entry totals ext u places B packet
  have runs := reader.arena_fits P lib S geom.fits valuation entry totals ext L u hdr space'.1 ceiling
  have reads := B.broadcast.readTicks_le_exterior runs.2.1 ξ n rfl
  change B.broadcast.readTicks ≤ 90*(exterior ξ r n+(teams+1)+1) at reads
  let loc := places u
  have jp := packets chart reader charge loc.valuation loc.entry loc.row loc.column loc.totals loc.extension
  change 1*(packet.bits.length+jointBudget packet.bits.length W+_+1+_) < r at jp
  have pin : B.layout.count = r * literal α n := by
    change (reader.siteOperands P lib S places geom.fits L.header u).layout.count = _
    rw [reader.siteOperands_arena P lib S geom.fits valuation entry totals ext L u]
    change r * arena.literal = _
    rw [show arena.literal = literal α n from geom.literalSize]
  let edge : Routing.Block (teams+1) := ⟨(⟨0,by have := L.three; omega⟩,⟨1,by have := L.three; omega⟩),Nat.zero_lt_one⟩
  have blockFit : L.header ≤ r*link := by have := L.fits edge; omega
  have peers : 0 < link := Nat.pos_of_mul_pos_left (hdr.trans_le blockFit)
  have count : teams+1 ≤ width n (1-ξ) := (Nat.div_pos_iff.mp peers).2
  have xr : r ≤ exterior ξ r n := Nat.le_mul_of_pos_right _ (by omega)
  have xt : teams+1 ≤ exterior ξ r n := count.trans (Nat.le_mul_of_pos_left _ hr)
  have once : 17*B.layout.count ≤ exterior ξ r n := by rw [pin,← Nat.mul_assoc]; exact literals r
  have hg' : width n (95/100:ℝ) ≤ width n (1-ξ) :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nn (by linarith))
  have gc : GeometryAdviceRate.ticks table.size reserve o b W ≤ exterior ξ r n :=
    (Nat.le_add_right _ _).trans (pub.1.trans (Nat.mul_le_mul_left r hg'))
  have fixed : pinSetup.slots ≤ 100 := by decide
  have target := clock r
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
