import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace
import OAI.Computability.BorderVNP.CubeRouteExteriorBootstrap

/-! # Choosing the signed header before the private routed payload and the live pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Branch Crossing VPVNP TeamScales TeamContraction JointHeader Routing
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {extra E dlog Q A B j : ℕ} (cube : FixedCube K) {s : EpochScales S (cube.pred+1) extra}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

/-- The same fixed header fits every chart reader at all sufficiently large
lengths. A preliminary layout has zero traffic and this positive header
extent, fixed before either input pin or a routed private assignment. Every
later true routing layout of this extent yields exactly the same header-only
exterior on the original physical wires. -/
theorem JointSchedule.eventually_blank_signed_layout (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (adv : ℕ → ℕ) (poly : PolynomiallyBounded adv) (c k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let T := adv (adviceScale b.σ b.ρ n)
      let symbols := alphabet s.α n
      let X := (R+1)*exterior ((s.τ:ℝ)/5) r n
      let blocks := blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1))
      let cap := declarationCap cube.pred symbols blocks cube.b cube.h cube.width
      let reserve := SeedPlan.profileReserve r n
      let tally := b.physical.tally n
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {C : CommonField e aux q l size ord} (chart : AdvisedBranch C)
        [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
        (reader : ChosenReader chart (R+1) r (b.physical.multBits n) tally (b.physical.word n) (T+6)),
        reader.charge ≤ c*(T+1)^k →
        let dim := pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ ι)
        let len := PositiveFields.width reserve cube.pred symbols cap (R+1) dim tally
        ∃ blank : WireLayout (R+1) r (b.physical.link n),
          blank.header = len ∧ 0<blank.header ∧ blank.width=(fun _ _ => 0) ∧
          ∀ (later : WireLayout (R+1) r (b.physical.link n)) (same : later.header=blank.header)
            (bits : List Bool) (old : bits.length=blank.header),
            exterior blank bits old (fun _ _ _ => false) =
              exterior later bits (old.trans same.symm) (fun _ _ _ => false) := by
  filter_upwards [b.eventually_lengths 0,b.eventually_startup_header,
    b.eventually_common_route_header (aux := aux) (q := q) cube adv poly c k] with n bounds fits header
  intro r R T symbols X blocks cap reserve tally l size ord C chart _ _ reader paid dim len
  have actual := header.2 chart reader paid
  have room : len ≤ r*b.physical.link n := fits _ actual.2.1
  let blank := headerOnly (List.replicate len false) bounds.teams.1 (by simpa using room)
  have length : blank.header=len := List.length_replicate
  refine ⟨blank,length,length.symm ▸ actual.1,rfl,?_⟩
  intro later same bits old
  exact (exterior_zero blank bits old).trans (exterior_zero later bits (old.trans same.symm)).symm

end Diagonal

end BorderVNP
end Computability
end OAI
