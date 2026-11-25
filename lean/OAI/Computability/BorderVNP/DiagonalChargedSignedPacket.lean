import OAI.Computability.BorderVNP.DiagonalSignedProfilePlacement
import OAI.Computability.BorderVNP.DiagonalSignedProfileClock
import OAI.Computability.BorderVNP.DiagonalNativeGeometryWindow

/-! # Installing the charged physical geometry table on the signed evaluation branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Branch Crossing Cover VPVNP BurstRAM VerifierNetwork Packing ExternalSew TeamScales
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamContraction TeamContraction.ProcessorSlots JointHeader RoutingISA GeometryAdvice GeometryAdviceRate
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {extra E dlog Q A B j : ℕ} (cube : FixedCube K) {s : EpochScales S (cube.pred+1) extra}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

/-- Literal separation, allocation and branch time for a specified raw gate
count, padded size and word interface on the fixed signed site. -/
def SignedTableStartupAt (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (physical : UniversalMachine.Program) (adv : ℕ → ℕ) (c k factor n raw gates ceiling o field desc : ℕ) : Prop :=
      let r := stretch b.ρ n
      let W := b.physical.word n
      let R := b.physical.teamsPred n
      let ξ := (s.τ:ℝ)/5
      let link := b.physical.link n
      let lit := literal s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let entries := (epochCopies S)^T*V
      let reserve := SeedPlan.profileReserve r n
      let cap := declarationCap cube.pred (alphabet s.α n)
        (blocksFor ((R+1)*exterior ξ r n : ℕ) (cube.h*cube.b) ((alphabet s.α n)^(cube.pred+1))) cube.b cube.h cube.width
      let input := adv (adviceScale b.σ b.ρ n)
      let first := freeStartWith physical r 32 64 W n
      let free := FieldProcessor.freeWidth physical s.α 32 64 r W n
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField e aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r (b.physical.multBits n) (b.physical.tally n) W (input+6)),
        reader.charge ≤ c*(input+1)^k →
        let dim := pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ ι)
        let len := PositiveFields.width reserve cube.pred (alphabet s.α n) cap (R+1) dim (b.physical.tally n)
        let arena : StartupArena := ⟨R+1,r,lit,link,len,reader.packetBitCount⟩
        let ell := stripeWidth (packetWords gates reserve o field*W) r
        let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
        let fresh := arena.next+7*dir.candidates
        raw ≤ ceiling ∧ gates = ceiling ∧ reader.packetBitCount ≤ r ∧ 0 < len ∧
          JointRoom dir first free (signedBootStripe first) (Allocation.stripe fresh reserve gates o field (lit/4) ell) ∧
          Allocation.stop fresh reserve gates o field W < 2^W ∧
          ∀ (loc : ReaderPlacement W) (f : BroadcastFrame) (frame : ℕ), f.Fits W frame →
            f.processors = r → f.teams = R+1 → f.link = TeamScales.link ξ (R+1) n →
            factor*(jointBudget (reader.packetAt loc).bits.length W+f.readTicks+2+((pinSetup.slots+17*(r*lit)+1)+
              GeometryAdviceRate.ticks gates reserve o field W)) ≤ TeamScales.ticks ξ r n

/-- Every concrete evaluator receipt on this length supplies the matching
reader installation for the original output arity and descriptor address. -/
def SignedReaderInstallAt (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (physical : UniversalMachine.Program) (adv : ℕ → ℕ) (c k factor degree U n : ℕ) : Prop :=
  let r := stretch b.ρ n
  let W := b.physical.word n
  let reserve := SeedPlan.profileReserve r n
  ∀ {X Y P : Type} [Fintype X] [Fintype Y] [Fintype P] {active o field scanTeams scanSites scanEntries : ℕ}
    (hist : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active≤reserve)
    (emit : Frame ((X ⊕ Fin reserve) ⊕ P) (Fin o × Fin field)) (x : X → Bool), 1 ≤ field →
    NativeGeometryReceipt U degree n r W scanTeams scanSites scanEntries hist order fit emit x →
    ∀ desc : ℕ, let ceiling := geometryGateCeiling U degree r n
      let table := geometryTable hist order fit emit x
      SignedTableStartupAt (aux:=aux) (q:=q) cube b physical adv c k factor n
        table.size (table.reserve ceiling).size ceiling o field desc

/-- Use the exact measured gate table as the parameter of its physical reader
deployment. The delivery bounds in the receipt may have counted any number
of scan rows, as the placement needs only the paid table evaluation and writes. -/
theorem SignedReaderInstallAt.startup {b : JointSchedule.{0} s (E+1) dlog Q A B j}
    {physical : UniversalMachine.Program} {adv : ℕ → ℕ} {c k factor degree U n : ℕ}
    (h : SignedReaderInstallAt (aux:=aux) (q:=q) cube b physical adv c k factor degree U n)
    {X Y P : Type} [Fintype X] [Fintype Y] [Fintype P] {active o field scanTeams scanSites scanEntries : ℕ}
    (hist : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active)
    (fit : active ≤ SeedPlan.profileReserve (stretch b.ρ n) n)
    (emit : Frame ((X ⊕ Fin (SeedPlan.profileReserve (stretch b.ρ n) n)) ⊕ P) (Fin o × Fin field))
    (x : X → Bool) (fieldPos : 1 ≤ field) (desc : ℕ)
    (receipt : NativeGeometryReceipt U degree n (stretch b.ρ n) (b.physical.word n)
      scanTeams scanSites scanEntries hist order fit emit x) :
    let raw := geometryTable hist order fit emit x
    let ceiling := geometryGateCeiling U degree (stretch b.ρ n) n
    SignedTableStartupAt (aux:=aux) (q:=q) cube b physical adv c k factor n
      raw.size (raw.reserve ceiling).size ceiling o field desc := by
  exact h hist order fit emit x fieldPos receipt desc

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
/-- Install the very same true table, header, program, literal, common field
packet and free description directory when the evaluator returns its measured
receipt. The share includes the actual lower-memory geometry endpoint. -/
theorem JointSchedule.eventually_install_signed_receipts (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (physical : UniversalMachine.Program) (adv : ℕ → ℕ) (poly : PolynomiallyBounded adv)
    (c k factor degree U : ℕ) (deg : E+2 ≤ dlog) :
    ∀ᶠ n : ℕ in atTop, SignedReaderInstallAt (aux:=aux) (q:=q) cube b physical adv c k factor degree U n := by
  filter_upwards [b.eventually_common_route_header (aux:=aux) (q:=q) cube adv poly c k,
    b.eventually_signed_profile_placement cube deg physical,
    b.eventually_signed_profile_clock (aux:=aux) (q:=q) adv poly c k factor,
    b.physical.eventually_nativePackets (G:=e) (aux:=aux) (q:=q) adv poly c k 1]
    with n header place clock short
  unfold SignedReaderInstallAt
  intro r₀ W₀ reserve₀ X Y P _ _ _ active o field scanTeams scanSites scanEntries hist order fit emit x fieldPos receipt
    desc ceiling source
  unfold SignedTableStartupAt
  intro r W R ξ link lit start V T entries reserve cap input first free l size ord common chart _ _ reader small
    dim len arena ell dir fresh
  let table := source.reserve ceiling
  have gates : table.size=ceiling := receipt.2.1
  have tablePaid : GeometryAdviceRate.ticks table.size reserve o field W+
      packetWords table.size reserve o field*W ≤ r*width n (95/100:ℝ) := by
    rw [gates]
    exact receipt.2.2.2
  have ready := header.2 chart reader small
  let loc : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have bit := short chart reader small loc.valuation loc.entry loc.row loc.column loc.totals loc.extension
  change 1*((reader.packetAt loc).bits.length+_+_+1+_) < r at bit
  rw [one_mul,reader.packetAt_length] at bit
  have copied : reader.packetBitCount ≤ r := by omega
  have fits := place desc len reader.packetBitCount reserve table.size o field ready.2.1 copied fieldPos
    ((Nat.le_add_left ..).trans tablePaid)
  exact ⟨receipt.1,gates,copied,ready.1,fits.1,fits.2,fun L f a mem procs teams peers =>
    clock chart reader small L f a _ mem procs teams peers ((Nat.le_add_right ..).trans tablePaid)⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
/-- The common threshold precedes the chart, the later pins and the emitted
gate choices. The canonical header includes the declarations and *all* team
subtotal words. Its exact reserved table fits the frozen geometry stripe and
native RAM, with the full signed reference packet and arbitrary fixed clock
share. The emitter may contain absolute addresses computed from the ceiling. -/
theorem JointSchedule.eventually_charged_signed_packet (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (physical : UniversalMachine.Program) (adv : ℕ → ℕ) (poly : PolynomiallyBounded adv)
    (c k factor degree U : ℕ) (power : degree+(E+2) ≤ dlog) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let W := b.physical.word n
      let R := b.physical.teamsPred n
      let ξ := (s.τ:ℝ)/5
      let link := b.physical.link n
      let lit := literal s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let entries := (epochCopies S)^T*V
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let rows := routingRows (boundary S start T) cells entries ((R+1)*V)
      let reserve := SeedPlan.profileReserve r n
      let cap := declarationCap cube.pred (alphabet s.α n)
        (blocksFor ((R+1)*exterior ξ r n : ℕ) (cube.h*cube.b) ((alphabet s.α n)^(cube.pred+1))) cube.b cube.h cube.width
      let input := adv (adviceScale b.σ b.ρ n)
      let first := freeStartWith physical r 32 64 W n
      let free := FieldProcessor.freeWidth physical s.α 32 64 r W n
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField e aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r (b.physical.multBits n) (b.physical.tally n) W (input+6)),
        reader.charge ≤ c*(input+1)^k →
        let dim := pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ ι)
        let len := PositiveFields.width reserve cube.pred (alphabet s.α n) cap (R+1) dim (b.physical.tally n)
        let arena : StartupArena := ⟨R+1,r,lit,link,len,reader.packetBitCount⟩
        ∀ {X Y P : Type} [Fintype X] [Fintype Y] [Fintype P] {active o field mult : ℕ}
          (hist : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active≤reserve)
          (emit : Frame ((X ⊕ Fin reserve) ⊕ P) (Fin o × Fin field)) (x : X → Bool),
          1 ≤ field → ((mult*hist.size+active:ℕ):ℝ) ≤ r*(n:ℝ)^(92/100:ℝ) →
          hist.size+emit.size+o*field ≤ mult*hist.size+U*rows*(logWidth r n)^degree →
          let ceiling := geometryGateCeiling U degree r n
          let table := (geometryTable hist order fit emit x).reserve ceiling
          let ell := stripeWidth (packetWords table.size reserve o field*W) r
          ∀ desc : ℕ, let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
            let fresh := arena.next+7*dir.candidates
            table.size = ceiling ∧ reader.packetBitCount ≤ r ∧ 0 < len ∧
              JointRoom dir first free (signedBootStripe first) (Allocation.stripe fresh reserve table.size o field (lit/4) ell) ∧
              Allocation.stop fresh reserve table.size o field W < 2^W ∧
              ∀ (loc : ReaderPlacement W) (f : BroadcastFrame) (frame : ℕ), f.Fits W frame →
                f.processors = r → f.teams = R+1 → f.link = TeamScales.link ξ (R+1) n →
                factor*(jointBudget (reader.packetAt loc).bits.length W+f.readTicks+2+((pinSetup.slots+17*(r*lit)+1)+
                  GeometryAdviceRate.ticks table.size reserve o field W)) ≤ TeamScales.ticks ξ r n := by
  have deg : E+2 ≤ dlog := (Nat.le_add_left ..).trans power
  filter_upwards [b.eventually_install_signed_receipts (aux:=aux) (q:=q) cube physical adv poly c k factor degree U deg,
    b.eventually_reserved_geometry_charge degree U power] with n deploy charge
  intro r W R ξ link lit start V T entries cells rows reserve cap input first free
    l size ord common chart _ _ reader small dim len arena X Y P _ _ _ active o field mult
    hist order fit emit x fieldPos paid cost ceiling table ell desc
  exact (deploy hist order fit emit x fieldPos (charge hist order fit emit x fieldPos paid cost) desc chart reader small).2

end Diagonal

end BorderVNP
end Computability
end OAI
