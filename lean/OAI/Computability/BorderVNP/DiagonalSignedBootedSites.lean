import OAI.Computability.BorderVNP.CellSparseExteriorDriver
import OAI.Computability.BorderVNP.DiagonalChosenJointBoot
import OAI.Computability.BorderVNP.DiagonalChosenSignedExtension

/-! # The installed signed task and cube fields on the reachable physical pin starts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine TeamScales
open Branch Crossing TeamContraction TeamContraction.ProcessorSlots GeometryAdvice
open CellMacro.Generator JointHeader BorderVNP.Cube TeamSite
open scoped Classical

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
    {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {C : CommonField paid aux q k s ord}
    {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pinSize a link n ec cubeN box lanes copies symbols : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally w pinSize)
    (id : TableEntry cubeN box lanes copies symbols → ℕ)
    (S : SiteData R r 64 32 w a)
local notation3 (prettyPrint := false) "prog" => (withStartup (signedBody id)).program
local notation3 (prettyPrint := false) "physical" => TimedProcessor.machine prog (siteLibrary SparseExterior.driver) (fun _ => some false)
variable (fit : fitsWith (TimedProcessor.machine (withStartup (signedBody id)).program
      (siteLibrary SparseExterior.driver) (fun _ => some false)) 64 32 r w a R link n ec)
    (valuation entry totals : Fin (R+1) → ℕ)
    (L : Routing.WireLayout (R+1) r link)
    (layout : Fin (R+1) → SignedTaskArena.Layout) (raw team subtotal : Fin (R+1) → ℕ)
    (old : Fin (R+1) → Fin 81 → Word w) (fresh profile gates outputCount outputWidth geomOff ell d blocks : ℕ)
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=n) (reg:=64) physical a link L.header
local notation3 (prettyPrint := false) "overlay" => fun v => CubeHeaderInstall.jointFields v
  fresh profile gates outputCount outputWidth geomOff ell d cubeN blocks box lanes symbols
local notation3 (prettyPrint := false) "exts" => fun u : Fin (R+1) =>
  overlay ((layout u).extension (raw u) (team u) (subtotal u) (old u))
local notation3 (prettyPrint := false) "place" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (exts u)
local notation3 (prettyPrint := false) "packs" => fun u : Fin (R+1) => reader.packetAt (place u)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinSize
local notation3 (prettyPrint := false) "off" => adviceOffsetWith physical r 32 64 w n
local notation3 (prettyPrint := false) "startAt" => freeStartWith physical r 32 64 w n
variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 6500 in
/-- The one timed signed program with its sparse private routine starts on the
actual reader packet with the complete cube, signed-task and geometry words.
Every positive exterior gives these same fields at the selected boot memory. -/
theorem ChosenReader.signed_booted_sites (fixed : Routing.Block (R+1)) (pin : Fin indexWidth → Bool)
    (regions : JointRoom D startAt a boot geom)
    (copyRoom : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^w) (hw : 0 < w) :
    let T := reader.startupSitesWith physical prog S place fit D boot geom bootBits geomBits strings L.header
    let G := wiringWith physical prog T indexWidth link n ec fit
    let args := fun u : Fin (R+1) => (arena).unitAddresses off (packs u)
    let frame := fun u => G.transferFrame u (args u).header (args u).dst
    let loc := fun u => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
    (∀ u, (args u).Fitted G u (packs u) (T.publicWords u) off ∧
      packetUnitBudget (args u).advice.count w (frame u) (loc u) ≤ T.limit.val) →
    ∃ B : (x : {z // PositiveExterior G args pin w z}) → (u : Fin (R+1)) →
        BootedPinStart SparseExterior.driver G T.publicWords T.registers args pin x.val u,
      ∀ x u, let ad := args u
        let F := G.processorFields u pin x.val ad.ibase ad.hbase ad.starbase
        let hdr := observed L x.val fixed
        let pub := T.publicWords u
        let mem := (B x u).memory
        (B x u).used ≤ T.limit.val ∧
        BootHeaderState F (frame u) ad.advice (packs u) pub hdr (B x u).out mem ∧
        JointImage D startAt a boot geom (bootBits u) (geomBits u) strings u.val F ∧
        LocalRow.BootPins pub (frame u) (exts u) hdr mem ∧
        ∀ j : Fin 81, mem ((pub 0).val+31+j.val) =
          (layout u).extension (raw u) (team u) (subtotal u) (overlay (old u)) j := by
  intro T G args frame loc ready
  obtain ⟨B,kept⟩ := reader.booted_positive_sites physical prog S fit valuation entry totals exts L
    D boot geom bootBits geomBits strings SparseExterior.driver fixed pin regions copyRoom ceiling hw ready
  refine ⟨B,?_⟩
  intro x u ad F hdr pub mem
  obtain ⟨paid,packet,image⟩ := kept x u
  obtain ⟨pins,fields⟩ := reader.signedStartup_boot (layout u) arena (valuation u) (entry u) (totals u)
    (raw u) (team u) (subtotal u) (old u) fresh profile gates outputCount outputWidth geomOff ell d cubeN blocks box
    lanes symbols packet
  rw [(layout u).cube_extension_signed (raw u) (team u) (subtotal u) (old u)] at pins
  exact ⟨paid,packet,image,pins,fields⟩

end Diagonal

end BorderVNP
end Computability
end OAI
