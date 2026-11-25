import OAI.Computability.BorderVNP.DiagonalChosenBootPinStart
import OAI.Computability.BorderVNP.DiagonalJointBootedSupport

/-! # Positive pre-call support on the chosen residue reader's installed tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Pins TeamScales
open Branch Crossing MvPolynomial TeamContraction TeamContraction.ProcessorSlots
open CellMacro.Generator JointHeader
open scoped Classical

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
    {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {C : CommonField paid aux q k s ord}
    {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pinSize pc routines a link n ec : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally w pinSize)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
    (S : SiteData R r 64 32 w a) (fit : fitsWith physical 64 32 r w a R link n ec)
    (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word w)
    (L : Routing.WireLayout (R+1) r link)
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=64) physical a link L.header
local notation "place" => fun u : Fin (R+1) => ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "pack" => fun u : Fin (R+1) => reader.packetAt (place u)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinSize
local notation "off" => adviceOffsetWith physical r 32 64 w n
local notation "start" => freeStartWith physical r 32 64 w n
variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2200000 in
/-- Select the signed pin states for all positive exteriors of the actual
reader in one family. Both the gathered reference packet and the copies of
the geometric and private source bits are read from this same physical
site table, including arbitrary payload and padding positions. -/
theorem ChosenReader.booted_positive_sites (gen : Fragment IO) (fixed : Routing.Block (R+1))
    (pin : Fin indexWidth → Bool) (regions : JointRoom D start a boot geom)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^w) (hw : 0 < w) :
    let T := reader.startupSitesWith physical P S place fit D boot geom bootBits geomBits strings L.header
    let G := wiringWith physical P T indexWidth link n ec fit
    let args := fun u : Fin (R+1) => (arena).unitAddresses off (pack u)
    let frame := fun u => G.transferFrame u (args u).header (args u).dst
    let loc := fun u => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
    (∀ u, (args u).Fitted G u (pack u) (T.publicWords u) off ∧
      packetUnitBudget (args u).advice.count w (frame u) (loc u) ≤ T.limit.val) →
    ∃ B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
        BootedPinStart gen G T.publicWords T.registers args pin x.val u,
      ∀ x u, let ad := args u
        let F := G.processorFields u pin x.val ad.ibase ad.hbase ad.starbase
        (B x u).used ≤ T.limit.val ∧
        BootHeaderState F (frame u) ad.advice (pack u) (T.publicWords u)
          (observed L x.val fixed) (B x u).out (B x u).memory ∧
        JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  intro T G args frame loc ready
  have choose (x : {ext // PositiveExterior G args pin w ext}) (u : Fin (R+1)) :
      ∃ B : BootedPinStart gen G T.publicWords T.registers args pin x.val u,
      let ad := args u
      let F := G.processorFields u pin x.val ad.ibase ad.hbase ad.starbase
      B.used ≤ T.limit.val ∧
      BootHeaderState F (frame u) ad.advice (pack u) (T.publicWords u) (observed L x.val fixed) B.out B.memory ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
    obtain ⟨tail,same,length,header⟩ := positive_common_boot_header G args pin L fixed hw (fun _ => rfl)
      (fun u => (T.publicWords u 0).val) (fun u => (ready u).1.physical) x.val x.property
    obtain ⟨B,paid,read,source⟩ :=
      reader.booted_sitesCommon physical P S fit valuation entry totals extension L D boot geom bootBits geomBits strings
        gen tail length x.val header u pin regions copies ceiling (ready u).1 (x.property u).1
    change B.used ≤ jointBudget (args u).advice.count w+(frame u).readTicks+2 at paid
    have room := (ready u).2
    unfold packetUnitBudget at room
    refine ⟨B,paid.trans (by omega),?_,source⟩
    rw [same]
    exact read
  exact ⟨fun x u => (choose x u).choose,fun x u => (choose x u).choose_spec⟩

end Diagonal

end BorderVNP
end Computability
end OAI
