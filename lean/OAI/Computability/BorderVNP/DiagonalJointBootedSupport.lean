import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalSupportedPrefixDomain
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorHeader

/-! # The signed processor on the actual jointly prepared exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit BorderVNP.Cube CellMacro.Generator JointHeader Routing
open scoped Classical BigOperators

variable {R r t d link inner n w : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))

/-- At every positive shared exterior the header observed on the fixed physical
block starts with the evaluation bit. Every other block supplies these same
digits, including on exteriors which later fail a route or directory check. -/
theorem positive_common_boot_header (hw : 0 < w) (size : ∀ i, (args i).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (ext : Exterior R r link → Bool) (positive : PositiveExterior G args pin w ext) :
    ∃ tail : List Bool, observed L ext fixed=true::tail ∧
      ∃ length : (true::tail).length=L.header,
        ∀ b, (L.exteriorEquiv ext).broadcast b = headerBits (true::tail) length := by
  obtain ⟨equal,tag,_⟩ := observed_positive G args pin ext L hw size base fit (fun u => (positive u).2) (positive 0).1 fixed
  cases shape : observed L ext fixed with
  | nil => simp [shape] at tag
  | cons v tail =>
    have on : v=true := Option.some.inj (show some v=some true by simpa only [shape,List.head?_cons] using tag)
    subst v
    have length := (congrArg List.length shape).symm.trans (observed_length ..)
    refine ⟨tail,rfl,length,fun b => (equal b).trans ?_⟩
    have digits := observed_bits L ext fixed
    let get := fun s : {l : List Bool // l.length=L.header} => headerBits s.val s.property
    exact digits.symm.trans (congrArg get (Subtype.ext shape : (⟨_,observed_length L ext fixed⟩ : {l : List Bool // l.length=L.header}) = ⟨_,length⟩))

section Installed

variable {dim box lanes selectors symbols a ec : ℕ}

/-- Execute and retain the true boot and pin dictionary on every startup-admitted
exterior, before deciding whether all teams can reach the private call. The stored
header is exactly the original block's observed bits, with no canonicality
requirement on any payload or unused link position. -/
theorem exists_joint_booted_starts (physical : UniversalMachine.Program)
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (data : SiteData R r 64 32 w a) (packet : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n ec) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1)) (hw : 0 < w) :
    let G := wiringWith physical (withStartup (signedBody id)).program (data.withPacket packet) d link n ec fit
    let frame := fun u => G.transferFrame u (args u).header (args u).dst
    let loc := fun u => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
    (∀ u, (args u).header=L.header) →
    (∀ u, (args u).Fitted G u (packet u) (data.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
    (∀ u, LoopFits w (loc u)) → (∀ u, (data.publicWords u 0).val+112 ≤ (args u).dst) →
    (∀ u, (args u).advice.dst+(packet u).bits.length ≤ (args u).dst ∨
      (args u).dst+(args u).header ≤ (args u).advice.dst) →
    ∃ B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
        BootedPinStart gen G data.publicWords data.registers args pin x.val u,
      ∀ x u, (B x u).used ≤ jointBudget (args u).advice.count w+(frame u).readTicks+2 ∧
        BootHeaderState (G.processorFields u pin x.val (args u).ibase (args u).hbase (args u).starbase)
          (frame u) (args u).advice (packet u) (data.publicWords u) (observed L x.val fixed) (B x u).out (B x u).memory := by
  intro G frame loc size ready loops front apart
  have result (x : {ext // PositiveExterior G args pin w ext}) (u : Fin (R+1)) :
      ∃ B : BootedPinStart gen G data.publicWords data.registers args pin x.val u,
        B.used ≤ jointBudget (args u).advice.count w+(frame u).readTicks+2 ∧
          BootHeaderState (G.processorFields u pin x.val (args u).ibase (args u).hbase (args u).starbase)
            (frame u) (args u).advice (packet u) (data.publicWords u) (observed L x.val fixed) B.out B.memory := by
    obtain ⟨tail,same,length,header⟩ := positive_common_boot_header G args pin L fixed hw size
      (fun u => (data.publicWords u 0).val) (fun u => (ready u).physical) x.val x.property
    rw [same]
    exact bootedPinStart_of_common physical id gen data packet fit args pin L x.val u tail length header
      (size u) (ready u) (loops u) (x.property u).1 (front u) (apart u)
  exact ⟨fun x u => (result x u).choose,fun x u => (result x u).choose_spec⟩

end Installed

namespace BootedPinStart

variable {dim box lanes selectors symbols : ℕ} {gen : Fragment IO}
    (id : TableEntry dim box lanes selectors symbols → ℕ)
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)
local notation "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)

/-- The real positive masked contribution of a shared input vanishes when
even one team cannot complete its pre-call preparation. -/
theorem product_zero (limit burst clock : ℕ) (ext : Exterior R r link → Bool)
    (agrees : PositiveExterior G args pin w ext)
    (outside : ¬ PinStart.preCallSupport (fun x u => (B x u).start) id ext) :
    (∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args pin limit burst clock ext u)=0 := by
  apply PinStart.product_zero_off_support (fun x u => (B x u).start) ext agrees outside
  exact fun u h => (B ⟨ext,agrees⟩ u).zero_of_empty id limit burst clock h

local notation "active" => PinStart.preCallSupport (fun x u => BootedPinStart.start (B x u)) id
local notation "X" => {ext // PositiveExterior G args pin w ext ∧ active ext}

variable (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (x : {ext // PositiveExterior G args pin w ext ∧
        PinStart.preCallSupport (fun z u => (B z u).start) id ext}) (u : Fin (R+1)),
      let boot := B ⟨x.val,x.property.1⟩ u
      PositiveContinuation id gen n (pub u) (TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n))
        boot.start.bank boot.memory boot.pins boot.used limit)

/-- Use the calibrated continuation only after the tuple of physical prefixes
establishes joint reachability. All earlier pin states and traces are retained. -/
noncomputable def supportedTeam (x : X) (u : Fin (R+1)) : PositiveTeam id gen n w :=
  (next x u).team burst cap (B ⟨x.val,x.property.1⟩ u).frameFit

/-- The supported team has the original booted registers, memory and pin dictionary. -/
theorem supportedTeam_start (x : X) (u : Fin (R+1)) :
    (supportedTeam id B limit burst cap next x u).start = (B ⟨x.val,x.property.1⟩ u).start := rfl

/-- The true signed positive branch, with its exact remaining clock after
bootstrap, on each shared exterior used by the private decoder. -/
theorem supportedTeam_value (paid : ∀ x u, (B x u).used ≤ limit) (x : X) (u : Fin (R+1)) :
    let T := supportedTeam id B limit burst cap next x u
    positiveMaskedNativeValue G (signedBody id) mac pub reg args pin limit burst (n^25) x.val u =
      boundedValue (signedBody id) T.pub (install gen n T.routines) T.bank T.memory
        (T.limit-T.used) T.burst (n^25) :=
  (B ⟨x.val,x.property.1⟩ u).team_value id limit burst (paid _ u) cap (next x u)

end BootedPinStart
end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
