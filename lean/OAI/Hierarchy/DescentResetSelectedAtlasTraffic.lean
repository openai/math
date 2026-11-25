import OAI.Hierarchy.DescentResetSelectedAtlasShape
import OAI.Hierarchy.DescentResetAtlasDatePrice

namespace OAI
/-! # Program price of the original root atlas, with the measured prior wire banks -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "c₀" => S.groupWidth k tail i
local notation "bits₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "cut₀" => resetCut S k tail p f h i
local notation "rawCap" => (((capCalendar G.b S.rounds g S.height).take i).prod*256)
local notation "date₀" => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "e₀" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "mid₀" => (date₀).successor.middle
local notation "bound₀" => PhysicalReset.selected_cut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old

def selected_root_inputs : (date₀).RootInputs :=
  PhysicalReset.namedRoots G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀)
    nextM C packet oldLanes primitiveLanes printedBits old io floor (bound₀).1 (by
      have lo : laneBits (c₀+k) h bits₀≤c₀+k := Nat.min_le_left _ _
      change laneBits (c₀+k) h bits₀-k≤c₀
      omega)

theorem selected_stencil_shape : (date₀).StencilShape :=
  PhysicalReset.namedStencil G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀) nextM C packet
    oldLanes primitiveLanes printedBits old io floor (bound₀).2.1

local notation "roots₀" => selected_root_inputs (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
local notation "shape₀" => selected_stencil_shape (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
local notation "base₀" => (date₀).stageStart floor
local notation "control₀" => (mid₀).rootControlBits rawCap

def selected_atlas (count : Bank) : (date₀).Atlas :=
  PhysicalReset.namedAtlas G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀)
    nextM C packet oldLanes primitiveLanes printedBits old io floor shape₀ count

local notation "menu₀" count => selected_atlas (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes
  printedBits old io floor count
local notation "rc₀" count "," w => (date₀).rootPhase shape₀ base₀ count io.hubs g (2^n) roots₀ w
local notation "book₀" count "," w => PhysicalReset.atlasBook (menu₀ count) shape₀ base₀ count io.hubs g (2^n) roots₀ w

theorem selected_root_geometry :
    (roots₀).field=(mid₀).rootField ∧ (roots₀).Ht=GroupStage.depthBound old.degree n f g ∧
    (∀s x,(roots₀).old s x=io.wire x.val s.val) ∧ (mid₀).oldBlocks=2^k :=
  ⟨rfl,rfl,fun _ _=>rfl,rfl⟩

theorem selected_atlas_traffic (count : Bank) (w : ℕ) (live : i<S.length) (degreeAt : old.degree=D)
    (capacity : r.placement.cap=rawCap) (localRoom : 8*bits₀≤h)
    (rootRoom : 8*(date₀).successor.groupWidth≤h)
    (dimension : (c₀+k)*(c₀+k)≤h/2)
    (ranges : Nat.clog 2 (c₀+k+2)+(c₀+k+S.censusBits p)≤h/2)
    (space : (rc₀ count, w).PreparedFits (book₀ count, w)) :
    (rc₀ count, w).preparedTicks (book₀ count, w) space+7*names ((rc₀ count, w).preparedRoots (book₀ count, w) space) ≤
      (Projected.Receiver.rootCoefficient old.degree n (GroupStage.depthBound old.degree n f g) control₀).total 1 1 1*
      (S.hostSize i+S.hostSize i*chunks (2^c₀) (mid₀).signedLanes+(h+1)*2^(h/2)) := by
  have shape:=selected_atlas_shape r rates p h drift degree nextM packet oldLanes primitiveLanes printedBits
    old io.wire io.roster floor live degreeAt capacity localRoom rootRoom dimension ranges
  exact PhysicalReset.Atlas.atlas_traffic (menu₀ count) shape₀ base₀ count io.hubs g (2^n) roots₀ h
    control₀ w shape space

/-- Apply the date-wide cofinal tariff to the selected program at its actual old
venue and its computed retile, clipped root and shared table shapes. -/
theorem selected_atlas_invoice (count : Bank) (w localRate receiver saving lead exponent : ℕ)
    (quote : ∀ H groups stages u N b width rows fee : ℕ,
      u≤TerminalScale.scale S.height localRate → N≤TerminalScale.scale S.height localRate →
      b≤TerminalScale.scale S.height localRate → width≤TerminalScale.scale S.height receiver →
      rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤(Projected.Receiver.rootCoefficient D n (GroupStage.depthBound D n f g) u).total 1 1 1*
        (H+H*rows+(h+1)*2^(h/2)) → 1≤ stages →
      fee*w≤H*h*(lead*TerminalScale.scale S.height exponent)+
        H*(groups*stages)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving)
    (live : i<S.length) (degreeAt : old.degree=D) (capacity : r.placement.cap=rawCap)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(date₀).successor.groupWidth≤h)
    (dimension : (c₀+k)*(c₀+k)≤h/2)
    (ranges : Nat.clog 2 (c₀+k+2)+(c₀+k+S.censusBits p)≤h/2)
    (controls : control₀≤TerminalScale.scale S.height localRate ∧
      2^k≤TerminalScale.scale S.height localRate ∧ bits₀≤TerminalScale.scale S.height localRate)
    (unit : (date₀).successor.groupWidth≤TerminalScale.scale S.height receiver)
    (radix : S.radix=2^k) (groups : S.groupCount i=2^c₀)
    (space : (rc₀ count, w).PreparedFits (book₀ count, w)) :
    ((rc₀ count, w).preparedTicks (book₀ count, w) space+7*names ((rc₀ count, w).preparedRoots (book₀ count, w) space))*w ≤
      S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+
      S.initialSites/(2^S.height)^saving := by
  have rows:=selected_root_rows rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  have priced:=selected_atlas_traffic r rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old io floor count w live degreeAt capacity localRoom rootRoom dimension ranges space
  rw [degreeAt] at priced
  rw [groups]
  exact quote _ _ _ control₀ (2^k) bits₀ (date₀).successor.groupWidth _ _
    controls.1 controls.2.1 controls.2.2 unit rows priced (by rw [radix];exact Nat.two_pow_pos _)

/-- Coefficients are independent of the field, the reached placement and the
height. This supplies the complete height-dependent tariff used by the issuer. -/
theorem selected_atlas_date_price (D n f g localRate receiver ratio saving : ℕ) :
    ∃ lead exponent : ℕ, ∀ᶠ h : ℕ in Filter.atTop, ∀ height copies w : ℕ,
      height≤Nat.log 2 h → 2^h≤copies → w≤ratio*h →
      ∀ H groups stages u N b width rows fee : ℕ,
        u≤TerminalScale.scale height localRate → N≤TerminalScale.scale height localRate →
        b≤TerminalScale.scale height localRate → width≤TerminalScale.scale height receiver →
        rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
        fee≤(Projected.Receiver.rootCoefficient D n (GroupStage.depthBound D n f g) u).total 1 1 1*
          (H+H*rows+(h+1)*2^(h/2)) → 1≤ stages →
        fee*w≤H*h*(lead*TerminalScale.scale height exponent)+
          H*(groups*stages)*(lead*TerminalScale.scale height exponent)+copies/(2^height)^saving := by
  obtain ⟨lead,exponent,prices⟩:=Projected.Receiver.atlas_date_price D n (GroupStage.depthBound D n f g)
    localRate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  filter_upwards [prices] with h price
  intro height copies w age ambient bits H groups stages u N b width rows fee uFit nFit bFit widthFit work cost limbs
  exact price height H groups stages copies u N b width rows w fee age ambient uFit nFit bFit widthFit bits work cost limbs


end
end Hierarchy.DescentSixParty.NativePitch

end OAI
