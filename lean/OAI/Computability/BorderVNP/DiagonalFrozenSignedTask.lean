import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomStartup
import OAI.Computability.BorderVNP.DiagonalCommonRouteHeader
import OAI.Computability.BorderVNP.DiagonalReservedGeometryClock
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.DiagonalFixedSignedSites
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom
import OAI.Computability.BorderVNP.RoutingISASignedReaderRoom
import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # The signed task on the frozen geometry and the chosen reader's actual banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins VPVNP VPVNP.BurstRAM
open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena TeamContraction TeamContraction.JointHeader
open TeamContraction.ProcessorSlots GeometryAdvice _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- Allocate the exact label sorter and cells above the reserved public gate
table, and lay out the signed task using the fixed paid/cube scalar numbering.
Only the table ceiling and dimensions enter. All pin and history values may
be supplied after this layout has been computed. -/
noncomputable def JointSchedule.frozenSignedTask (n l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories) : SignedTaskArena.Layout :=
  let r := stretch b.ρ n
  let R := b.physical.teamsPred n+1
  let w := b.physical.word n
  let start := CoverScale.initialDepth (Epoch.Cube D) r n
  let T := epochs s.τ n
  let V := CoverScale.sites (Epoch.Cube D) start
  let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
  let cables := (boundary S start T).edges+4*(R*V)
  let bundles := (epochCopies S)^T*V
  let axes := Fintype.card (Epoch.Cube D)
  let marked := DeckGrid.seedSiteCapacity n r axes (start-1)
  let body := BottomGridBank.bodyBudget (DeckGrid.seedBoxCapacity n r axes (start-1) (Fintype.card (DeckGrid.Direction axes)))
  let base := Allocation.stop (initial.next+7*dir.candidates) profile ceiling outputs field w
  let traffic := R*exterior ((s.τ:ℝ)/5) r n
  let sizes := selectedSizes base (alphabet s.α n) traffic cells cables dir.candidates R r n profile
  let arena := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
  let par := pairedTableParameters (l+1) size
  let expBits := Nat.clog 2 (r*(2*l+1)+1)
  let scalars := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
  ⟨arena,cube.cubeID G,physicalParameters arena dirs n bundles marked par expBits scalars w
    (headerFactor*logWidth r n) body⟩

/-- The counts, opaque-record envelope and two sort banks installed in the
signed report stage are computed from this same frozen schedule. The list of
cube scalar indices keeps the paid and cube entries in disjoint positions. -/
theorem JointSchedule.frozenSignedTask_reports (n l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories) :
    let r := stretch b.ρ n
    let R := b.physical.teamsPred n+1
    let W := b.physical.word n
    let start := CoverScale.initialDepth (Epoch.Cube D) r n
    let T := epochs s.τ n
    let V := CoverScale.sites (Epoch.Cube D) start
    let bundles := (epochCopies S)^T*V
    let axes := Fintype.card (Epoch.Cube D)
    let marked := DeckGrid.seedSiteCapacity n r axes (start-1)
    let body := BottomGridBank.bodyBudget (DeckGrid.seedBoxCapacity n r axes (start-1) (Fintype.card (DeckGrid.Direction axes)))
    let par := pairedTableParameters (l+1) size
    let scalars := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
    task.id = cube.cubeID G ∧ task.p.parameters = par ∧ task.dim = par+scalars ∧
    task.p.report = reportBounds task.cube bundles marked par (Nat.clog 2 (r*(2*l+1)+1)) scalars W ∧
    task.p.report.uses = R*(par*Nat.clog 2 (r*(2*l+1)+1)) ∧ task.p.report.countWidth = W ∧
    task.p.siteWidth = headerFactor*logWidth r n ∧ task.p.bodyCap = body ∧
    task.p.sorted = dirs.sorted ∧ task.p.padded = dirs.padded ∧ task.p.stops = dirs.stops ∧
    task.p.bundlePayload = dirs.bundlePayload ∧ task.p.bundleInverse = dirs.bundleInverse :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable {ι : Type} [Fintype ι] {aux : ι → F} {q l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField G aux q l size ord} {chart : AdvisedBranch common}
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    {R r w pin : ℕ} (reader : ChosenReader chart (R+1) r w w w pin)

local notation "queryWords" => Fintype.card (Board.Physical (pairedTableParameters (l+1) size) pin w (G.Entry ⊕ ι))
local notation "guessWords" => Fintype.card (Guess (Fin (pairedTableParameters (l+1) size)) reader.gridRank
  (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

omit [NeZero D] in
/-- The physical reader packet has precisely the literal width, header, and
copy count used to reserve the frozen task. The scalar addresses placed
inside that packet play no role in its length. -/
theorem ChosenReader.frozenTask_startupArena {physical : UniversalMachine.Program} {pc n ec : ℕ} {α ξ : ℝ}
    (geo : FieldProcessor.Scale physical pc 64 32 α ξ r n R w ec) (link header : ℕ) :
    reader.startupArenaWith (n:=n) (reg:=64) physical (FieldProcessor.freeWidth physical α 32 64 r w n)
      link header = (⟨R+1,r,literal α n,link,header,reader.packetBitCount⟩ : StartupArena) := by
  unfold ChosenReader.startupArenaWith
  rw [geo.literalSize]

/-- The reader's valuation, six-word gate program, and serialized totals share
the actual task's memory. Its extended frame names this team and uses the full
hardware word for each subtotal in the common header. -/
noncomputable def ChosenReader.frozenTaskPlacement (task : SignedTaskArena.Layout) (initial : StartupArena)
    (team : Fin (R+1)) (old : Fin 81 → Word w) : ReaderPlacement w :=
  task.readerPlacement initial queryWords guessWords reader.gates
    (rawAddress initial task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap)
    team.val w old

omit [NeZero D] in
/-- Actual startup addresses and report-extension words before any geometry
overlay. The third signed-frame argument is the bit width of a subtotal. -/
theorem ChosenReader.frozenTaskPlacement_fields (task : SignedTaskArena.Layout) (initial : StartupArena)
    (team : Fin (R+1)) (old : Fin 81 → Word w) :
    let place := reader.frozenTaskPlacement task initial team old
    place.valuation = task.valuation w ∧ place.entry = task.entry w queryWords guessWords reader.gates ∧
    place.totals = task.tallyBits ∧ place.row = initial.ibase ∧ place.column = initial.hbase ∧
    place.extension = task.extension
      (rawAddress initial task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap)
      team.val w old := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩



omit [NeZero D] in
/-- The extended frame assigns words 33, 34, 36, 38, 39, 40 and 95 to the
dimension, local accumulator, raw claims, team count, team ordinal, subtotal
width and parameter count. -/
theorem ChosenReader.frozenTaskPlacement_reportWords (task : SignedTaskArena.Layout) (initial : StartupArena)
    (team : Fin (R+1)) (old : Fin 81 → Word w) :
    let x := (reader.frozenTaskPlacement task initial team old).extension
    let raw := rawAddress initial task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
    x 2 = TeamTapeInputEmit.word w task.dim ∧ x 3 = TeamTapeInputEmit.word w task.after.localBase ∧
    x 5 = TeamTapeInputEmit.word w raw ∧ x 7 = TeamTapeInputEmit.word w task.cube.teams ∧
    x 8 = TeamTapeInputEmit.word w team.val ∧ x 9 = TeamTapeInputEmit.word w w ∧
    x 64 = TeamTapeInputEmit.word w task.p.parameters := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

omit [NeZero D] in
/-- The actual geometry and cube-header overlays preserve the signed count
and report operands in the final packet, including the physical team ordinal
and the width of its subtotal words. -/
theorem ChosenReader.frozenTaskPlacement_jointWords (task : SignedTaskArena.Layout) (initial : StartupArena)
    (team : Fin (R+1)) (old : Fin 81 → Word w) (fresh gates outputs field off stripe : ℕ) :
    let base := (reader.frozenTaskPlacement task initial team old).extension
    let a := task.cube.header
    let x := CubeHeaderInstall.jointFields base fresh a.profile gates outputs field off stripe
      a.d task.cube.n a.blocks task.cube.b task.cube.h task.cube.s
    let raw := rawAddress initial a.profile task.cube.n a.d a.cap
    x 2 = TeamTapeInputEmit.word w task.dim ∧ x 3 = TeamTapeInputEmit.word w task.after.localBase ∧
    x 5 = TeamTapeInputEmit.word w raw ∧ x 7 = TeamTapeInputEmit.word w task.cube.teams ∧
    x 8 = TeamTapeInputEmit.word w team.val ∧ x 9 = TeamTapeInputEmit.word w w ∧
    x 64 = TeamTapeInputEmit.word w task.p.parameters :=
  reader.frozenTaskPlacement_reportWords task initial team old

omit [NeZero D] in
/-- The physical addresses used by the signed reference packet are word
addresses of the admitted task, before any pin contents are known. -/
theorem ChosenReader.frozenTaskPlacement_fits (task : SignedTaskArena.Layout) (initial : StartupArena)
    (team : Fin (R+1)) (old : Fin 81 → Word w)
    (endFit : task.endAddress w queryWords guessWords reader.gates < 2^w) :
    let place := reader.frozenTaskPlacement task initial team old
    place.valuation < 2^w ∧ place.entry < 2^w ∧ place.totals < 2^w := by
  change task.valuation w < _ ∧ task.entry w queryWords guessWords reader.gates < _ ∧ task.tallyBits < _
  unfold SignedTaskArena.Layout.endAddress SignedTaskArena.Layout.entry DiagonalResidueRAM.gateBase
    SignedTaskArena.Layout.valuation at *
  omega

/-- A bound on the number of output fields suffices to reserve the signed
task after the length-only gate ceiling, even if later instructions refer
to addresses inside that task. No emitter or accepted history is involved. -/
theorem JointSchedule.eventually_frozen_ceiling_ticks (U degree : ℕ) (power : degree+(E+2) ≤ dlog) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let reserve := SeedPlan.profileReserve r n
      ∀ outputs field : ℕ, 1≤field → reserve+outputs*field ≤ geometryGateBudget U degree r n →
        GeometryAdviceRate.ticks (geometryGateCeiling U degree r n) reserve outputs field (b.physical.word n)+
          GeometryAdviceRate.packetWords (geometryGateCeiling U degree r n) reserve outputs field*b.physical.word n ≤
          r*width n (95/100:ℝ) := by
  filter_upwards [b.eventually_numeric_geometry_charge degree power (2*((U:ℝ)+8)) (by positivity)] with n clock
  intro r reserve outputs field fieldPos fit
  let g := geometryGateBudget U degree r n
  let mass := ((U:ℝ)+8)*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree
  have floor : (g:ℝ) ≤ mass := Nat.floor_le (by positivity)
  have small : (g+reserve+outputs*field:ℕ) ≤ g+g := by omega
  have counted : ((g+reserve+outputs*field:ℕ):ℝ) ≤ (2*((U:ℝ)+8))*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree := by
    calc
      _ ≤ (g:ℝ)+g := by exact_mod_cast small
      _ ≤ mass+mass := add_le_add floor floor
      _ = _ := by dsimp only [mass]; ring
  exact (clock fieldPos (show geometryGateCeiling U degree r n≤4*g by rfl) counted).2

/-- The serialized packet of the reserved gate table fits at the same lengths. -/
theorem JointSchedule.eventually_frozen_ceiling_packet (U degree : ℕ) (power : degree+(E+2) ≤ dlog) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let reserve := SeedPlan.profileReserve r n
      ∀ outputs field : ℕ, 1≤field → reserve+outputs*field ≤ geometryGateBudget U degree r n →
        GeometryAdviceRate.packetWords (geometryGateCeiling U degree r n) reserve outputs field*b.physical.word n ≤
          r*width n (95/100:ℝ) := by
  filter_upwards [b.eventually_frozen_ceiling_ticks cube U degree power] with n room
  intro r reserve outputs field pos fit
  exact (Nat.le_add_left _ _).trans (room outputs field pos fit)

/-- The selected positive header fits this fixed task. Its aligned raw claims
end at the first input pin. Every tally digit and reader address is below the
native cutoff, with the threshold uniform over all admitted readers. -/
theorem JointSchedule.eventually_frozen_signed_task (φ : K →+* F) (q : ℕ)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k headerFactor : ℕ) :
    ∃ C power : ℕ, ∀ᶠ n : ℕ in atTop, ∀ l, n=l+1 →
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let W := b.physical.word n
      let link := b.physical.link n
      let lit := literal s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let entries := (epochCopies S)^T*V
      let reserve := SeedPlan.profileReserve r n
      let symbols := alphabet s.α n
      let X := (R+1)*exterior ((s.τ:ℝ)/5) r n
      let cap := declarationCap cube.pred symbols (blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1)))
        cube.b cube.h cube.width
      let lim := f (adviceScale b.σ b.ρ n)
      Nonempty (SeedPlan S n r (start-1) T (width n s.α) headerFactor Q) →
      ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r W W W (lim+6)), reader.charge≤c*(lim+1)^k →
        let par := pairedTableParameters (l+1) size
        let scalars := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
        let len := PositiveFields.width reserve cube.pred symbols cap (R+1) (par+scalars) W
        let initial : StartupArena := ⟨R+1,r,lit,link,len,reader.packetBitCount⟩
        let query := Fintype.card (Board.Physical par (lim+6) W (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
        let guesses := Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
        ∀ (desc ceiling outputs field : ℕ) (dirs : GeometryDirectories), 1≤field →
          GeometryAdviceRate.packetWords ceiling reserve outputs field*W ≤ r*width n (95/100:ℝ) →
          let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
          let task := b.frozenSignedTask cube n l size headerFactor initial dir reserve ceiling outputs field dirs
          let raw := rawAddress initial reserve cube.pred symbols cap
          task.ScalarRoom W query guesses reader.gates (C*(r*n+1)^power) ∧
            task.endAddress W query guesses reader.gates < 2^W ∧
            initial.next ≤ task.cube.header.header ∧ raw+(R+1)*(par+scalars)*W = initial.ibase ∧
            initial.frame+30 < 2^W ∧ initial.ibase+(par+2)*(lim+6) ≤ task.tallyBits ∧
            initial.hbase+(par+2)*(lim+6) ≤ task.tallyBits ∧
            initial.dense+(6+3*reader.gates+query)*W ≤ task.tallyBits := by
  obtain ⟨C,power,room⟩ := b.eventually_signed_from_startup (aux := φ ∘ cube.table) (q := q) cube f hf c k headerFactor
  refine ⟨C,power,?_⟩
  filter_upwards [room,b.eventually_common_route_header (aux := φ ∘ cube.table) (q := q) cube f hf c k,
    b.physical.eventually_nativePackets (G := G) (aux := φ ∘ cube.table) (q := q) f hf c k 1,
    eventually_ge_atTop 1] with n before header packets hn
  intro l eqn r R W link lit start V T entries reserve symbols X cap lim seed size ord common chart _ _ reader cost
    par scalars len initial query guesses desc ceiling outputs field dirs fieldPos packetLimit dir task raw
  let sample := reader.nativePacket 0 0 0 0 0 (fun _ => 0)
  have budget := packets chart reader cost 0 0 0 0 0 (fun _ => 0)
  change 1*(sample.bits.length+_+_+1+_) < r at budget
  let dummy : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have counted : sample.bits.length = reader.packetBitCount := reader.packetAt_length dummy
  have copied : reader.packetBitCount ≤ r := by omega
  have hr := stretch_one b.ρ n
  have α : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have litLe : lit ≤ n := Nat.floor_le_of_le (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ))
      (show 1-(s.α:ℝ)/3 ≤ 1 by linarith))
  have litPos : 1 ≤ lit := Nat.le_floor (by
    simpa using Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ))
      (show 0 ≤ 1-(s.α:ℝ)/3 by linarith [s.alpha_small]))
  have charged := before l eqn seed dir len reader.packetBitCount (r*n) reserve ceiling outputs field
    (header.2 chart reader cost).2.1 copied (Nat.mul_pos hr hn) (Nat.mul_le_mul_left r litLe) le_rfl
    rfl rfl rfl (le_refl 2) rfl rfl fieldPos packetLimit (cube.cubeID G) dirs chart reader cost
  have valid : task.endAddress W query guesses reader.gates < 2^W := charged.2.2
  have layout : initial.next ≤ task.cube.header.header := by
    change initial.next ≤ Allocation.stop (initial.next+7*dir.candidates) reserve ceiling outputs field W
    unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp
    omega
  have countedWidth : reader.packetBitCount = W*(6+3*reader.gates+query+81)+(par+2)*(lim+6) := rfl
  have pins : (par+2)*(lim+6) ≤ initial.count := by
    change _ ≤ r*lit
    exact ((Nat.le_add_left _ _).trans (countedWidth ▸ copied)).trans (Nat.le_mul_of_pos_right _ litPos)
  have entryBits : (6+3*reader.gates+query)*W ≤ initial.copied := by
    change _ ≤ reader.packetBitCount
    rw [countedWidth,Nat.mul_comm (6+3*reader.gates+query)]
    exact (Nat.mul_le_mul_left W (Nat.le_add_right _ 81)).trans (Nat.le_add_right _ _)
  have addr := (rawAddress_room task initial (reserve:=reserve) (axes:=cube.pred) (groups:=symbols)
    (cap:=cap) (width:=W) rfl).2.1
  exact ⟨charged.2.1,valid,layout,addr,task.reader_room initial layout pins entryBits valid⟩

end Diagonal

end BorderVNP
end Computability
end OAI
