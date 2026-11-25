import OAI.Computability.BorderVNP.CubeTeamOwnedArenaSetup
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot
import OAI.Computability.BorderVNP.CubeScatterArenaDelivered
import OAI.Computability.BorderVNP.TransmissionInverseBit

/-! # Scanner metadata in the returned native group schedule

The decoder writes the claimed row array and its chosen coordinate. The
minimum check is read-only. The group schedule writes only the three arrays
beginning at the end of the powers table. Consequently every earlier
scanner operand retains its decoded or pinned value, and the owner array
contains exactly the schedule's greedy owners.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open LocalRow CubeHeaderInstall TeamContraction.ProcessorSlots

/-- Addresses below the weight array precede each of the three arrays written
by the native group schedule. -/
theorem Layout.schedule_before (a : Layout) {wl : GroupWeights.Layout} {tl : TeamNative.Layout}
    {before after : ℕ → ℕ} (run : GroupWeights.ScheduleResult wl tl before after)
    (weights : wl.weights = a.groupWeights) (totals : tl.totals = a.teamTotals)
    (owners : tl.owners = a.ownerBase) {x : ℕ} (hx : x < a.groupWeights) : after x = before x := by
  have ht : a.groupWeights ≤ a.teamTotals := Nat.le_add_right ..
  have ho : a.teamTotals ≤ a.ownerBase := Nat.le_add_right ..
  apply run.other
  · intro k _; rw [weights]; omega
  · intro k; rw [totals]; omega
  · intro k _; rw [owners]; omega

private theorem primary_image (a : Layout) (saved : ℕ) (orig : ℕ → ℕ) {x : ℕ}
    (hx : x < a.header.header) : powerHeaderImage a saved orig x = orig x := by
  have ex := arenaExtents a
  have hp : a.header.header ≤ a.header.packetBase := by unfold Inputs.packetBase; omega
  have bank : a.header.packetBase ≤ a.packetEnd := ex.1
  have power : a.packetEnd+8+a.h ≤ a.powerBase := ex.2.1
  unfold powerHeaderImage
  rw [headerImage_outside _ _ _ _ _ _ (.inl hx)]
  simp [CubePowers.image,show ¬ a.powerBase ≤ x by omega]

/-- The exact native boot postcondition and the subsequent minimum and group
schedule returns supply every word needed by the team scanner. Rows and coordinate
are the actual raw broadcast readings, even before identifying a passing tuple. -/
theorem Layout.scannerWords_of_schedule {w : ℕ} (a : Layout) (pub : Arg → Word w)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    {bits : List Bool} {orig : Memory w}
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits orig)
    (decl : Broadcast a.n a.header.d a.header.cap)
    {bootRegs : Bank w} {bootMem : Memory w}
    (decoded : DecodedRows a (readings pub) f.dst decl (readings orig) (.ofWords bootRegs bootMem))
    {mac : TeamOpcode.Macros w 8} {es minRegs minMem}
    (minimum : Runs pub mac CubeLengths.minimum bootRegs bootMem es minRegs minMem)
    (wl : GroupWeights.Layout) (tl : TeamNative.Layout) {final : ℕ → ℕ}
    (scheduled : GroupWeights.ScheduleResult wl tl (readings minMem) final)
    (groups : wl.groups = a.header.d) (weights : wl.weights = a.groupWeights)
    (totals : tl.totals = a.teamTotals) (owners : tl.owners = a.ownerBase)
    (axes : a.header.a = a.n+1) (primary : (pub 0).val+112 ≤ a.header.header)
    (positive : 0 < a.header.d) (stopFit : a.stop < 2^w) (labelsFit : a.alphabet < 2^w) :
    a.ScannerWords (readings pub 0) f.team (readCode (a.n+1) decl.1)
      (fun g => (TeamNative.owner tl.r (wl.weight (readings minMem)) g.val).val) (readings pub) final
      (fun p j => readCode (a.header.cap+1) (decl.2 p j)) := by
  have same : minMem = bootMem := minimum.memory_eq_of_storeFree (by decide)
  subst minMem
  obtain ⟨image,loaded,actual,claimed,axis,rows,_⟩ := decoded
  change readings bootMem = powerHeaderImage a f.dst (readings orig) at image
  have keep (x : ℕ) (hx : x < a.groupWeights) : final x = readings bootMem x :=
    a.schedule_before scheduled weights totals owners hx
  have dec := a.declaration_before_schedule axes
  have denseEnd : a.header.header+13+a.header.entries+a.header.d*a.header.d*(a.n+1) ≤ a.groupWeights :=
    dec.trans (min_le_left ..)
  have primaryKeep (k : ℕ) (hk : k < 112) : final ((pub 0).val+k) = readings bootMem ((pub 0).val+k) :=
    keep _ (by omega)
  have fieldKeep (k : ℕ) (hk : k < 13) : final (a.header.header+k) = readings bootMem (a.header.header+k) :=
    keep _ (by omega)
  have prim (k : ℕ) (hk : k < 112) : final ((pub 0).val+k) = readings orig ((pub 0).val+k) := by
    rw [primaryKeep k hk,image]
    exact primary_image _ _ _ (by omega)
  obtain ⟨_,single,vertex,publicLe,cell,stop⟩ := a.separated
  have vpub : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  have views : a.pairBase ≤ a.stop := (Nat.le_add_right ..).trans (cell ▸ stop)
  have own : a.ownerBase ≤ a.pairBase := (Nat.le_add_right ..).trans a.source_order.2.2
  have strideBound : a.pairStride ≤ a.stop := by
    have lo := Nat.le_mul_of_pos_right a.pairStride (pow_pos positive 2)
    exact lo.trans ((Nat.le_add_left ..).trans a.orderedViews_before_tables)
  have pinned (k v : ℕ) (hk : k < 112) (operand : a.operand k = some v) (fits : v < 2^w) :
      final ((pub 0).val+k) = v := (prim k hk).trans
    (pins.arenaOperand a old fresh profile gates outputs width off ell operand fits)
  have setup : (rowLayout a.header a.b a.h a.powerBase).Loaded a.n (readings pub) final :=
    ⟨(primaryKeep 59 (by decide)).trans loaded.d,(primaryKeep 60 (by decide)).trans loaded.axes,
      (primaryKeep 61 (by decide)).trans loaded.bc,(primaryKeep 62 (by decide)).trans loaded.power,
      (primaryKeep 63 (by decide)).trans loaded.header,(fieldKeep 7 (by decide)).trans loaded.blocks,
      (fieldKeep 8 (by decide)).trans loaded.bank,fun j hj => (keep (a.powerBase+j) (by
        change a.powerBase+j < a.powerBase+(a.n+1); omega)).trans (loaded.powers j hj)⟩
  have static : readings bootMem (a.header.header+6) = a.rowSelectorBits := by
    rw [image,powerHeaderImage,headerImage_field _ _ _ _ _ _ (by decide) (by decide)]
    rfl
  refine ⟨rfl,setup,(fieldKeep 0 (by decide)).trans actual,(fieldKeep 1 (by decide)).trans claimed,?_,
    (prim 0 (by decide)).trans pins.team,pinned 56 _ (by decide) rfl labelsFit,
    pinned 77 _ (by decide) rfl (own.trans_lt (views.trans_lt stopFit)),
    pinned 78 _ (by decide) rfl ((vpub.trans publicLe).trans_lt (views.trans_lt stopFit)),
    pinned 85 _ (by decide) rfl (views.trans_lt stopFit),pinned 86 _ (by decide) rfl (strideBound.trans_lt stopFit),
    pinned 88 _ (by decide) rfl ((single.trans (vpub.trans publicLe)).trans_lt (views.trans_lt stopFit)),
    (fieldKeep 5 (by decide)).trans axis,(fieldKeep 6 (by decide)).trans static,?_⟩
  · intro x y j
    let k := (CubeLengths.entryOrder a.header.d (a.n+1) ((x,y),j)).val
    have hk : k < a.header.d*a.header.d*(a.n+1) := (CubeLengths.entryOrder _ _ ((x,y),j)).isLt
    exact (keep (a.header.header+13+a.header.entries+k) (by omega)).trans (rows x y j)
  · intro g
    rw [← owners]
    exact scheduled.owners g.val (g.isLt.trans_le groups.ge)

open private read_write from OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

private theorem canonicalRead {n d blocks b h K s cap : ℕ}
    (select : Packet n d blocks → Selector n K h) (decl : Broadcast n d cap)
    (size : cap = declarationCap n d blocks b h s)
    (spelling : (size ▸ decl : Broadcast n d (declarationCap n d blocks b h s)) = broadcast b s select) :
    readCode (n+1) decl.1 = (chosen b s select).val ∧
    (fun p j => readCode (cap+1) (decl.2 p j)) = subtotals itemRow (crossCount b s select) (chosen b s select) := by
  subst cap
  change decl = broadcast b s select at spelling
  subst decl
  simp only [broadcast,read_write,and_self]

/-- On the canonical passing broadcast, the words available at the end of scheduling
give the physical chosen coordinate and the complete array of true subtotals. -/
theorem Layout.ScannerWords.of_canonicalBroadcast (a : Layout) {frame team : ℕ}
    {owner : Fin a.header.d → ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (select : Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h)
    (decl : Broadcast a.n a.header.d a.header.cap)
    (size : a.header.cap = declarationCap a.n a.header.d a.header.blocks a.b a.h a.s)
    (spelling : (size ▸ decl : Broadcast a.n a.header.d
      (declarationCap a.n a.header.d a.header.blocks a.b a.h a.s)) = broadcast a.b a.s select)
    (words : a.ScannerWords frame team (readCode (a.n+1) decl.1) owner pub mem
      (fun p j => readCode (a.header.cap+1) (decl.2 p j))) :
    a.ScannerWords frame team (Physical.chosen a.b a.s select).val owner pub mem
      (subtotals itemRow (crossCount a.b a.s select) (Physical.chosen a.b a.s select)) := by
  obtain ⟨axis,rows⟩ := canonicalRead select decl size spelling
  rwa [axis,rows] at words

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
