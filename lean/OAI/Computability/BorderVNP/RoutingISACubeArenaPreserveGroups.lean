import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserve
import OAI.Computability.BorderVNP.CubeScatterPaddingMetadata
import OAI.Computability.BorderVNP.LabelIndexChooserSpace
import OAI.Computability.BorderVNP.CubeLabelPassFit
import OAI.Computability.BorderVNP.CubeGroupWeightCheckedSchedule

/-! # Public words surviving the complete native grouping schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube

/-- All public group tables start after the secondary header, packet and vertex banks. -/
theorem Layout.group_order (a : Layout) :
    a.header.header ≤ a.publicBase ∧ a.publicBase ≤ a.heads ∧ a.publicBase ≤ a.cableMean ∧
    a.publicBase ≤ a.dataMean ∧ a.publicBase ≤ a.widthBase ∧ a.publicBase ≤ a.ordinalBase ∧
    a.publicBase ≤ a.powerBase ∧ a.powerBase+(a.n+1) ≤ a.groupWeights ∧
    a.groupWeights ≤ a.teamTotals ∧ a.teamTotals ≤ a.ownerBase ∧
    a.ownerBase ≤ a.pairDirectory ∧ a.pairDirectory ≤ a.hostDirectory ∧ a.hostDirectory ≤ a.records := by
  dsimp only [Layout.publicBase,Layout.vertexBase,Layout.singleBank,Layout.packetEnd,
    CubeHeaderInstall.bankStop,CubeHeaderInstall.Inputs.packetBase,Layout.heads,Layout.nodes,Layout.demands,
    Layout.cableMean,Layout.dataMean,Layout.widthBase,Layout.ordinalBase,Layout.powerBase,Layout.groupWeights,
    Layout.teamTotals,Layout.ownerBase,Layout.pairDirectory,Layout.hostDirectory,Layout.records]
  omega

/-- Label initialization and every assignment preserve the whole region below
the label output, including both the raw demand directory and pin array. -/
theorem label_before (L : Layout) (l : LabelIndex.Layout) (p : LabelTrial.Frame)
    (before : ℕ → ℕ) (z c : ℕ) (rows : ℕ → List LabelTrial.Incident)
    (alloc : LabelIndex.Allocated l) (endpoints : LabelIndex.Endpoints l before)
    (heads : l.heads=L.heads) (labels : p.labels=L.publicBase) (bins : p.cables=L.cableMean ∧ p.data=L.dataMean)
    {x : ℕ} (hx : x < L.publicBase) :
    p.prefix z rows (LabelIndex.image l before).mem c x = before x := by
  obtain ⟨_,hh,hc,hd,_⟩ := L.group_order
  rw [p.prefix_off z rows _ c x]
  · exact (LabelIndex.image_view l before alloc endpoints).input x (heads ▸ hx.trans_le hh)
  · intro i _ eq
    unfold LabelTrial.Frame.cacheAddr at eq
    split at eq <;> omega
  · intro j _; rw [labels]; omega

/-- The directed-interval pass, positional powers, static declaration, dynamic
declaration and read-only minimum check all preserve the old low input. -/
theorem declaration_before (L : Layout) {l : NativeIntervals.Layout} {old directed : ℕ → ℕ}
    (image : l.Image old l.count directed) (wi : l.widths=L.widthBase) (oi : l.ordinals=L.ordinalBase)
    (bits broadcast : ℕ) {x : ℕ} (hx : x < L.header.header) :
    (L.header.decoder broadcast).finalImage (L.header.image L.n bits
      (CubePowers.image L.header.d L.powerBase (L.n+1) directed)) x = old x := by
  obtain ⟨low,_,_,_,hw,ho,hp,_⟩ := L.group_order
  rw [(L.header.decoder broadcast).finalOutside]
  · simp only [CubeHeaderInstall.Inputs.image,ite_eq_right (show ¬(L.header.header ≤ x ∧ x < L.header.header+13) by omega),
      CubePowers.image,ite_eq_right (show ¬(L.powerBase ≤ x ∧ x - L.powerBase < L.n+1) by omega)]
    apply image.outside <;> omega
  · change x ≠ L.header.header+5; omega
  · left; change x < L.header.header+13+L.header.entries; omega
  · left; change x < L.header.header+13+2*L.header.entries; omega

/-- Greedy scheduling, the two-word cell-bank installer and the pair-directory
traversal retain all earlier arrays, including the complete power table. -/
theorem scheduled_before (L : Layout) {g : GroupWeights.Layout} {team : TeamNative.Layout}
    {c : CellBanks.Layout} {p : PairDirectory.Layout} {old scheduled table : ℕ → ℕ}
    (weights : GroupWeights.ScheduleResult g team old scheduled)
    (pairs : PairDirectory.Image p (c.written scheduled c.cells) p.count table)
    (fields : g.weights=L.groupWeights ∧ team.totals=L.teamTotals ∧ team.owners=L.ownerBase ∧
      c.dest=L.hostDirectory ∧ p.table=L.pairDirectory) {x : ℕ} (hx : x < L.groupWeights) :
    table x = old x := by
  obtain ⟨_,_,_,_,_,_,_,_,tot,own,pair,cell,_⟩ := L.group_order
  obtain ⟨ws,ts,os,cs,ps⟩ := fields
  rw [pairs.outside x (.inl (by omega)),c.written_outside scheduled c.cells x (.inl (by omega))]
  exact weights.other x (fun _ _ => by omega) (fun _ => by omega) (fun _ _ => by omega)

/-- A word below the secondary header survives every native stage from
entry of the label chooser through the published pair directory, immediately
before the transmission data writer. -/
theorem before_data (L : Layout) (lab : LabelIndex.Layout) (choice : LabelTrial.Frame)
    (orig : ℕ → ℕ) (z : ℕ) (rows : ℕ → List LabelTrial.Incident)
    (alloc : LabelIndex.Allocated lab) (endpoints : LabelIndex.Endpoints lab orig)
    (heads : lab.heads=L.heads) (labels : choice.labels=L.publicBase)
    (bins : choice.cables=L.cableMean ∧ choice.data=L.dataMean)
    {interval : NativeIntervals.Layout} {directed : ℕ → ℕ}
    (image : interval.Image (choice.prefix z rows (LabelIndex.image lab orig).mem lab.cells) interval.count directed)
    (wi : interval.widths=L.widthBase) (oi : interval.ordinals=L.ordinalBase) (bits broadcast : ℕ)
    {g : GroupWeights.Layout} {team : TeamNative.Layout} {c : CellBanks.Layout} {p : PairDirectory.Layout}
    {scheduled table : ℕ → ℕ}
    (weights : GroupWeights.ScheduleResult g team ((L.header.decoder broadcast).finalImage
      (L.header.image L.n bits (CubePowers.image L.header.d L.powerBase (L.n+1) directed))) scheduled)
    (pairs : PairDirectory.Image p (c.written scheduled c.cells) p.count table)
    (fields : g.weights=L.groupWeights ∧ team.totals=L.teamTotals ∧ team.owners=L.ownerBase ∧
      c.dest=L.hostDirectory ∧ p.table=L.pairDirectory) {x : ℕ} (hx : x < L.header.header) :
    table x = orig x := by
  obtain ⟨low,_,_,_,_,_,power,group,_⟩ := L.group_order
  rw [scheduled_before L weights pairs fields (by omega),declaration_before L image wi oi bits broadcast hx]
  exact label_before L lab choice orig z lab.cells rows alloc endpoints heads labels bins (hx.trans_le low)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
