import OAI.Computability.BorderVNP.RoutingISACubeArenaPreservePadding
import OAI.Computability.BorderVNP.CubeScatterTransmissionRealization
import OAI.Computability.BorderVNP.PrivatePlacementImage
import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # Protected primary, secondary and powers words of the real padding invocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM Transmission Evaluator BorderVNP.Cube BorderVNP.Cube.Tally
open BorderVNP.Cube.Padding BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources

/-- Every literal header word below the substitution and live scratch arrays survives
pin preparation, the actual geometric reconstruction, private-slot placement and
the native publication of the raw delivery directory. -/
theorem epoch_word {w o : ℕ} (pins : Pins.Layout) (guess : ℕ → Bool) (before : Memory w)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s t : Bank w} {fresh dest clock : ℕ}
    {out : Fin o → ℕ} {es geom slotted}
    (geometry : PackedHistoryCircuit.GeometryReturn pub mac s (Pins.preparedMemory pins guess before pins.count)
      fresh dest clock out es t geom)
    (l : PrivatePlacement.Layout) (image : l.Image (readings geom) l.entries (readings slotted))
    (base : ℕ) (rows : List Packing.Directory.Row) {x : ℕ}
    (inputs : x < pins.ibase ∧ x < pins.hbase) (hg : x < fresh)
    (privateSlot : x < l.raw ∧ x < l.scratch) (raw : x < base) (cnt : x ≠ (pub 0).val+9) :
    Packing.Directory.ISA.publish slotted (pub 0).val base rows x = before x := by
  rw [Packing.Directory.ISA.publish,Function.update_of_ne cnt,
    Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl raw)]
  apply (Fin.ext (image.outside x (fun _ _ => by omega) (Or.inl privateSlot.2))).trans
  exact (geometry.preserved x hg).trans
    (Pins.preparedMemory_other pins guess before pins.count x (fun _ _ => by omega) (fun _ _ _ => by omega))

/-- The initial packet bank and all decoder writes end before the public group tables. -/
theorem Layout.packet_before_public (L : Layout) : L.header.packetBase ≤ L.publicBase := by
  dsimp only [Layout.publicBase,Layout.vertexBase,Layout.singleBank,Layout.packetEnd,CubeHeaderInstall.bankStop]
  omega

/-- A word in the installed power table is still its true power after both stages
of declaration preparation and the complete greedy and directory passes. -/
theorem Layout.power_after_group (L : Layout) (input : ℕ → ℕ) (bits broadcast : ℕ)
    {g : GroupWeights.Layout} {team : TeamNative.Layout} {c : CellBanks.Layout} {p : PairDirectory.Layout}
    {scheduled final : ℕ → ℕ}
    (weights : GroupWeights.ScheduleResult g team ((L.header.decoder broadcast).finalImage
      (L.header.image L.n bits (CubePowers.image L.header.d L.powerBase (L.n+1) input))) scheduled)
    (pairs : PairDirectory.Image p (c.written scheduled c.cells) p.count final)
    (fields : g.weights=L.groupWeights ∧ team.totals=L.teamTotals ∧ team.owners=L.ownerBase ∧
      c.dest=L.hostDirectory ∧ p.table=L.pairDirectory) (i : Fin (L.n+1)) :
    final (L.powerBase+i.val) = CubePowers.image L.header.d L.powerBase (L.n+1) input (L.powerBase+i.val) := by
  obtain ⟨_,_,_,_,_,_,power,group,_⟩ := L.group_order
  have high := L.packet_before_public.trans power
  unfold CubeHeaderInstall.Inputs.packetBase at high
  rw [scheduled_before L weights pairs fields (by have := i.isLt; omega),(L.header.decoder broadcast).finalOutside]
  · simp only [CubeHeaderInstall.Inputs.image,ite_eq_right (show ¬(L.header.header ≤ L.powerBase+i.val ∧
      L.powerBase+i.val < L.header.header+13) by omega)]
  · change L.powerBase+i.val ≠ L.header.header+5; omega
  · right; change L.header.header+13+L.header.entries+L.header.entries ≤ L.powerBase+i.val; omega
  · right; change L.header.header+13+2*L.header.entries+L.header.a ≤ L.powerBase+i.val; omega

/-- All consumed primary literals and selected secondary/power words survive the
row writers, complete routing, immutable table installation and the physical owned
traversal. The resulting `Published` can be passed directly to `Published.decode`. -/
theorem Layout.padding_published {w : ℕ} (L : Layout) (pub : Arg → Word w) (emit : DataWriter.Layout)
    {g : SharedRows.Layout} {m preRoute postRoute installed final : Memory w}
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) (readings preRoute))
    (primaryFrame : g.frame=(pub 0).val) (records : g.records=emit.output) (arena : emit.output=L.records)
    (routed : ∀ x < L.records, postRoute x=preRoute x)
    (f : DiagonalTallyPacketEmit.Frame) (id : TableEntry L.n L.b L.h L.K L.s → ℕ)
    (written : readings installed = CubeConstants.image (CubeConstants.inArena f L.stop L.n L.b L.h L.K L.s)
      (CubeConstants.idBase L.stop L.n L.b L.h L.K L.s) id (readings postRoute))
    (team : ℕ) (axis : Fin (L.n+1)) (selectors : ℕ)
    {A : Data L.n L.header.d L.header.blocks L.b L.h L.K L.s} {owner : Fin L.header.d → ℕ}
    (returned : FiniteEvaluator.CubeTriple.Readback (l := L.scanner (pub 0).val team axis.val selectors)
      A owner L.powerBase L.vertexBase L.publicBase installed final)
    (B : Bootstrap w)
    (header : B.stat L.header.d L.n L.header.blocks L.b L.h L.s = L.header)
    (pre : Published (arenaPointers L) B pub m team axis L.header.d L.header.blocks L.b L.h L.K L.s)
    (low : (pub 0).val+112 ≤ L.header.header) :
    Published (arenaPointers L) B pub final team axis L.header.d L.header.blocks L.b L.h L.K L.s := by
  let scanner := L.scanner (pub 0).val team axis.val selectors
  obtain ⟨_,_,_,_,_,_,pw,gw,gt,tot,od,ph,hr⟩ := L.group_order
  have headLo := L.packet_before_public
  unfold CubeHeaderInstall.Inputs.packetBase at headLo
  have keep (x : ℕ) (below : x < L.records) (ct : x ≠ (pub 0).val+13)
      (src : x ∈ source scanner L.powerBase L.n) (pubCt : x ≠ (pub 0).val+46) :
      final x = m x :=
    L.padding_word pub emit shared primaryFrame records arena routed f id written returned below ct (Or.inl ⟨src,pubCt⟩)
  have fixed (k : ℕ) (hk : k=0 ∨ k∈fixedFields) : final ((pub 0).val+k) = m ((pub 0).val+k) := by
    obtain ⟨src,ct46,ct13⟩ := primary_padding_read (scanner:=scanner) (power:=L.powerBase) (n:=L.n) hk
    have under : k < 112 := by rcases hk with rfl | h; decide; simp [fixedFields] at h; omega
    exact keep _ (by omega) ct13 src ct46
  have secondary (j : ℕ) (hj : j < 13) : final (L.header.header+j) = m (L.header.header+j) := by
    apply keep _ (by omega) (by omega) _ (by omega)
    exact Or.inr (Or.inl (Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))
  have power : final (L.powerBase+axis.val) = m (L.powerBase+axis.val) := by
    have ix := axis.isLt
    apply keep _ (by omega) (by omega) _ (by omega)
    exact Or.inr (Or.inl (Or.inr ⟨Nat.le_add_right ..,by change L.powerBase+axis.val < L.powerBase+L.n+1; omega⟩))
  constructor
  · have h : final ((pub 0).val) = m ((pub 0).val) := by simpa only [Nat.add_zero] using fixed 0 (Or.inl rfl)
    exact (congrArg Fin.val h).trans pre.core
  · intro j hj
    have h : final ((pub 0).val+31+j.val) = m ((pub 0).val+31+j.val) := by
      simpa only [Nat.add_assoc] using fixed (31+j.val) (Or.inr hj)
    exact h.trans (pre.extended j hj)
  · exact pre.literal
  · have h := secondary 5 (by decide)
    rw [← header] at h
    exact (congrArg Fin.val h).trans pre.axisWord
  · obtain ⟨dst,old,hs⟩ := pre.secondary
    refine ⟨dst,old,fun j hj => ?_⟩
    have read := hs j hj
    have keepH := secondary j (by simp at hj; omega)
    rw [← header] at keepH
    exact (congrArg Fin.val keepH).trans read
  · obtain ⟨input,h⟩ := pre.power
    exact ⟨input,(congrArg Fin.val power).trans h⟩

end RoutingISA.CubeArena

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing

/-- Each genuine complete native return preserves the original public prefix.
All safety and capacity premises come from the common prepared table. -/
theorem SharedRoutePrepared.before_records {R r t d link inner n w : ℕ} {Edge : Type}
    {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool} {ext : Exterior R r link → Bool}
    {L : WireLayout (R+1) r link} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {owner : ℕ → Fin (R+1)} {origin stride : ℕ} {tab : TableLayout} {row : ℕ → TableRow}
    {pub : Fin (R+1) → Arg → Word w} {before : Fin (R+1) → Memory w} {dst ib hb sb : Fin (R+1) → ℕ}
    {guess : Fin (R+1) → ℕ → Bool}
    (h : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (u : Fin (R+1)) {mac : TeamOpcode.Macros w 8} {s : Bank w}
    (z : Returns route (pub u) mac s (before u)) (a : ℕ) (ha : a < tab.records) :
    z.val.2.2 a = before u a :=
  CubeArena.route_before_records tab row (pub u) mac s (before u) h.allocated h.ordered h.rowFit
    (h.base u) (h.fields u) (h.records u) _ (h.frame u) (h.fit u) h.teams (h.capacity u) (h.written u).route z ha

end TeamContraction

end BorderVNP
end Computability
end OAI
