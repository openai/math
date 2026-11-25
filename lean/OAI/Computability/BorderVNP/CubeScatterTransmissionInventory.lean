import OAI.Computability.BorderVNP.CubeScatterArenaDelivered
import OAI.Computability.BorderVNP.TransmissionPlacedBanks

/-! # Static scanner inputs survive the actual shared writer, scheduler, and transmission

The immutable frame, declaration, powers and owner words lie before the
transmission records. The public scheduler writes beyond the records, and
the actual delivery histories preserve every low address up to the read extent.
The shared emitter changes one low word, publishing the count at frame 13.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.TeamRowSources

/-- Every static word of the row scanner outside the directed pair buffers precedes
the public routing records. This includes all claims, header fields, owner words and powers. -/
theorem Layout.scanner_before_pair_directory (ar : Layout) (frame team axis selectors : ℕ)
    (frameLow : frame+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1)
    {j : ℕ} (hj : j ∈ source (ar.scanner frame team axis selectors) ar.powerBase ar.n)
    (staticWord : j ∉ Set.Ico ar.pairBase (ar.pairBase+ar.pairStride*(ar.header.d*ar.header.d))) :
    j < ar.pairDirectory := by
  have decl : ar.header.header+13+2*(ar.header.d*ar.header.d*(ar.n+1))+(ar.n+1) = ar.header.packetBase := by
    simp [CubeHeaderInstall.Inputs.packetBase,CubeHeaderInstall.Inputs.entries,axes]
  have high : ar.header.packetBase ≤ ar.packetEnd := Nat.le_add_right _ _
  have vert : ar.vertexBase ≤ ar.publicBase := Nat.le_add_right _ _
  obtain ⟨scratch,single,_,_,_,_⟩ := ar.separated
  obtain ⟨powers,owners,_⟩ := ar.source_order
  have recordsHigh : ar.ownerBase+ar.header.d = ar.pairDirectory := rfl
  simp only [source,scanner,Set.mem_union,Set.mem_Ico] at hj
  rcases hj with ((claim|owner)|(((prim|head)|power)|view))
  all_goals first | exact False.elim (staticWord view) | rcases ‹_ ∧ _› with ⟨lo,hi⟩; omega

/-- In particular all static scanner words precede the seven-word routing table. -/
theorem Layout.scanner_before_records (ar : Layout) (frame team axis selectors : ℕ)
    (frameLow : frame+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1)
    {j : ℕ} (hj : j ∈ source (ar.scanner frame team axis selectors) ar.powerBase ar.n)
    (staticWord : j ∉ Set.Ico ar.pairBase (ar.pairBase+ar.pairStride*(ar.header.d*ar.header.d))) :
    j < ar.records := (ar.scanner_before_pair_directory frame team axis selectors frameLow axes hj staticWord).trans_le
      ((show ar.pairDirectory ≤ ar.hostDirectory from Nat.le_add_right ..).trans (Nat.le_add_right ..))

end RoutingISA.CubeArena

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
  {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}

/-- The shared writer's poststate is preserved at each address below the routing
records all the way through the real per-team return. The region includes the
published row count and every immutable scanner input other than the delivered views. -/
theorem ReturnedDelivery.returned_before_records (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins)
    (ar : CubeArena.Layout) (frame count : ℕ) (table : f.table = ar.table frame count)
    (u : Fin (R+1)) (x : ℕ) (low : x < ar.records) :
    readings (H u).history.val.2.2 x = f.before u x := by
  have before (a : TableArray) (kind : a = .widths ∨ a = .ordinals ∨ a = .offsets ∨ a = .used) :
      x < f.table.base a := by
    rcases kind with rfl | rfl | rfl | rfl <;> rw [table] <;>
      simp only [CubeArena.Layout.table,TableLayout.reserve,TableLayout.base] <;> omega
  have outside (a : TableArray) (kind : a = .widths ∨ a = .ordinals ∨ a = .offsets ∨ a = .used) :
      ¬ f.table.contains a x := fun inside => (Nat.not_le_of_gt (before a kind)) inside.1
  have init := (f.image u).outside x (outside _ (Or.inl rfl)) (outside _ (Or.inr (Or.inl rfl)))
    (outside _ (Or.inr (Or.inr (Or.inl rfl)))) (outside _ (Or.inr (Or.inr (Or.inr rfl))))
  have xo : x < f.table.ordinals := before .ordinals (Or.inr (Or.inl rfl))
  have extent : x < f.table.readExtent (pins u) :=
    xo.trans_le ((Nat.le_add_right _ _).trans (f.table.readExtent_bounds _).1)
  have kept := (f.placed u).before_low (i := (H u).count) le_rfl extent
  rw [(H u).output]
  exact (congrArg Fin.val kept).trans init

/-- Every low field except the emitter's count is preserved from immediately
before the shared writer to the actual returned team memory. -/
theorem SharedWriters.returned_static (writer : SharedWriters f g src)
    (ar : CubeArena.Layout) (frame count : ℕ) (table : f.table = ar.table frame count)
    (u : Fin (R+1)) (x : ℕ) (low : x < ar.records) (other : x ≠ g.frame+13) :
    readings (H u).history.val.2.2 x = src u x := by
  have records : g.records = ar.records := writer.records.symm.trans (congrArg TableLayout.records table)
  have below : x < g.address g.dataCount := by unfold SharedRows.Layout.address; rw [records]; omega
  exact (f.returned_before_records ar frame count table u x low).trans
    ((writer.emitted u).outside x other (Or.inl below))

/-- The low field changed by the shared emitter contains its actual full row count
at the end of transmission. -/
theorem SharedWriters.returned_count (writer : SharedWriters f g src)
    (ar : CubeArena.Layout) (frame count : ℕ) (table : f.table = ar.table frame count)
    (u : Fin (R+1)) (low : g.frame+13 < ar.records) :
    readings (H u).history.val.2.2 (g.frame+13) = g.dataCount+g.groups.choose 2 :=
  (f.returned_before_records ar frame count table u _ low).trans (writer.emitted u).count

/-- The complete value of every immutable scanner input at transmission return:
the count is the actual emitted count, and every other static operand is exactly
the shared writer's input word. -/
theorem SharedWriters.returned_scanner_static (writer : SharedWriters f g src)
    (ar : CubeArena.Layout) (count team axis selectors : ℕ) (table : f.table = ar.table g.frame count)
    (u : Fin (R+1)) (frameLow : g.frame+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1)
    {j : ℕ} (hj : j ∈ TeamRowSources.source (ar.scanner g.frame team axis selectors) ar.powerBase ar.n)
    (staticWord : j ∉ Set.Ico ar.pairBase (ar.pairBase+ar.pairStride*(ar.header.d*ar.header.d))) :
    readings (H u).history.val.2.2 j = if j = g.frame+13 then g.dataCount+g.groups.choose 2 else src u j := by
  have before := ar.scanner_before_records _ team axis selectors frameLow axes hj staticWord
  by_cases eq : j = g.frame+13
  · subst j
    exact (writer.returned_count ar _ _ table u before).trans (ite_eq_left rfl).symm
  · rw [ite_eq_right eq]
    exact writer.returned_static ar _ _ table u _ before eq

end TeamContraction

end BorderVNP
end Computability
end OAI
