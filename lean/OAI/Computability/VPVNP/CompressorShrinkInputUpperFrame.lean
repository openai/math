import OAI.Computability.VPVNP.CompressorGreedyPacketFootprints
import OAI.Computability.VPVNP.CompressorShrinkPreparationAccess
import OAI.Computability.VPVNP.CompressorShrinkBundleAccess

/-! # The upper frame of the pre-selection input scans

The complete greedy, placement, ranking and width scans access the old
incidence data and the freshly allocated input arena. Their stores preserve
every address at or above the arena's exclusive end.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput.Run

open BurstRAM Compression SourceTransport

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : ShrinkInput.Run X T start m)

/-- Bounds on all sixteen deterministic input segments before the absolute-ID
scatter. The old width and incidence columns can be anywhere below the arena. -/
theorem input_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (room : stop X start < 2^w) :
    LogAccess (fun x ↦ lo ≤ x ∧ x < stop X start) (fun x ↦ start ≤ x ∧ x < stop X start) r.reports := by
  let rd := fun x ↦ lo ≤ x ∧ x < stop X start
  let wr := fun x ↦ start ≤ x ∧ x < stop X start
  have endGreedy : GreedyArena.greedyStop start (Fintype.card X.Base) a ≤ stop X start := by
    obtain ⟨_,a,b,c⟩ := range_bounds X start
    exact a.trans (b.trans c)
  have g (s : GreedyVisit.Stage) : LogAccess rd wr (GreedyVisit.packetReports r.greedy s) :=
    (GreedyVisit.packet_access r.greedy lo low s).mono
      (fun _ h ↦ ⟨h.1,h.2.trans_le endGreedy⟩) (fun _ h ↦ ⟨h.1,h.2.trans_le endGreedy⟩)
  have greedy : LogAccess rd wr r.greedy.reports := (((((g .extract).append (g .zero)).append
    (g .colorPrepare)).append (g .colorRead)).append (g .tagPrepare)).append (g .tagRead)
  obtain ⟨sites,clear,cls,app,gather,rank⟩ := r.preparation_footprints lo low room
  obtain ⟨_,abs⟩ := ShrinkBundlePlan.run_absolute r ((range_bounds X start).2.2.2.trans_lt room)
  obtain ⟨scatter,thick,cd,pieces,_⟩ := ShrinkBundlePlan.Scheduled.width_footprints r abs lo (low 5) room
  have classified := ((greedy.append sites.2).append clear.2).append cls.2
  have ranked := ((classified.append app.2).append gather.2).append rank.2
  exact (((ranked.append scatter.2).append thick.2).append cd.2).append pieces.2


theorem post_upper (room : stop X start < 2^w) (addr : ℕ) (high : stop X start ≤ addr) : r.post addr = m addr := by
  rw [← r.post_reports]
  exact after_outside m (r.input_access 0 (fun _ ↦ Nat.zero_le _) room).2 (fun h ↦ high.not_gt h.2)

end CompressorRecords.ShrinkInput.Run

end VPVNP
end Computability
end OAI
