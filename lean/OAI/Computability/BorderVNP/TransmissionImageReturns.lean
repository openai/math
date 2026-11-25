import OAI.Computability.BorderVNP.TransmissionSenderWords
import OAI.Computability.BorderVNP.TransmissionImageDirectory

/-! # Physical transmission histories for the actual scheduler image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

/-- On the physical table constructed by the scheduler, returns of the complete
transmission program are in bijection with the locally guessed slot words whose
remote sends match the true source and link words. The scheduler image supplies
the directory reads and every endpoint address calculation. -/
theorem image_sender_equiv {w : ℕ} {l : TableLayout} {row : ℕ → TableRow}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m))
    (al : l.Allocated w) (rowsFit : l.RowsFit w row) (initial : l.recordsMatch row before)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (frame : f.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (directory : ∀ i < l.count,
      (tableRange l m i).directorySeparated (directoryFrame pub m 0) l)
    (sep : ∀ i < l.count,
      (tableRange l m i).scheduleSeparated (directoryFrame pub m 0) pub m f.teams)
    (sourceFit : ∀ i < l.count,
      (tableRange l m i).selected (directoryFrame pub m 0) = some (some .sendData) →
        (tableRange l m i).source.val+(tableRange l m i).width.val ≤ 2^w) :
    let team := directoryFrame pub m 0
    let rows := tableRange l m
    ∃ E : SenderWords rows pub m ≃ TableReturn pub macros s m, ∀ b,
      (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val ∧
      (E b).val.2.2 = tableMemory rows team pub m (decodeChoices rows team (List.ofFn b.val)) l.count ∧
      traceCost (E b).val.1 ≤ 256*(1+l.count+∑ i ∈ Finset.range l.count, (rows i).incident team) ∧
      ∀ e ∈ (E b).val.1, e.sign = .plus := by
  let rows := tableRange l m
  have count := image_count image al pub hf loaded
  have inside {i : ℕ} (hi : i < (directoryFrame pub m 13).val) : i < l.count := count ▸ hi
  have a := Schedule.of_table image al pub hf loaded f frame fit teams capacity
  have h := scheduled_sender_equiv rows pub macros m s a
    (fun _ hi => ScheduledRange.of_table image al rowsFit initial f teams (inside hi))
    (fun _ hi => tableRange_valid_kind image al rowsFit initial (inside hi))
    (fun i hi => sep i (inside hi)) (fun i hi => sourceFit i (inside hi))
    (image_directory image al pub hf loaded directory)
  simpa only [count] using h

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
