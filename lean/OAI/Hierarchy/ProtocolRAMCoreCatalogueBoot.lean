import OAI.Hierarchy.ProtocolRAMCoreCatalogueBudget
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceROM

namespace OAI
/-! # The numbered catalogue and complete market calendar share one subdivision -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {h W k jobs tables N phases attempts R K H : ℕ} {S : PurchaseSampler}

theorem boot_geometry {h d k jobs : ℕ} (v : Fin jobs→Market h d k) {size : ℕ} (layout : Boot.Layout v size)
    (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (words : Boot.Tape h d)
    (auth : ∀i : Fin (2^h), words i.val=((π i).val:Word _)) : Geometry π (Boot.booted v size words) d := fun t =>
  PurchaseCT.resident_numbered π t 0 0 0 0 _ (Boot.subdivision v layout hd π words auth).2

def masterWords (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (joint : JointHeader.Board)
    (ports : PortROM.Table tables) (N : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^h))) (stock : ℕ→ℕ) (rest : Boot.Tape h (2^W)) :=
  JointHeader.words joint h (2^W) N k phase π stock (ports.words (initial order M groups dir rest))

theorem master_retains (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (joint : JointHeader.Board)
    (ports : PortROM.Table tables) (N : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^h))) (stock : ℕ→ℕ) (rest : Boot.Tape h (2^W)) (i : ℕ)
    (start : 2^h≤ i) (before : i< joint.initial) (early : i< ports.base) :
    masterWords order M groups dir joint ports N phase π stock rest i=initial order M groups dir rest i := by
  let raw := initial order M groups dir rest
  have lo : i< joint.initial+GlobalTests.rows h N k := by omega
  change JointHeader.words joint h (2^W) N k phase π stock (ports.words raw) i=_
  rw [JointHeader.below_scores joint phase π stock (ports.words raw) i (lo.trans_le (JointHeader.order ..))]
  rw [JointHeader.lowData,FeedROM.before_stock _ _ _ _ _ _ _ lo]
  simp only [JointHeader.inventory,fillSegment,not_le.mpr before,false_and,ite_false,
    Boot.permutationWords,dite_eq_right (Nat.not_lt.mpr start)]
  exact ports.frame raw i (.inl early)

/-- The exact memory reached by the one boot CPU is simultaneously the
calendar's market receipt and the source of every numbered core row. -/
theorem master_boot (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (joint : JointHeader.Board)
    (ports : PortROM.Table tables) (N : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^h))) (stock : ℕ→ℕ) (rest : Boot.Tape h (2^W))
    (v : Fin jobs→Market h (2^W) k) {size : ℕ} (layout : Boot.Layout v size)
    (space : let endAt := top h W K dir.groups H R
      endAt≤ joint.initial ∧ endAt≤ ports.base ∧ endAt≤ size ∧ endAt<2^Native.wordBits h (2^W) Native.copies ∧
      ∀j,endAt≤ Boot.low (v j)) :
    let words := masterWords order M groups dir joint ports N phase π stock rest
    let mid := Boot.booted v size words
    let c := sourceAt h W k attempts R K dir.groups H (pointBits h W)
    (Native.subdivisionProgram h (2^W)).Exec (Boot.initial v size words) mid (Native.subdivisionConstant (2^W)*2^h) ∧
      Boot.Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧ Rows c order dir π M mid := by
  obtain ⟨jointLo,portLo,storage,wordRoom,marketLo⟩ := space
  let words := masterWords order M groups dir joint ports N phase π stock rest
  have topHdr : headBase h W K dir.groups H+headerWords R≤ top h W K dir.groups H R :=
    (le_max_left ..).trans (le_max_right ..)
  have cap : groupStart h W≤ headBase h W K dir.groups H+headerWords R := by
    unfold headBase SiteROM.endAddress superStart
    omega
  have piLow : 2^h≤ joint.initial := (le_max_right ..).trans (cap.trans (topHdr.trans jointLo))
  have auth := JointHeader.authentic (N:=N) (k:=k) joint phase π stock (ports.words (initial order M groups dir rest)) piLow
  obtain ⟨ran,receipt⟩ := Boot.start v layout (Nat.two_pow_pos _) π words auth
  refine ⟨ran,receipt,rows_of_retained order (pointBits h W) M groups dir π rest _ (boot_geometry v layout
    (Nat.two_pow_pos _) π words auth) ?_ (rooms_of_top (by rw [total_stages];omega) wordRoom)⟩
  intro a lo hi
  have upper := hi.trans_le topHdr
  have read := receipt.kept a ((le_max_left ..).trans lo) (fun j hit=>Nat.not_lt_of_ge hit.1 (upper.trans_le (marketLo j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (upper.trans_le storage)] at read
  exact read.trans (master_retains order M groups dir joint ports N phase π stock rest a
    ((le_max_right ..).trans lo) (upper.trans_le jointLo) (upper.trans_le portLo))

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
