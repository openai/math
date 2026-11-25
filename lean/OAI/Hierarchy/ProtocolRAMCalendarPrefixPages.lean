import OAI.Hierarchy.ProtocolRAMCalendarPrefixWidths
import OAI.Hierarchy.ProtocolRAMCalendarPrefixDebits

namespace OAI
/-! # All chronological paid-width and catalyst-debit pages from the same native archive -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard CatalystArchive
open ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators

theorem native_text (W : ℕ) (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) :
    text (ReserveUse.native W a b count n reserve)=218 := by
  have scatter : text (ProtocolRAMWeightedScatter.program W a.scratch n)=22 := rfl
  rw [ReserveUse.native,text_seq,text_passes,scatter]
  rfl

theorem program_text {W count N : ℕ} (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks)
    (a : ReserveUse.Archive) (size : ℕ→Fin (N+1)) (reserve last : ℕ) :
    text (program L old a size reserve W last)=(last+1)*218 := by
  induction last with
  | zero => simpa only [program,Nat.one_mul] using native_text W a (banks L old 0) count (size 0).val reserve
  | succ j ih =>
    rw [program,text_seq,ih,native_text]
    exact (Nat.succ_mul (j+1) 218).symm

/-- Price the whole literal replay suffix, including its sparse row syntax and
every dated native counter, in the units required by the physical CPU bill. -/
theorem replay_bill {W edges count N : ℕ} (es : List Event) (compile : Event→List PaidWidths.Slice)
    (lw : PrefixWidths.Layout edges) (lr : PrefixWidths.Layout count) (a : ReserveUse.Archive)
    (old : RouteSettlement.Banks) (n : ℕ→Fin (N+1)) (reserve perTick perText : ℕ)
    (tick : ∀j≤es.length,∀ev∈es,
      ((compile ev).map (fun s=>RepairHistogram.ticks s.count (s.columns (lw.bank j) edges))).sum≤perTick)
    (rom : ∀j≤es.length,∀ev∈es,
      ((compile ev).map (fun s=>rowText (RepairHistogram.pair (s.columns (lw.bank j) edges))+22)).sum≤perText) :
    let T := es.length
    let rows := PrefixWidths.prefixRows es compile
    let body := (PrefixWidths.program lw rows W T).seq (program lr old a n reserve W T)
    CheapCode body ∧ text body≤(T+1)*(30+T*perText+218) ∧
      PrefixWidths.time lw rows T+cost count n T≤(T+1)*(8+6*edges+T*perTick+(19+12*count+160*N)) := by
  intro T rows body
  refine ⟨@cheap_seq W (PrefixWidths.program lw rows W T) (program lr old a n reserve W T)
      (@PrefixWidths.cheap edges W lw rows T) (@cheap W count N lr old a n reserve T),?_,?_⟩
  · change text ((PrefixWidths.program lw rows W T).seq (program lr old a n reserve W T))≤_
    rw [text_seq,program_text,Nat.mul_add]
    exact Nat.add_le_add_right (PrefixWidths.text_bound (W:=W) lw es compile perText rom) _
  · rw [Nat.mul_add]
    exact Nat.add_le_add (PrefixWidths.ticks_bound lw es compile perTick tick) (cost_le n T)

private theorem word_fits {W floor : ℕ} (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (ok : a.kind.Fits W floor ∧ a.pointer.Fits W floor ∧ a.history.Fits W floor) :
    (ReserveUse.word a b).Fits W floor := by
  simp [ReserveUse.word,Expr.Fits,ok]

/-- Append both genuine reporters to the same paid computation. The immutable directory
is read below the first width page. Every reserve page starts above all reported widths,
so both dated outputs and every original low archive word are present in the same out state. -/
theorem after_widths {W edges count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (compile : Event→List PaidWidths.Slice) (lw : PrefixWidths.Layout edges) (lr : PrefixWidths.Layout count)
    (old : RouteSettlement.Banks) (a : ReserveUse.Archive) (producer : Procedure W) (m archive : Memory W)
    (ticks : ℕ) (start : producer.Exec m archive ticks)
    (widths : PrefixWidths.Ready lw (PrefixWidths.prefixRows (events c) compile) archive (events c).length)
    (dir : Directory a (site c issued) (debit c issued) archive)
    (fixture : a.kind.Fits W lw.archive ∧ a.pointer.Fits W lw.archive ∧ a.history.Fits W lw.archive)
    (separated : (lw.bank (events c).length).base+edges≤lr.archive)
    (temporary : ∀j≤(events c).length,(lr.bank (2*j+1)).base+count≤a.scratch)
    (room : a.scratch+2*recordCount c issued<2^W) (wide : fuel c*payload<2^W) :
    let last := (events c).length
    let rows := PrefixWidths.prefixRows (events c) compile
    let size := countAt c issued
    let reserve := fuel c*payload
    let wout := PrefixWidths.image lw rows archive last
    let out := image lr old a size reserve (site c issued) (debit c issued) wout last
    ((producer.seq (PrefixWidths.program lw rows W last)).seq (program lr old a size reserve W last)).Exec m out
      ((ticks+PrefixWidths.time lw rows last)+cost count size last) ∧
    (∀x<lw.archive,out x=archive x) ∧
    (∀j≤last,∀e : Fin edges,(out ((lw.bank j).base+e.val)).val=PaidWidths.total (rows j) archive e) ∧
    ∀j≤last,∀v : Fin count,(out ((banks lr old j).used.base+v.val)).val=
      (∑ i : Fin (recordCount c issued),
        if ((rank c issued).symm i).1.val<j ∧ site c issued i=v then debit c issued i else 0) ∧
      (out ((banks lr old j).reserved.base+v.val)).val=reserve := by
  intro last rows size reserve wout out
  change (lw.bank last).base + edges ≤ lr.archive at separated
  have first := PrefixWidths.replay lw rows archive last widths
  have low : lw.archive≤lr.archive :=
    (lw.archive_le last).trans ((Nat.le_add_right _ _).trans separated)
  have frozen : Directory a (site c issued) (debit c issued) wout :=
    dir.preserved lw.archive first.kept ⟨fixture.1.2.2,fixture.2.1.2.2,fixture.2.2.2.2⟩
  have ready : Ready lr old a size reserve wout (site c issued) (debit c issued) last :=
    ⟨frozen,fun j _=>ProtocolRAMGeneratedWrite.fits_mono _ low (word_fits a (banks lr old j) fixture),
      temporary,room,wide,fun j _ v=>funded c issued j v⟩
  have second := replay lr old a size reserve wout (site c issued) (debit c issued) last ready
  refine ⟨Procedure.Exec.then (Procedure.Exec.then start first.ran) second.ran,fun x hx=>(second.kept x (hx.trans_le low)).trans (first.kept x hx),?_,?_⟩
  · intro j hj e
    have fits : (lw.bank j).base+e.val<lr.archive := by
      have bound := e.isLt
      rcases Nat.eq_or_lt_of_le hj with eq | lt
      · subst j
        omega
      · have early := lw.before lt
        omega
    exact (congrArg Fin.val (second.kept _ fits)).trans (first.read j hj e)
  · intro j hj v
    obtain ⟨usedAt,reserveAt⟩ := second.read j hj v
    exact ⟨usedAt.trans (chronological c issued j v),reserveAt⟩

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve

end
end OAI
