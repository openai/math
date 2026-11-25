import OAI.Hierarchy.ProtocolRAMCalendarPrefixPages

namespace OAI
/-! # Dated reserve replay at the physical owners of the original debit archive -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators

theorem used_positive {N count : ℕ} (physical economic : Fin N→Fin count) (amount : Fin N→ℕ)
    (stop : Fin (N+1)) (v : Fin count) (active : ∀i,0<amount i→physical i=economic i) :
    used physical amount stop v=used economic amount stop v := by
  unfold used
  apply Finset.sum_congr rfl
  intro i _
  let idx:=Fin.castLE (Nat.le_of_lt_succ stop.isLt) i
  change (if physical idx=v then amount idx else 0)=(if economic idx=v then amount idx else 0)
  by_cases hit : 0<amount idx
  · rw [active _ hit]
  · simp [Nat.eq_zero_of_not_pos hit]

private theorem archive_word_fits {W floor : ℕ} (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (ok : a.kind.Fits W floor ∧ a.pointer.Fits W floor ∧ a.history.Fits W floor) :
    (ReserveUse.word a b).Fits W floor := by
  simp [ReserveUse.word,Expr.Fits,ok]

/-- The actual stored owner may be a valid dummy at a zero debit. Every
native prefix nonetheless gives the exact economic debit for each resource. -/
theorem after_widths_native {W edges count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (compile : Event→List PaidWidths.Slice) (lw : PrefixWidths.Layout edges) (lr : PrefixWidths.Layout count)
    (old : RouteSettlement.Banks) (a : ReserveUse.Archive) (producer : Procedure W) (m archive : Memory W)
    (ticks : ℕ) (start : producer.Exec m archive ticks)
    (widths : PrefixWidths.Ready lw (PrefixWidths.prefixRows (events c) compile) archive (events c).length)
    (nativeOwner : Fin (recordCount c issued)→Fin count)
    (active : ∀i,0<debit c issued i→nativeOwner i=site c issued i)
    (dir : Directory a nativeOwner (debit c issued) archive)
    (fixture : a.kind.Fits W lw.archive ∧ a.pointer.Fits W lw.archive ∧ a.history.Fits W lw.archive)
    (separated : (lw.bank (events c).length).base+edges≤lr.archive)
    (temporary : ∀j≤(events c).length,(lr.bank (2*j+1)).base+count≤a.scratch)
    (room : a.scratch+2*recordCount c issued<2^W) (wide : fuel c*payload<2^W) :
    let last := (events c).length
    let rows := PrefixWidths.prefixRows (events c) compile
    let size := countAt c issued
    let reserve := fuel c*payload
    let wout := PrefixWidths.image lw rows archive last
    let out := image lr old a size reserve nativeOwner (debit c issued) wout last
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
  have frozen : Directory a nativeOwner (debit c issued) wout :=
    dir.preserved lw.archive first.kept ⟨fixture.1.2.2,fixture.2.1.2.2,fixture.2.2.2.2⟩
  have ready : Ready lr old a size reserve wout nativeOwner (debit c issued) last :=
    ⟨frozen,fun j _=>ProtocolRAMGeneratedWrite.fits_mono _ low (archive_word_fits a (banks lr old j) fixture),
      temporary,room,wide,fun j _ v=>(used_positive _ _ _ (size j) v active).le.trans (funded c issued j v)⟩
  have second := replay lr old a size reserve wout nativeOwner (debit c issued) last ready
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
    exact ⟨usedAt.trans ((used_positive _ _ _ (size j) v active).trans (chronological c issued j v)),reserveAt⟩

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve
end

end OAI
