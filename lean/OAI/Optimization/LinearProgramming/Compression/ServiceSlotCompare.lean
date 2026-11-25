import OAI.Optimization.LinearProgramming.Compression.ServiceSlotScan

/-! Finite RAM code for the exact order used by generator lookup and insertion. Two slots
are compared in linear time, with unchanged scalar storage outside registers 0, 5, and 6. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

def headStep : Block := .seq (slotMoves headMoves) compareHeaders

theorem headStep_spec (P : ℚ → Prop) (s m : Memory ℚ) (r c a b : ℕ)
    (hy : 7≤ s.index 20) (hq : 7≤ s.index 21) (ha : s.data (s.index 20+r)=(a:ℚ))
    (hb : s.data (s.index 21+r)=(b:ℚ)) (hs : SlotSafe P m) (fm : SlotFrame s m)
    (cm : SlotCursor s m (r+1) c) :
    ∃ t k, k≤8 ∧ Block.Eval (SlotSafe P) headStep m k t ∧ SlotFrame s t ∧ SlotCursor s t r c ∧
      t.index 23=prependCode a b (m.index 23) := by
  let z := afterMoves m headMoves
  have ez := slotMoves_eval P m headMoves hs
  have fz : SlotFrame s z := fm.trans (afterMoves_frame m headMoves (by simp [headMoves,SlotMove.dst]))
  have cz : SlotCursor s z r c := by simpa using cm.head (Nat.succ_pos _)
  obtain ⟨t,k,hk,e,g⟩ := compareHeaders_spec P z a b
    (by rw [cz.leftRow,fz.high (by omega),ha]) (by rw [cz.rightRow,fz.high (by omega),hb])
    (by rw [cz.rightRow]; omega) ez.safe_end
  have h23 : z.index 23=m.index 23 := afterMoves_index m headMoves 23 (by simp [headMoves,SlotMove.dst])
  exact ⟨t,2+k,by omega,ez.seq e,fz.trans g.frame,cz.of_preserved (fun i hi hj => g.index _ (by omega)),
    by simpa only [h23] using g.result⟩

/-- The comparison output occupies address register 23. The original slot bases and
ambient dimension occupy registers 20, 21, and 22 throughout. -/
def slotCompare : Block := .seq warmSlots (.seq pairSweep (.seq headStep headStep))

/-- This concrete fixed program implements the comparison used by the sorted table,
with a single dimension-linear bound on actual executed instructions. -/
theorem slotCompare_spec : SlotComparatorSpec slotCompare (fun n => 100*(n+1)) := by
  intro d e n D E y q P s hd hn hy hq by₀ bq₀ hs hp
  obtain ⟨m,k₀,hk₀,e₀,fm,cm,hm⟩ := warmSlots_spec P s n hn hs
  obtain ⟨w,k₁,hk₁,e₁,fw,cw,hw⟩ := pairSweep_spec y q P s m hd hn hy hq by₀ bq₀ e₀.safe_end hp fm cm hm
  obtain ⟨z,k₂,hk₂,e₂,fz,cz,hz⟩ := headStep_spec P s w 1 (2+n) (order y.val) (order q.val)
    by₀ bq₀ hy.order hq.order e₁.safe_end fw cw
  obtain ⟨t,k₃,hk₃,e₃,ft,ct,ht⟩ := headStep_spec P s z 0 (2+n) (tag y.val) (tag q.val)
    by₀ bq₀ (by simpa using hy.tag) (by simpa using hq.tag) e₂.safe_end fz cz
  exact ⟨t,k₀+(k₁+(k₂+k₃)),by change _ ≤ 100*(n+1); omega,e₀.seq (e₁.seq (e₂.seq e₃)),
    by rw [ht,hz]; exact finishCode y q _ hw,ft.index,ft.data⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
