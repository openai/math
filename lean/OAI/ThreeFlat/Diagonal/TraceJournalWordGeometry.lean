import OAI.Hierarchy.TraceSeedVisit
import OAI.ThreeFlat.Diagonal.TraceIterationJournal

namespace OAI
/-! # Actual 64w-bit placement of the word-visit arrays -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalStage NavigationDirectory Hierarchy

/-- The last stage header ends before the native dense array. The additional
terminal directory record gives one whole row of separation. -/
theorem header_dense {W limit cap edges : ℕ} {a : Archive} {cur : Word W} {ss : List Stage}
    (limits : a.TraceLimits limit cur ss edges cap) : (finish a.K ss a.cursor).header≤a.cursor.dense := by
  have h := limits.tables
  rw [Archive.directory_length] at h
  rw [header_finish,limits.origin]
  omega

/-- The current receiver's β=16·2^(32w) base lies above the historical lower
bound on the word program. The retained-lane capacity is smaller as well. -/
theorem seed_room {F : Type} [Field F] (B : Block F) {w : ℕ} (pos : 0<w)
    (axes off slots cap rawStatic : ℕ) :
    2^w ≤ 2^((64*w)/16) ∧ 21*(2^((64*w)/16))^4 ≤
        (TraceSeedWriter.archive B w axes off slots cap rawStatic).cursor.header := by
  have scale : 64*w/16 = 4*w := by omega
  rw [scale]
  refine ⟨Nat.pow_le_pow_right (by decide) (by omega),?_⟩
  change 21*(2^(4*w))^4 ≤ 16*2^(32*w)+64
  rw [←pow_mul, show 4*w*4=16*w by ring, show 32*w=16*w+16*w by omega,pow_add]
  have h : 2 ≤ 2^(16*w) := Nat.one_lt_two_pow (by omega)
  nlinarith [Nat.mul_le_mul_left (2^(16*w)) h]

/-- The literal five-word seed kernels lie between the finished selector headers
and the initial stage heap, so every word is retained from actual seed startup. -/
theorem seed_records {F : Type} [Field F] {W s limit : ℕ} {cur ctr : Word W} (a : Archive)
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) (raw : List Bool)
    {origin mid : Memory W} (journal : a.TraceJournal limit cur ctr P rem X a.cursor raw origin mid)
    (head : (finish a.K (P.directory rem (Fintype.card X.Base)) a.cursor).header≤a.initialRecords)
    (heap : a.metadataEnd≤a.cursor.heap) (control : a.cursor.heap≤cur.val) (next : cur.val<ctr.val) :
    ∀ i, a.initialRecords≤ i → i<a.metadataEnd → mid i=origin i := by
  intro i lo hi
  exact Archive.TraceJournal.frame P rem X a.cursor raw journal (by omega) (by omega)
    ⟨Or.inr (head.trans lo),Or.inl (hi.trans_le heap)⟩


end ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery

end OAI
