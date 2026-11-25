import OAI.Computability.BorderVNP.CubeISAOwnedPacketStage
import OAI.Computability.BorderVNP.CubeISAOwnedVertexRow

/-! # Writing the owned vertices from the actual packet-bank selector words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Cube.Physical.Owned Cube.Tally VPVNP.BurstRAM Owned OwnedVertex

/-- Initialize the mixed-radix iterator and emit the vertices on this side of the row. -/
def vertexStage (n b h K s : ℕ) : Code := .seq (OwnedRowSetup.packet n b h K s) (vertexRow n)

/-- Tick allowance for preparation, packet selection, and the actual three-word vertex records. -/
def vertexStageCost (n d blocks b h K s : ℕ) : ℕ :=
  (OwnedRowSetup.packet n b h K s).slots + ((∑ t : Fin (packetTrials n d blocks),
    (6*n+22 + if packetTrialValid t then 2+emitPacketCost n (selectorWidth n K h) else 1))+1)

/-- The vertex row has an unsigned trace and keeps both routed stream cursors. -/
theorem vertexRow_frame (n : ℕ) : (vertexRow n).unsigned = true ∧ (vertexRow n).keeps 36 = true ∧
    (vertexRow n).keeps 37 = true := by
  obtain ⟨u,c36,c37⟩ := packetCandidate_frame n
  change ((packetCandidate n).unsigned && true) = true ∧
    ((packetCandidate n).keeps 36 && true) = true ∧ ((packetCandidate n).keeps 37 && true) = true
  simpa only [Bool.and_true] using And.intro u (And.intro c36 c37)

/-- The complete vertex stage is deterministic. In particular the selector already in
addressed memory determines every directory word on any returning path. -/
theorem vertexStage_deterministic (n b h K s : ℕ) : (vertexStage n b h K s).deterministic = true := by
  change ((OwnedRowSetup.packet n b h K s).deterministic && ((packetCandidate n).deterministic && true)) = true
  simp [OwnedRowSetup.packet_deterministic,packetCandidate_deterministic]

/-- Installed selector bits produce the exact dense vertex directory. The row advances only
its output cursor among the outer control registers. Both routed stream cursors survive. -/
theorem vertexStage_run {w n b h K s : ℕ} (l : OwnedRowSetup.Layout)
    (D : PacketRowData n l.d l.blocks b h K s) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (out : ℕ) (entry : Entry D.axis D.pair.val.1 D.pair.val.2 r)
    (group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : PacketRoom l w n b h K s (pub 0).val)
    (base : D.base = l.bank) (stride : D.stride = bankWidth n b h K s) (output : readings r 7 = out)
    (bankRoom : D.base+(l.d*l.d)^(n+1)*2*l.blocks*D.stride ≤ out)
    (directoryRoom : out+(2*l.blocks*(l.d.choose 2)^n)*(3*2^n) < 2^w)
    (stored : ∀ p : Packet n l.d l.blocks, p.1.1 D.axis = D.pair →
      SelectorRead.Stored (readings m) (bankAt D.base D.stride p) (D.select p)) :
    TraceRun pub mac (vertexStage n b h K s) r m [] (vertexStageCost n l.d l.blocks b h K s) (fun t mt =>
      (∀ j, Control j → j ≠ 7 → t j = r j) ∧ t 36 = r 36 ∧ t 37 = r 37 ∧
      readings t 7 = out+(2*l.blocks*(l.d.choose 2)^n)*(3*2^n) ∧
      readings mt = (rowImage (blocks := l.blocks) D.axis D.pair D.high D.base D.stride
        (selectorWidth n K h) out (readings m) (packetTrials n l.d l.blocks)).2) := by
  have width : selectorWidth n K h ≤ w := Nat.clog_le_of_le_pow ((le_max_left ..).trans fit.keys.le)
  have within : selectorWidth n K h ≤ D.stride := by rw [stride]; unfold bankWidth supplyBase; omega
  have small : 3 < 2^w := by have h := fit.layout.primary; omega
  have valid (p : Packet n l.d l.blocks) (hp : p.1.1 D.axis = D.pair) :
      SelectorRead.Valid (readings m) (bankAt D.base D.stride p) (selectorWidth n K h) (Fintype.card (Selector n K h)) := by
    have word := stored p hp
    refine ⟨fun j hj => ?_,word.rank ▸ (selectorOrder n K h (D.select p)).isLt⟩
    rw [word ⟨j,hj⟩]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)
  change TraceRun pub mac (.seq _ _) r m ([] ++ []) (_ + _) _
  apply (preparePacketStage l D pub mac r m entry group loaded fit base stride).seq
  rintro u mu ⟨ready,owner,dim,bits,choices,keep,hm⟩
  subst mu
  have tested := vertexRow_run pub mac D.axis D.pair D.high D.base D.stride out (selectorWidth n K h)
    (Fintype.card (Selector n K h)) u m ready owner ((keep _ (by decide)).trans entry.axis) dim
    ((keep _ (by decide)).trans output) bits choices (stride ▸ fit.positive) width within bankRoom
    directoryRoom fit.trials ((le_max_right ..).trans fit.keys.le) small
  obtain ⟨unsigned,c36,c37⟩ := vertexRow_frame n
  obtain ⟨es,t,mt,run,ok,cost,image,cursor,_,low⟩ := traceRun_unsigned (tested.complete valid) unsigned
  refine ⟨es,t,mt,run,ok,cost,?_,(run.keepsReg c36).trans (Fin.ext (keep _ (by decide))),
    (run.keepsReg c37).trans (Fin.ext (keep _ (by decide))),cursor,image⟩
  intro j hj h7
  have bounds := (by decide : ∀ j : Reg, Control j → j.val < 24 ∧ j ≠ 18 ∧ OwnedRowSetup.Held j) j hj
  exact Fin.ext ((low j bounds.1 h7 bounds.2.1).trans (keep j bounds.2.2))

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
