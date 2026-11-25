import OAI.Computability.BorderVNP.RoutingISAScheduledLength
import OAI.Computability.BorderVNP.RoutingISARelayProof
import OAI.Computability.BorderVNP.RoutingISAOffsetControl
import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # The triangular enumeration of the physical relay program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM Finset

/-- Registers and memory retained between adjacent endpoint pairs. -/
def RelayState (l : TableLayout) (mem : ℕ → ℕ) (relay u : ℕ) (z : NatState) : Prop :=
  l.ready z ∧ z.mem = mem ∧ z.reg 21 = u ∧ z.reg 22 = relay

/-- The positive natural length used for each local quotient loop is computed
by the fixed scheduler code on the caller's own public width table. -/
def RelayLengthRuns {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (l : TableLayout)
    (mem : ℕ → ℕ) (relay : ℕ) (len : ℕ → ℕ → ℕ) : Prop :=
  ∀ u < l.teams, ∀ y < l.teams, ∀ s m, RelayState l mem relay u (.ofWords s m) → readings s 23 = y →
    BoundedRun pub macros scheduledLengthWord s m scheduledLengthWord.slots
      (fun z => RelayState l mem relay u z ∧ z.reg 23 = y ∧ z.reg 28 = len u y)

/-- Cost of one iteration at a pair of endpoints. -/
def relayPairCost (n : ℕ) : ℕ := scheduledLengthWord.slots + (n * (relayBody.slots+1) + 2) + 1

/-- Cost of processing all upper-triangular pairs with the same first endpoint. -/
def relayRowCost (R : ℕ) (len : ℕ → ℕ → ℕ) (u : ℕ) : ℕ :=
  1 + ((∑ y ∈ Ico (u+1) R, (relayPairCost (len u y) + 1)) + 1) + 1

/-- Physical trace allowance including setup, both endpoint counters, all loop
guards and the actual quotient comparisons. -/
def relayCheckCost (R : ℕ) (len : ℕ → ℕ → ℕ) : ℕ :=
  tableSetup.slots + 4 + 1 + ((∑ u ∈ Ico 0 R, (relayRowCost R len u + 1)) + 1)

/-- Occupied physical leg words of every unordered pair agree at this relay. -/
def RelayChecks (R : ℕ) (len : ℕ → ℕ → ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ u < R, ∀ y, u < y → y < R → ∀ q < len u y, RelayWordAgrees pub mem u v y q

/-- Space for the two addresses actually accessed at each occupied quotient. -/
def RelayRooms (w R : ℕ) (len : ℕ → ℕ → ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ u < R, ∀ y, u < y → y < R → ∀ q < len u y,
    LegRoom w pub mem u v y q ∧ LegRoom w pub mem y v u q

private def pairCheck : Code := .block [scheduledLengthWord,compareRelayPositions,.binary .add 23 23 1]
private def rowCheck : Code := .block [.binary .add 23 21 1,.whileLt 23 3 pairCheck,.binary .add 21 21 1]

variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    {l : TableLayout} (al : l.Allocated w) {mem : ℕ → ℕ} {v : ℕ} {len : ℕ → ℕ → ℕ}
    (lengths : RelayLengthRuns pub macros l mem v len) (room : RelayRooms w l.teams len (readings pub) mem v)

include al lengths room

private theorem pair_test {u y : ℕ} (hu : u < l.teams) (hy : y < l.teams) (huy : u < y)
    (s : Bank w) (m : Memory w) (h : RelayState l mem v u (.ofWords s m)) (cur : readings s 23 = y) :
    TestRun pub macros pairCheck s m (relayPairCost (len u y))
      (∀ q < len u y, RelayWordAgrees (readings pub) mem u v y q)
      (fun z => RelayState l mem v u z ∧ z.reg 23 = y+1) := by
  let Q z := RelayState l mem v u z ∧ z.reg 23 = y ∧ z.reg 28 = len u y
  have first := (lengths u hu y hy s m h cur).asTest (by decide)
  have next (t : Bank w) (mt : Memory w) (hs : Q (.ofWords t mt)) := by
    have r21 : (t 21).val = u := hs.1.2.2.1
    have r22 : (t 22).val = v := hs.1.2.2.2
    have r23 : (t 23).val = y := hs.2.1
    have r28 : (t 28).val = len u y := hs.2.2
    have mm : readings mt = mem := hs.1.2.1
    have fit : ∀ q < (t 28).val,
        LegRoom w (readings pub) (readings mt) (t 21).val (t 22).val (t 23).val q ∧
        LegRoom w (readings pub) (readings mt) (t 23).val (t 22).val (t 21).val q := by
      rw [r21,r22,r23,r28,mm]; exact room u hu y huy hy
    have test := compareRelayPositions_test pub macros t mt (hs.1.1 0 (by decide))
      (hs.1.1 1 (by decide)) (hs.1.1 2 (by decide)) fit
    refine test.mono (cost' := len u y * (relayBody.slots+1)+2)
      (ok' := ∀ q < len u y, RelayWordAgrees (readings pub) mem u v y q)
      (Q := fun z => RelayState l mem v u z ∧ z.reg 23 = y) (by rw [r28]) (by rw [r28,r21,r22,r23,mm]) ?_
    intro z hz
    have unchanged (i : Reg) (hi : i.val ≤ 12) : z.reg i = readings t i := by
      apply hz.keep i (by omega) <;> rintro rfl <;> norm_num at hi
    exact ⟨⟨fun i hi => (unchanged i hi).trans (hs.1.1 i hi), hz.memory.trans mm,
      (hz.keep 21 (by decide) (by decide) (by decide) (by decide)).trans r21,
      (hz.keep 22 (by decide) (by decide) (by decide) (by decide)).trans r22⟩,
      (hz.keep 23 (by decide) (by decide) (by decide) (by decide)).trans r23⟩
  have inc (t : Bank w) (mt : Memory w) (hs : RelayState l mem v u (.ofWords t mt) ∧ readings t 23 = y) := by
    have step := (advance_cursor pub macros 23 (by decide) t mt y hs.1.1 hs.2 (Nat.lt_of_le_of_lt hy al.teamsFit)).asTest rfl
    refine step.mono (Q := fun z => RelayState l mem v u z ∧ z.reg 23 = y+1) le_rfl Iff.rfl ?_
    rintro z ⟨ready,cur,kept,hm⟩
    exact ⟨⟨ready,hm.trans hs.1.2.1,(kept 21 (by decide)).trans hs.1.2.2.1,
      (kept 22 (by decide)).trans hs.1.2.2.2⟩,cur⟩
  apply (first.seq fun t mt hp => (next t mt hp).seq inc).mono
  · simp [relayPairCost, Nat.add_assoc]
  · simp
  · exact fun _ hp => hp

private theorem row_test {u : ℕ} (hu : u < l.teams) (s : Bank w) (m : Memory w)
    (h : RelayState l mem v u (.ofWords s m)) :
    TestRun pub macros rowCheck s m (relayRowCost l.teams len u)
      (∀ y, u < y → y < l.teams → ∀ q < len u y, RelayWordAgrees (readings pub) mem u v y q)
      (RelayState l mem v (u+1)) := by
  let I (i : ℕ) (z : NatState) := (RelayState l mem v u z ∧ z.reg 23 = i) ∧ u < i
  let a := Code.binary .add 23 21 1
  have r21 : readings s 21 = u := h.2.2.1
  have r1 : readings s 1 = 1 := h.1 1 (by decide)
  have safe : a.safeReadOnly w (readings pub) (readings m) (readings s) := by
    change readings s 21 + readings s 1 < 2^w
    rw [r21,r1]; exact Nat.lt_of_le_of_lt hu al.teamsFit
  obtain ⟨es,t,run,cap,vals⟩ := a.runReadOnly pub macros m s safe
  have first : BoundedRun pub macros a s m 1 (I (u+1)) := by
    have out := congrFun vals
    have keep (j : Reg) (hj : j ≠ 23) : readings t j = readings s j := by
      simpa [a,Code.evalNat,hj] using out j
    refine ⟨es,t,m,run,cap,⟨⟨⟨fun j hj => (keep j (by rintro rfl; norm_num at hj)).trans (h.1 j hj),
      h.2.1,(keep 21 (by decide)).trans r21,(keep 22 (by decide)).trans h.2.2.2⟩,?_⟩,Nat.lt_succ_self _⟩⟩
    change readings t 23 = u+1
    simpa [a,Code.evalNat,addressOp,r21,r1] using out 23
  have loop (z : Bank w) (mz : Memory w) (init : I (u+1) (.ofWords z mz)) :=
    test_counted_loop 23 3 pairCheck l.teams (fun j => relayPairCost (len u j))
      (fun j => ∀ q < len u j, RelayWordAgrees (readings pub) mem u v j q) I
      (fun _ _ hz => ⟨hz.1.2,hz.1.1.1 3 (by decide)⟩)
      (fun i hi z mz hz => (pair_test pub macros al lengths room hu hi hz.2 z mz hz.1.1 hz.1.2).mono le_rfl Iff.rfl
        (fun _ h => ⟨h,Nat.lt_succ_of_lt hz.2⟩))
      (u+1) hu z mz init
  have inc (z : Bank w) (mz : Memory w) (hz : I l.teams (.ofWords z mz)) := by
    have step := (advance_cursor pub macros 21 (by decide) z mz u hz.1.1.1 hz.1.1.2.2.1
      (Nat.lt_of_le_of_lt hu al.teamsFit)).asTest rfl
    refine step.mono (Q := RelayState l mem v (u+1)) le_rfl Iff.rfl ?_
    rintro t ⟨ready,cur,kept,hm⟩
    exact ⟨ready,hm.trans hz.1.1.2.1,cur,(kept 22 (by decide)).trans hz.1.1.2.2.2⟩
  apply ((first.asTest rfl).seq fun z mz hz => (loop z mz hz).seq inc).mono
  · simp [relayRowCost, Nat.add_assoc]
  · simp
  · exact fun _ hp => hp

omit lengths room in
private theorem actualLengths (row : ℕ → TableRow) (fit : l.RowsFit w row) (hv : v < l.teams)
    (widths : ∀ i < l.teams^2, mem (l.widths+i) = l.pairWidth row l.count i) :
    RelayLengthRuns pub macros l mem v (fun u y => l.partnerLength row u v y) := by
  intro u hu y hy s m h cur
  have hm : readings m = mem := h.2.1
  obtain ⟨es,t,r,cap,ready,val,kept⟩ := scheduledLengthWord_run l row pub macros s m al fit h.1
    hu hv hy h.2.2.1 h.2.2.2 cur (by rwa [hm])
  exact ⟨es,t,m,r,cap,⟨ready,hm,(kept 21 (by decide)).trans h.2.2.1,
    (kept 22 (by decide)).trans h.2.2.2⟩,(kept 23 (by decide)).trans cur,val⟩

omit lengths room in
/-- The whole native relay test accepts exactly the physical comparisons for
all upper-triangular pairs. Its actual word-sized inner length is computed
from the real width array, before inspecting the two legs. -/
theorem checkRelays_test (row : ℕ → TableRow) (s : Bank w) (m : Memory w)
    (fit : l.RowsFit w row) (base : (pub 0).val = l.frame) (fields : l.frameFields (readings m))
    (localTeam : frameField (readings pub) (readings m) 0 = v) (hv : v < l.teams)
    (widths : ∀ i < l.teams^2, readings m (l.widths+i) = l.pairWidth row l.count i)
    (space : RelayRooms w l.teams (fun u y => l.partnerLength row u v y) (readings pub) (readings m) v) :
    let len := fun u y => l.partnerLength row u v y
    TestRun pub macros checkRelays s m (relayCheckCost l.teams len)
      (RelayChecks l.teams len (readings pub) (readings m) v) (RelayState l (readings m) v l.teams) := by
  let len := fun u y => l.partnerLength row u v y
  have length := actualLengths pub macros al row fit hv widths
  let I := RelayState l (readings m) v
  have setup := (run_tableSetup pub macros s m l al base fields).asTest (by decide)
  have frame (t : Bank w) (mt : Memory w) (hp : l.ready (.ofWords t mt) ∧ readings mt = readings m) :
      BoundedRun pub macros (readFrame 22 62 63 0) t mt 4
        (fun z => l.ready z ∧ z.mem = readings m ∧ z.reg 22 = v) := by
    have hs : (readFrame 22 62 63 0).safeReadOnly w (readings pub) (readings mt) (readings t) := by
      have hb := (pub 0).isLt
      simp (config := {decide := true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
        addressOpFits,readings,hb]
    obtain ⟨es,z,r,cap,out⟩ := (readFrame 22 62 63 0).runReadOnly pub macros mt t hs
    refine ⟨es,z,mt,r,cap,fun j hj => (congrFun out j).trans
      (((readFrame 22 62 63 0).evalNat_protected _ _ _ (lo := 13) (by decide) j (by omega)).trans
        (hp.1 j hj)),hp.2,?_⟩
    change readings z 22 = v
    rw [out,readFrameFixed,Function.update_self,hp.2]
    exact localTeam
  have init (t : Bank w) (mt : Memory w)
      (hp : l.ready (.ofWords t mt) ∧ readings mt = readings m ∧ readings t 22 = v) :
      BoundedRun pub macros (.copy 21 0) t mt 1 (I 0) := by
    apply (reset_cursor pub macros 21 (by decide) t mt hp.1).mono le_rfl
    rintro z ⟨ready,cur,kept,mm⟩
    exact ⟨ready,mm.trans hp.2.1,cur,(kept 22 (by decide)).trans hp.2.2⟩
  have loop (t : Bank w) (mt : Memory w) (hp : I 0 (.ofWords t mt)) :=
    test_counted_loop 21 3 rowCheck l.teams (relayRowCost l.teams len)
      (fun u => ∀ y, u < y → y < l.teams → ∀ q < len u y, RelayWordAgrees (readings pub) (readings m) u v y q)
      I (fun _ _ hz => ⟨hz.2.2.1,hz.1 3 (by decide)⟩)
      (fun i hi t mt hz => row_test pub macros al length space hi t mt hz)
      0 (Nat.zero_le _) t mt hp
  apply (setup.seq fun t mt hz => ((frame t mt hz).asTest (by decide)).seq fun z mz hz' =>
    ((init z mz hz').asTest rfl).seq loop).mono
  · simp [relayCheckCost,Nat.add_assoc,len]
    omega
  · simp [RelayChecks,len]
  · exact fun _ hp => hp

end RoutingISA

end BorderVNP
end Computability
end OAI
