import OAI.Computability.BorderVNP.CubeISAOwnedPacketRowModel

/-! # Native selected-packet scatter across a whole strict symbol row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.PacketRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned Physical.VertexIndex
open VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally Finset

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

/-- Entry state of the physical strict-row packet loop. -/
structure Entry (r : Bank w) (m : Memory w) : Prop where
  /-- All fields of the ordinary mixed-radix trial iterator. -/
  scan : packetReady (blocks := blocks) D.axis D.pair D.stride D.base 0 (.ofWords r m)
  /-- Local side's grouping symbol. -/
  group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val
  /-- Grouping coordinate. -/
  axis : readings r 4 = D.axis.val
  /-- Number of remaining coordinates. -/
  dim : readings r 5 = n
  /-- Selector bit width. -/
  width : readings r 8 = selectorWidth n K h
  /-- Cardinality of the selector range. -/
  count : readings r 9 = Fintype.card (Selector n K h)
  /-- Next routed selector word. -/
  selector : r 36 = word w D.selector
  /-- Next routed crossing word. -/
  crossing : r 37 = word w D.crossing

/-- Full physical packet-row postcondition at a chronological trial prefix. -/
structure At (r₀ : Bank w) (m₀ : Memory w) (k : ℕ) (r : Bank w) (m : Memory w) : Prop where
  /-- Persistent low words, excluding the live trial cursor. -/
  low : ∀ j : Reg, j.val < 24 → j ≠ 18 → r j = r₀ j
  /-- Trial cursor. -/
  trial : readings r 18 = k
  /-- Routed selector cursor. -/
  selector : r 36 = word w (D.before m₀ k).sel
  /-- Routed crossing cursor. -/
  crossing : r 37 = word w (D.before m₀ k).cross
  /-- Actual complete memory image. -/
  memory : m = (D.before m₀ k).mem

private theorem bump {r₀ r : Bank w} {m₀ m : Memory w} {k : ℕ} (one : readings r 1 = 1)
    (trial : readings r 18 = k) (cap : k+1 < 2^w) (low : ∀ j : Reg, j.val < 24 → j ≠ 18 → r j = r₀ j)
    (sel : r 36 = word w (D.before m₀ (k+1)).sel) (cross : r 37 = word w (D.before m₀ (k+1)).cross)
    (hm : m = (D.before m₀ (k+1)).mem) : D.At r₀ m₀ (k+1) (bumpBank r 18) m := by
  have fits : (r 18).val + (r 1).val < 2^w := by
    change readings r 18 + readings r 1 < _
    rwa [trial,one]
  refine ⟨fun j hj hn => (Function.update_of_ne hn ..).trans (low j hj hn),?_,sel,cross,hm⟩
  change ((Function.update r 18 (r 18 + r 1)) 18).val = k+1
  rw [Function.update_self,Fin.val_add_eq_of_add_lt fits]
  exact congrArg₂ Nat.add trial one

/-- Actual trial preparation, selector copying and validation, owner dispatch, and private
or routed stores for every selected packet of the row. The only nondeterministic bits are
the assigned local demands and internal supplies, in their native chronological order. -/
theorem scatterRow_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r₀ : Bank w) (m₀ : Memory w) (entry : D.Entry r₀ m₀)
    (prepared : D.PreparedRow src m₀) (positive : 0 < D.stride)
    (width : selectorWidth n K h ≤ D.stride)
    (allocation : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ 2^w)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w) :
    TraceRun pub mac (rowLoop (packetCandidate n) (ownedPacket n b h K s)) r₀ m₀
      (rowChoices packetTrialValid D.choices)
      ((∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then ownedPacketCost n b h K s else 1))+1)
      (D.At r₀ m₀ (packetTrials n d blocks)) := by
  let N := packetTrials n d blocks
  let I := D.At r₀ m₀
  let addr (t : Fin N) := D.base + trialPacketIndex d ((d*d)^D.axis.val) blocks D.pair.val.1.val D.pair.val.2.val t.val * D.stride
  let P (t : Fin N) (r : Bank w) (m : Memory w) := I t.val r m ∧
    readings r 24 = addr t ∧ readings r 25 = t.val/blocks%2 ∧ readings r 40 = if packetTrialValid t then 1 else 0
  obtain ⟨r0,r1,r2,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19⟩ := entry.scan
  have cap : N < 2^w := by change packetTrials n d blocks < _; rw [← r19]; exact (r₀ 19).isLt
  have regs k r m (hi : I k r m) : readings r 18 = k ∧ readings r 19 = N :=
    ⟨hi.trial,(congrArg Fin.val (hi.low 19 (by decide) (by decide))).trans r19⟩
  have space (t : Fin N) : addr t + D.stride ≤ 2^w := by
    have le := Nat.mul_le_mul_right D.stride (Nat.succ_le_of_lt (trialPacketIndex_lt D.axis D.pair t))
    rw [Nat.succ_mul] at le
    dsimp only [addr]
    omega
  have prepare (t : Fin N) r m (hi : I t.val r m) :
      TraceRun pub mac (packetCandidate n) r m [] (6*n+19) (P t) := by
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (hi.low j hj hn)
    have prep := packetCandidate_run pub mac r m D.axis D.pair t
      ((low 0 (by decide) (by decide)).trans r0) ((low 1 (by decide) (by decide)).trans r1)
      ((low 2 (by decide) (by decide)).trans r2) ((low 10 (by decide) (by decide)).trans r10)
      ((low 11 (by decide) (by decide)).trans r11) ((low 12 (by decide) (by decide)).trans r12)
      ((low 13 (by decide) (by decide)).trans r13) ((low 14 (by decide) (by decide)).trans r14)
      ((low 15 (by decide) (by decide)).trans r15) ((low 16 (by decide) (by decide)).trans r16)
      ((low 17 (by decide) (by decide)).trans r17) hi.trial positive
      ((Nat.lt_add_of_pos_right positive).trans_le (space t))
    apply (packetCandidate_traced prep).mono le_rfl
    rintro y my ⟨⟨base,ori,_,flag,keep,mem⟩,sel,cross⟩
    exact ⟨⟨fun j hj hn => (Fin.ext (keep j hj)).trans (hi.low j hj hn),(keep 18 (by decide)).trans hi.trial,
      sel.trans hi.selector,cross.trans hi.crossing,(funext fun j => Fin.ext (congrFun mem j)).trans hi.memory⟩,base,ori,flag⟩
  have flag t r m (hp : P t r m) : r 40 = r 1 ↔ packetTrialValid t := by
    obtain ⟨hi,_,_,flag⟩ := hp
    have unit : readings r 1 = 1 := (congrArg Fin.val (hi.low 1 (by decide) (by decide))).trans r1
    rw [Fin.ext_iff]
    change readings r 40 = readings r 1 ↔ _
    by_cases h : packetTrialValid t <;> simp [flag,unit,h]
  have visit (t : Fin N) (ok : packetTrialValid t) r m (hp : P t r m) :
      TraceRun pub mac (ownedPacket n b h K s) r m (D.choices t) (ownedPacketCost n b h K s)
        (fun y my => I (t.val+1) (bumpBank y 18) my) := by
    obtain ⟨hi,base,ori,_⟩ := hp
    let p := D.packet t ok
    let c := D.cursor p (D.before m₀ t.val)
    obtain ⟨_,row,orient,rank⟩ := OwnedVertex.selected_fields D.axis D.pair t ok
    have eqRow : p.1.1 D.axis = D.pair := row
    have eqBase : addr t = c.dest := congrArg (fun k => D.base+k*D.stride) rank
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (hi.low j hj hn)
    have grp : readings r 3 = (groupSymbol p D.axis D.high).val := by
      rw [groupSymbol,eqRow]
      exact (low 3 (by decide) (by decide)).trans entry.group
    have upper : readings r 15 = (p.1.1 D.axis).val.2.val :=
      (low 15 (by decide) (by decide)).trans (r15.trans ((congrArg (fun q : Symbols d => q.val.2.val) eqRow).symm))
    have fields : OwnerInput (K := K) (h := h) p D.axis D.high r :=
      ⟨upper,ori.trans orient.symm,grp,(low 4 (by decide) (by decide)).trans entry.axis,
        (low 5 (by decide) (by decide)).trans entry.dim,(low 8 (by decide) (by decide)).trans entry.width,
        (low 9 (by decide) (by decide)).trans entry.count⟩
    have ready := prepared_congr _ _ _ m
      (fun j hj => (congrFun hi.memory j).trans (D.before_source m₀ prepared t.val j hj)) (prepared t ok)
    obtain ⟨pre,after⟩ := ready.split
    have room : c.dest+selectorWidth n K h ≤ 2^w := eqBase ▸ (Nat.add_le_add_left width _).trans (space t)
    obtain ⟨y,es,run,trace,cost,final,keep⟩ := ownedPacket_run (pub := pub) (mac := mac) src p D.axis D.high (D.select p)
      c r m fields hi.selector hi.crossing (base.trans eqBase) fit room pre (D.demand p) (D.supply p) after
    rw [ownedPacket_advance] at final
    refine ⟨es,y,_,run,by simpa only [choices,ok,dite_true,body,p] using trace,cost,?_⟩
    apply D.bump ((congrArg Fin.val (keep 1 (by decide))).trans ((low 1 (by decide) (by decide)).trans r1))
      ((congrArg Fin.val (keep 18 (by decide))).trans hi.trial) ((Nat.succ_le_of_lt t.isLt).trans_lt cap)
      (fun j hj hn => (keep j (by omega)).trans (hi.low j hj hn))
    · rw [D.before_visit m₀ t ok]
      exact final.1
    · rw [D.before_visit m₀ t ok]
      exact final.2.1
    · rw [D.before_visit m₀ t ok,selectors_advance,hi.memory]
      rfl
  have skip (t : Fin N) (no : ¬packetTrialValid t) r m (hp : P t r m) : I (t.val+1) (bumpBank r 18) m := by
    have hi := hp.1
    apply D.bump ((congrArg Fin.val (hi.low 1 (by decide) (by decide))).trans r1) hi.trial
      ((Nat.succ_le_of_lt t.isLt).trans_lt cap) hi.low
    · simpa only [D.before_skip m₀ t no] using hi.selector
    · simpa only [D.before_skip m₀ t no] using hi.crossing
    · simpa only [D.before_skip m₀ t no] using hi.memory
  exact traceRow_run (packetCandidate n) (ownedPacket n b h K s) (6*n+19) packetTrialValid D.choices
    (fun _ => ownedPacketCost n b h K s) I P regs prepare flag visit skip r₀ m₀
    ⟨fun _ _ _ => rfl,r18,entry.selector,entry.crossing,rfl⟩

end Cube.Scatter.PacketRowData

end BorderVNP
end Computability
end OAI
