import OAI.Computability.BorderVNP.CubeISAPacketTallyPrefix

/-! # Native execution of every selected packet in one physical declaration row

The invariant tracks the subtotal in every cut direction and preserves the
header, packet banks and all memory outside the local row and digit scratch.
Validity is tested on the actual selector words stored at each packet address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PacketTally

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM Tally
open scoped Classical

/-- An address outside both mutable work arrays. -/
def Outside (n h row scratch a : ℕ) : Prop :=
  (a < row ∨ row+(n+1) ≤ a) ∧ (a < scratch ∨ scratch+h ≤ a)

/-- Natural fit and separation facts for the fixed owned-row allocation. -/
structure Rooms (w n d blocks K h row scratch head bank stride : ℕ) : Prop where
  /-- The header fits eight words. -/
  metadata : head+7 < 2^w
  /-- Candidate enumeration fits one counter. -/
  counter : packetTrials n d blocks < 2^w
  /-- Packet stride is positive. -/
  positive : 0 < stride
  /-- The selector prefix fits in one packet. -/
  width : selectorWidth n K h ≤ stride
  /-- The complete padded packet bank fits. -/
  packets : bank+(d*d)^(n+1)*2*blocks*stride ≤ 2^w
  /-- The mutable pair row fits. -/
  rowWords : row+(n+1) ≤ 2^w
  /-- The temporary decoded edge sequence fits. -/
  digitWords : scratch+h ≤ 2^w
  /-- Row and scratch do not overlap. -/
  work : scratch+h ≤ row ∨ row+(n+1) ≤ scratch
  /-- Metadata survives the writes. -/
  metadataOutside : ∀ k < 8, Outside n h row scratch (head+k)
  /-- Every allocated packet word survives the writes. -/
  packetOutside : ∀ a, bank ≤ a → a < bank+(d*d)^(n+1)*2*blocks*stride → Outside n h row scratch a

private theorem header_transfer {mem old : ℕ → ℕ} {a n K h row scratch s : ℕ}
    (head : Header old a n K h row scratch s) (keep : ∀ k < 8, mem (a+k) = old (a+k)) :
    Header mem a n K h row scratch s :=
  ⟨(keep 0 (by decide)).trans head.bits,(keep 1 (by decide)).trans head.terms,
    (keep 2 (by decide)).trans head.radix,(keep 3 (by decide)).trans head.rowBase,
    (keep 4 (by decide)).trans head.dimension,(keep 5 (by decide)).trans head.digits,
    (keep 6 (by decide)).trans head.count,(keep 7 (by decide)).trans head.edgeWidth⟩

private theorem words_transfer (n K h : ℕ) {mem old : ℕ → ℕ} {a : ℕ}
    (same : ∀ k < selectorWidth n K h, mem (a+k) = old (a+k)) :
    (SelectorRead.Valid mem a (selectorWidth n K h) (Fintype.card (Selector n K h)) ↔
      SelectorRead.Valid old a (selectorWidth n K h) (Fintype.card (Selector n K h))) ∧
      selection n K h mem a = selection n K h old a := by
  have decoded : SelectorRead.decoded mem a (selectorWidth n K h) =
      SelectorRead.decoded old a (selectorWidth n K h) := by
    apply congrArg (VPVNP.RAMSerialization.wordBits _).symm
    exact funext fun j => by rw [same j.val j.isLt]
  have valid : SelectorRead.Valid mem a (selectorWidth n K h) (Fintype.card (Selector n K h)) ↔
      SelectorRead.Valid old a (selectorWidth n K h) (Fintype.card (Selector n K h)) := by
    unfold SelectorRead.Valid
    rw [decoded]
    exact and_congr_left' (forall_congr' fun j => forall_congr' fun hj => by rw [same j hj])
  refine ⟨valid,?_⟩
  by_cases hv : SelectorRead.Valid old a (selectorWidth n K h) (Fintype.card (Selector n K h))
  · simp only [selection,dite_eq_left hv,dite_eq_left (valid.mpr hv),Option.some.injEq]
    congr 2
    exact congrArg Fin.val decoded
  · simp only [selection,dite_eq_right hv,dite_eq_right (valid.not.mpr hv)]

private structure RowState {n d blocks : ℕ} (i : Fin (n+1)) (sym : Symbols d)
    (f : Packet n d blocks → Fin (n+1) → ℕ) (old : ℕ → ℕ) (h row scratch : ℕ)
    (reg : Reg → ℕ) (k : ℕ) (z : NatState) : Prop where
  low : ∀ r : Reg, r.val < 24 → r ≠ 18 → z.reg r = reg r
  cursor : z.reg 18 = k
  subtotal : ∀ j : Fin (n+1), z.mem (row+j.val) = old (row+j.val) + rowPrefix i sym f k j
  outside : ∀ a, Outside n h row scratch a → z.mem a = old a

private theorem ready_transfer {n d blocks : ℕ} (i : Fin (n+1)) (sym : Symbols d)
    (stride bank k : ℕ) (x y : NatState)
    (head : RoutingISA.Owned.packetReady (blocks := blocks) i sym stride bank 0 x)
    (low : ∀ r : Reg, r.val < 24 → r ≠ 18 → y.reg r = x.reg r) (cursor : y.reg 18 = k) :
    RoutingISA.Owned.packetReady (blocks := blocks) i sym stride bank k y := by
  simp only [RoutingISA.Owned.packetReady] at head ⊢
  simp only [low 0 (by decide) (by decide),low 1 (by decide) (by decide),
    low 2 (by decide) (by decide),low 10 (by decide) (by decide),low 11 (by decide) (by decide),
    low 12 (by decide) (by decide),low 13 (by decide) (by decide),low 14 (by decide) (by decide),
    low 15 (by decide) (by decide),low 16 (by decide) (by decide),low 17 (by decide) (by decide),
    low 19 (by decide) (by decide),cursor,true_and]
  tauto

/-- Complete concrete scan of a strict physical row, including skipped trials and
the native selector and accumulator callback at every valid trial. The success
condition involves only the original addressed packet words. -/
theorem row_run {w n d blocks K h : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (sym : Symbols d)
    (b s row scratch bank stride : ℕ)
    (ready : RoutingISA.Owned.packetReady (blocks := blocks) i sym stride bank 0 (.ofWords r m))
    (head : Header (readings m) (readings r 8) n K h row scratch s)
    (room : Rooms w n d blocks K h row scratch (readings r 8) bank stride)
    (sums : ∀ j : Fin (n+1), readings m (row+j.val)+packetTrials n d blocks*(h*s) < 2^w) :
    let addr := fun p : Packet n d blocks => bank+packetIndex p*stride
    let f := fun (p : Packet n d blocks) => contribution K h b s (readings m) (addr p) p
    TestRun pub mac (RoutingISA.Owned.rowLoop (RoutingISA.Owned.packetCandidate n) callback) r m
      ((∑ t : Fin (packetTrials n d blocks),
        (6*n+22 + if packetTrialValid t then cost n K h else 1))+1)
      (∀ p : {p : Packet n d blocks // p.1.1 i = sym}, SelectorRead.Valid (readings m) (addr p.val)
        (selectorWidth n K h) (Fintype.card (Selector n K h)))
      (fun z => (∀ j : Fin (n+1), z.mem (row+j.val) = readings m (row+j.val)+∑ p : {p : Packet n d blocks // p.1.1 i = sym}, f p.val j) ∧
        (∀ a, Outside n h row scratch a → z.mem a = readings m a) ∧
        (∀ q : Reg, q.val < 24 → q ≠ 18 → z.reg q = readings r q) ∧ z.reg 18 = packetTrials n d blocks) := by
  let old := readings m
  let reg := readings r
  let addr (p : Packet n d blocks) := bank+packetIndex p*stride
  let f (p : Packet n d blocks) := contribution K h b s old (addr p) p
  let I := RowState i sym f old h row scratch reg
  let good (t : Fin (packetTrials n d blocks)) := ∀ ht : packetTrialValid t,
    SelectorRead.Valid old (addr (packetRowEquiv i sym ⟨t,ht⟩).val) (selectorWidth n K h)
      (Fintype.card (Selector n K h))
  have init : I 0 (.ofWords r m) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,cur,_⟩ := ready
    exact ⟨fun _ _ _ => rfl,cur,fun j => by simp [rowPrefix,old,NatState.ofWords],fun _ _ => rfl⟩
  have stable : RoutingISA.Owned.stableLow I := fun k z y hs keep hm =>
    ⟨fun j hj ne => (keep j hj).trans (hs.low j hj ne),(keep 18 (by decide)).trans hs.cursor,
      fun j => (congrFun hm _).trans (hs.subtotal j),fun a ha => (congrFun hm a).trans (hs.outside a ha)⟩
  have regs k z (hs : I k z) := ready_transfer i sym stride bank k _ z ready hs.low hs.cursor
  have skip (t : Fin (packetTrials n d blocks)) (ht : ¬packetTrialValid t) (z : NatState) (hs : I t.val z) :
      I (t.val+1) (RoutingISA.Owned.increment 18 z) := by
    refine ⟨fun j hj ne => (Function.update_of_ne ne ..).trans (hs.low j hj ne),
      by simp [RoutingISA.Owned.increment,hs.cursor],
      fun j => ?_,hs.outside⟩
    simpa only [RoutingISA.Owned.increment,prefix_skip i sym f t ht] using hs.subtotal j
  have visit (t : Fin (packetTrials n d blocks)) (ht : packetTrialValid t) (u : Bank w) (mu : Memory w)
      (hs : I t.val (.ofWords u mu)) (atPacket : RoutingISA.Owned.packetAt i sym stride bank t (.ofWords u mu)) :
      TestRun pub mac callback u mu (cost n K h) (good t) (RoutingISA.Owned.nextAt I 18 t.val) := by
    let p := (packetRowEquiv i sym ⟨t,ht⟩).val
    have rank := trialPacketIndex_eq i sym ⟨t,ht⟩
    have pk : readings u 24 = addr p := by simpa only [NatState.ofWords,addr,p,← rank] using atPacket.1
    have pkIndex : packetIndex p < (d*d)^(n+1)*2*blocks := rank ▸ trialPacketIndex_lt i sym t
    have bound : addr p+stride ≤ bank+(d*d)^(n+1)*2*blocks*stride := by
      have v := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt pkIndex)
      rw [Nat.succ_mul] at v
      dsimp [addr]; omega
    have width := room.width
    have packetSpace := room.packets
    have packetRoom : addr p+selectorWidth n K h ≤ 2^w := by omega
    have h8 : readings u 8 = reg 8 := hs.low 8 (by decide) (by decide)
    have live : Header (readings mu) (readings u 8) n K h row scratch s := by
      rw [h8]
      exact header_transfer head fun k hk => hs.outside _ (room.metadataOutside k hk)
    have liveBits (k : ℕ) (hk : k < selectorWidth n K h) :
        readings mu (addr p+k) = old (addr p+k) := by
      apply hs.outside _ (room.packetOutside _ ?_ ?_)
      · dsimp [addr]; omega
      · omega
    have ⟨valid,sel⟩ := words_transfer n K h liveBits
    have fit (j : ℕ) (hj : j < n+1) : readings mu (row+j)+h*s < 2^w := by
      let v : Fin (n+1) := ⟨j,hj⟩
      have start := hs.subtotal v
      change readings mu (row+j) = old (row+j)+rowPrefix i sym f t.val v at start
      have sum := sums v
      have pre := prefix_le i sym f (h*s) (fun p j => contribution_le ..) t.val v
      have mx := Nat.mul_le_mul_right (h*s) (Nat.succ_le_of_lt t.isLt)
      rw [Nat.succ_mul] at mx
      change old (row+j)+packetTrials n d blocks*(h*s) < _ at sum
      omega
    have run := callback_test (pub := pub) (mac := mac) u mu p b s row scratch (addr p) pk live
      (h8 ▸ room.metadata) packetRoom room.rowWords room.digitWords room.work fit
    apply run.mono le_rfl (valid.trans ⟨fun good _ => good,fun good => good ht⟩)
    rintro z ⟨⟨rows,out⟩,low⟩
    have cur := (low 18 (by decide)).trans hs.cursor
    have one : reg 1 = 1 := ready.2.1
    refine ⟨(low 1 (by decide)).trans ((hs.low 1 (by decide) (by decide)).trans one),cur,
      ⟨fun j hj ne => (Function.update_of_ne ne ..).trans ((low j (by omega)).trans (hs.low j hj ne)),
      by simp [RoutingISA.Owned.increment,cur],fun j => ?_,
      fun a ha => (out a ha.1 ha.2).trans (hs.outside a ha)⟩⟩
    have cg : contribution K h b s (readings mu) (addr p) p j = f p j := by
      simp only [f,contribution,sel]
    change z.mem (row+j.val) = old (row+j.val) + rowPrefix i sym f (t.val+1) j
    rw [rows j,cg,show readings mu (row+j.val) = _ from hs.subtotal j,prefix_valid i sym f t ht]
    exact Nat.add_assoc ..
  have run := RoutingISA.Owned.packetRow_run pub mac i sym stride bank callback (fun _ => cost n K h)
    good I stable regs room.counter room.positive (fun t => trialPacketBase_lt i sym t room.positive room.packets)
    visit skip r m init
  apply run.mono le_rfl ?_ ?_
  · constructor
    · intro all p
      let t := (packetRowEquiv i sym).symm p
      have same : packetRowEquiv i sym t = p := Equiv.apply_symm_apply ..
      exact same ▸ all t.val t.property t.property
    · intro all t ht _
      exact all (packetRowEquiv i sym ⟨t,ht⟩)
  · intro z hs
    exact ⟨fun j => (hs.subtotal j).trans (congrArg (old (row+j.val)+·) (prefix_full i sym f j)),
      hs.outside,hs.low,hs.cursor⟩

/-- Constant setup, linear selector read and one quotient and row update per slot. -/
theorem cost_eq (n K h : ℕ) : cost n K h = 39 + 12*selectorWidth n K h + 15*h := by
  change 24+(4+selectorWidth n K h*12+1+3+(15*h+7)) = _
  omega

/-- On the selector assignment stored in the owned packet banks, the entire packet
pass adds exactly the first sum in the strict physical row formula. -/
theorem physical_row_run {w n d blocks K h : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (sym : Symbols d)
    (b s row scratch bank stride : ℕ) (select : Packet n d blocks → Selector n K h)
    (ready : RoutingISA.Owned.packetReady (blocks := blocks) i sym stride bank 0 (.ofWords r m))
    (head : Header (readings m) (readings r 8) n K h row scratch s)
    (room : Rooms w n d blocks K h row scratch (readings r 8) bank stride)
    (sums : ∀ j : Fin (n+1), readings m (row+j.val)+packetTrials n d blocks*(h*s) < 2^w)
    (stored : ∀ p : {p : Packet n d blocks // p.1.1 i = sym},
      SelectorRead.Stored (readings m) (bank+packetIndex p.val*stride) (select p.val)) :
    BoundedRun pub mac (RoutingISA.Owned.rowLoop (RoutingISA.Owned.packetCandidate n) callback) r m
      ((∑ t : Fin (packetTrials n d blocks),
        (6*n+22 + if packetTrialValid t then cost n K h else 1))+1)
      (fun z => (∀ j : Fin (n+1), z.mem (row+j.val) = readings m (row+j.val) +
        ∑ t : {t : Fin (packetTrials n d blocks) // packetTrialValid t},
          crossCount b s select (.inl (packetRowEquiv i sym t).val) j) ∧
        (∀ a, Outside n h row scratch a → z.mem a = readings m a) ∧
        (∀ q : Reg, q.val < 24 → q ≠ 18 → z.reg q = readings r q) ∧ z.reg 18 = packetTrials n d blocks) := by
  have run := row_run pub mac r m i sym b s row scratch bank stride ready head room sums
  have valid (p : {p : Packet n d blocks // p.1.1 i = sym}) :
      SelectorRead.Valid (readings m) (bank+packetIndex p.val*stride) (selectorWidth n K h)
        (Fintype.card (Selector n K h)) := by
    refine ⟨fun j hj => ?_,(stored p).rank ▸ (selectorOrder n K h (select p.val)).isLt⟩
    rw [stored p ⟨j,hj⟩]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)
  apply (run.complete valid).mono le_rfl
  rintro z ⟨rowAt,remaining⟩
  refine ⟨fun j => (rowAt j).trans (congrArg (readings m (row+j.val)+·) ?_),remaining⟩
  apply Fintype.sum_equiv (packetRowEquiv i sym).symm
  intro p
  rw [Equiv.apply_symm_apply]
  simp only [contribution,selection_of_stored (stored p)]
  rfl

end Cube.PacketTally

end BorderVNP
end Computability
end OAI
