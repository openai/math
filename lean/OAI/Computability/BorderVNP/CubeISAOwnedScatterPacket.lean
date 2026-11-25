import OAI.Computability.BorderVNP.CubeISAOwnedScatterShape
import OAI.Computability.BorderVNP.CubeScatterPacketInverse

/-! # Native callback scattering one selected packet in the owned-row traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.VertexIndex VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Common, choice-free part of every path through an owned packet. -/
def ownedPrefix (n K h : ℕ) : Code := .seq (copySelectors n K h) decodeOwner

/-- Full native callback at a valid packet trial. -/
def ownedPacket (n b h K s : ℕ) : Code := .seq (ownedPrefix n K h) (scatterPacket n b h K s)

/-- Tick allowance for a packet callback with its actual radix table and reserved rectangle. -/
def ownedPacketCost (n b h K s : ℕ) : ℕ :=
  4 * selectorWidth n K h + 3 + decodeOwnerCost n (selectorWidth n K h) +
  (2 * (Fintype.card (Selector n K h) + (n+1)) + 4 * bodyWidth n b h s + 4)

/-- The physical copy of a selector stores the bits expected by the ordinary reader. -/
theorem selectorImage_stored (m : Memory w) (base : ℕ) (u : Selector n K h) (one : 1 < 2^w) :
    SelectorRead.Stored (readings (image (selectorPositions u) base m)) base u := by
  intro j
  let bit := VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
    (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j
  have hit := image_at (selectorPositions u) base m
    ⟨j.val, by simpa only [selectorPositions,List.length_ofFn] using j.isLt⟩ (b := bit)
    (by simp [bit,selectorPositions,Position.value])
  exact (congrArg Fin.val hit).trans (word_val _ _ (bit.toNat_le.trans_lt one))

/-- The prefix contains neither nondeterministic bits nor private calls. -/
theorem ownedPrefix_deterministic : (ownedPrefix n K h).deterministic = true := by
  have prog (k : ℕ) : (program (List.replicate k .selector)).deterministic = true := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ,program,Code.deterministic,ih,Bool.and_true]
      decide
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨by decide,prog _⟩,by decide⟩

/-- Every valid prefix returns the real selector and owner keys, leaving the two routed
cursors at the end of the selector copy and the beginning of the crossing stream. -/
theorem ownedPrefix_run (src : Set ℕ) (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (u : Selector n K h) (c : Cursor) (r : Bank w) (m : Memory w)
    (entry : OwnerInput (K := K) (h := h) p i high r) (sel : r 36 = word w c.selector)
    (cross : r 37 = word w c.crossing) (addr : readings r 24 = c.dest)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : c.dest + selectorWidth n K h ≤ 2^w)
    (input : Prepared src (selectorPositions u) c m) :
    ∃ t es, Runs pub mac (ownedPrefix n K h) r m es t (image (selectorPositions u) c.dest m) ∧
      TraceOK es [] es.length ∧ traceCost es ≤ 4*selectorWidth n K h+3+decodeOwnerCost n (selectorWidth n K h) ∧
      (advance (selectorPositions u) c).loaded t ∧ t 43 = word w (selectorOrder n K h u).val ∧
      t 44 = word w (2^i.val) ∧ t 45 = wordBit w (ownerBit i p.1.2 high) ∧
      ∀ j : Reg, j.val < 36 → t j = r j := by
  have base : r 24 = word w c.dest :=
    Fin.ext (addr.trans (word_val _ _ (addr ▸ (r 24).isLt)).symm)
  obtain ⟨a,es,copy,copied,cost,loaded,keep⟩ := copySelectors_run pub mac src u c r m sel cross base input
  let bank := image (selectorPositions u) c.dest m
  have one : 1 < 2^w := (Nat.one_le_pow (n+1) 2 (by decide)).trans_lt ((le_max_right ..).trans_lt fit)
  have safe (j : Reg) (hj : j.val < 36) : a j = r j :=
    keep j ((by decide : ∀ j : Reg, j.val < 36 → j ∉ ([36,37,38,59,60] : List Reg)) j hj)
  have owner : OwnerInput (K := K) (h := h) p i high a := by
    rcases entry with ⟨hu,ho,hg,ha,hn,hw,hk⟩
    exact ⟨(congrArg Fin.val (safe 15 (by decide))).trans hu,(congrArg Fin.val (safe 25 (by decide))).trans ho,
      (congrArg Fin.val (safe 3 (by decide))).trans hg,(congrArg Fin.val (safe 4 (by decide))).trans ha,
      (congrArg Fin.val (safe 5 (by decide))).trans hn,(congrArg Fin.val (safe 8 (by decide))).trans hw,
      (congrArg Fin.val (safe 9 (by decide))).trans hk⟩
  obtain ⟨t,fs,decode,clear,budget,key,place,side,frame⟩ := decodeOwner_run
    (pub := pub) (mac := mac) p i high u a bank c.dest owner
    ((congrArg Fin.val (safe 24 (by decide))).trans addr) (selectorImage_stored m c.dest u one) fit room
  have untouched (j : Reg) (hj : j.val < 39 ∨ j = 59) : t j = a j :=
    frame j ((by decide : ∀ j : Reg, j.val < 39 ∨ j = 59 → j ∉ decodeScratch) j hj)
  refine ⟨t,es++fs,copy.seq decode,by simpa using copied.append clear,
    (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cost budget),?_,key,place,side,
    fun j hj => (untouched j (.inl (by omega))).trans (safe j hj)⟩
  exact ⟨(untouched 36 (by decide)).trans loaded.1,(untouched 37 (by decide)).trans loaded.2.1,
    (untouched 38 (by decide)).trans loaded.2.2.1,(untouched 59 (by decide)).trans loaded.2.2.2⟩

/-- A complete selected-packet execution produces the prescribed two-stage bank image.
Only locally owned positions consume choices; every other event has positive sign as well.
All low registers survive for the enclosing trial and symbol-row loops. -/
theorem ownedPacket_run (src : Set ℕ) (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (u : Selector n K h) (c : Cursor) (r : Bank w) (m : Memory w)
    (entry : OwnerInput (K := K) (h := h) p i high r) (sel : r 36 = word w c.selector)
    (cross : r 37 = word w c.crossing) (addr : readings r 24 = c.dest)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : c.dest + selectorWidth n K h ≤ 2^w)
    (input : Prepared src (selectorPositions u) c m)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool)
    (body : Prepared src (bodyPositions u i (ownerBit i p.1.2 high) x z) (advance (selectorPositions u) c)
      (image (selectorPositions u) c.dest m)) :
    let ps := bodyPositions u i (ownerBit i p.1.2 high) x z
    let mid := advance (selectorPositions u) c
    ∃ t es, Runs pub mac (ownedPacket n b h K s) r m es t (image ps mid.dest (image (selectorPositions u) c.dest m)) ∧
      TraceOK es ((ps.map Position.digit).flatMap Digit.choices) es.length ∧
      traceCost es ≤ ownedPacketCost n b h K s ∧ (advance ps mid).loaded t ∧
      ∀ j : Reg, j.val < 36 → t j = r j := by
  intro ps mid
  obtain ⟨a,es,pre,clear,hcost,loaded,key,place,side,keep⟩ :=
    ownedPrefix_run (pub := pub) (mac := mac) src p i high u c r m entry sel cross addr fit room input
  obtain ⟨t,fs,run,trace,budget,hfinal,frame⟩ := scatterPacket_run pub mac src u i (ownerBit i p.1.2 high) a
    (image (selectorPositions u) c.dest m) mid loaded key place side fit x z body
  refine ⟨t,es++fs,pre.seq run,by simpa using clear.append trace,
    (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hcost budget),hfinal,?_⟩
  intro j hj
  exact (frame j ((by decide : ∀ j : Reg, j.val < 36 → j ∉ ([36,37,38,58,60] : List Reg)) j hj)).trans (keep j hj)

/-- Given its deterministic prefix, every native return has precisely the digit realization
of the dispatched owner, including the exact chronology of the prefix and the digit actions. -/
theorem ownedPacket_iff {u : Selector n K h} {i : Fin (n+1)} {owner : Bool} {r a : Bank w}
    {m ma : Memory w} {pre} (preRun : Runs pub mac (ownedPrefix n K h) r m pre a ma)
    (one : a 59 = 1) (key : a 43 = word w (selectorOrder n K h u).val)
    (place : a 44 = word w (2^i.val)) (side : a 45 = wordBit w owner)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w) {es t mt} :
    Runs pub mac (ownedPacket n b h K s) r m es t mt ↔
      ∃ ds : List Digit, ds.map Digit.mode = bodyModes b s u i owner ∧
        let e := result ds (Function.update a (58 : Reg) 0) ma
        es = pre ++ (List.replicate (dispatchTicks (selectorOrder n K h u) i owner) (tick w) ++ e.trace) ∧
          t = e.bank ∧ mt = e.mem := by
  constructor
  · intro whole
    obtain ⟨ls,fs,y,my,htr,head,tail⟩ := Runs.seq_iff.mp whole
    obtain ⟨rfl,rfl,rfl⟩ := head.unique_of_deterministic ownedPrefix_deterministic preRun
    obtain ⟨ds,modes,ht,bank,mem⟩ := (scatterPacket_iff u i owner _ _ one key place side fit).mp tail
    exact ⟨ds,modes,htr.trans (congrArg (_ ++ ·) ht),bank,mem⟩
  · rintro ⟨ds,modes,rfl,rfl,rfl⟩
    exact preRun.seq ((scatterPacket_iff u i owner _ _ one key place side fit).mpr ⟨ds,modes,rfl,rfl,rfl⟩)

end Cube.Scatter

end BorderVNP
end Computability
end OAI
