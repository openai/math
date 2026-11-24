import OAI.Computability.VPVNP.CompressorShrinkDemandGatherCall
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.CompressorRecordGreedy

/-!
# Gathering the two rectangular shrink demands in motif order

The AB and CD rectangles may use different strides. Each visit reads one
cell of each rectangle and writes both values into the next dense demand
row. The output is disjoint from both sources. Source padding is never read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkDemandGather

open BurstRAM BurstRAM.PrivateRAM

variable {w B Q : ℕ} {p : Fin 6 → Word w}

/-- The two source rectangles need room for their strides and the destination
needs two cells per motif. Either rectangle can precede or follow the output. -/
structure Layout (B Q : ℕ) (p : Fin 6 → Word w) : Prop where
  columns : (p 0).val = Q
  abStride : Q ≤ (p 1).val
  cdStride : Q ≤ (p 2).val
  abFit : (p 3).val+B*(p 1).val ≤ 2^w
  cdFit : (p 4).val+B*(p 2).val ≤ 2^w
  denseFit : (p 5).val+2*(B*Q) ≤ 2^w
  abApart : (p 3).val+B*(p 1).val ≤ (p 5).val ∨ (p 5).val+2*(B*Q) ≤ (p 3).val
  cdApart : (p 4).val+B*(p 2).val ≤ (p 5).val ∨ (p 5).val+2*(B*Q) ≤ (p 4).val

private abbrev word (i : ℕ) : Word w := Fin.ofNat _ i

private def sourceCell (p : Fin 6 → Word w) (Q i : ℕ) (s a : Fin 6) : ℕ :=
  (p a).val+(i/Q)*(p s).val+i%Q

private theorem packed_lt {b r B Q : ℕ} (hb : b < B) (hr : r < Q) : b*Q+r < B*Q := by
  have h := Nat.mul_le_mul_right Q hb
  rw [Nat.succ_mul] at h
  omega

private theorem source_bounds (L : Layout B Q p) {i : ℕ} (hi : i < B*Q) (s a : Fin 6)
    (stride : Q ≤ (p s).val) (fit : (p a).val+B*(p s).val ≤ 2^w)
    (apart : (p a).val+B*(p s).val ≤ (p 5).val ∨ (p 5).val+2*(B*Q) ≤ (p a).val) :
    (src p (word i) s a).val = sourceCell p Q i s a ∧
      (sourceCell p Q i s a < (p 5).val ∨ (p 5).val+2*(B*Q) ≤ sourceCell p Q i s a) := by
  have hq : 0 < Q := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hi
  have ho := packed_lt ((Nat.div_lt_iff_lt_mul hq).mpr hi) ((Nat.mod_lt i hq).trans_le stride)
  have hx : i < 2^w := by have := L.denseFit; omega
  have hv : (word (w := w) i).val = i := Nat.mod_eq_of_lt hx
  have hdiv : (BinaryOp.div.eval (word i) (p 0)).val = i/Q := by
    change ((word (w := w) i).val / (p 0).val) % (2^w) = _
    rw [hv, L.columns, Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt hx)]
  have hmod : (BinaryOp.mod.eval (word i) (p 0)).val = i%Q := by
    change ((word (w := w) i).val % (p 0).val) % (2^w) = _
    rw [hv, L.columns, Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt hx)]
  constructor
  · simp only [src, Fin.val_add, Fin.val_mul, hdiv, hmod, Nat.mod_add_mod, Nat.add_mod_mod, sourceCell]
    apply Nat.mod_eq_of_lt
    omega
  · unfold sourceCell
    omega

/-- Each physical read address belongs to its live input rectangle. -/
theorem source_range (L : Layout B Q p) {i : ℕ} (hi : i < B*Q) (s a : Fin 6)
    (stride : Q ≤ (p s).val) (fit : (p a).val+B*(p s).val ≤ 2^w)
    (apart : (p a).val+B*(p s).val ≤ (p 5).val ∨ (p 5).val+2*(B*Q) ≤ (p a).val) :
    (p a).val ≤ (src p (word i) s a).val ∧ (src p (word i) s a).val < (p a).val+B*(p s).val := by
  rw [(source_bounds L hi s a stride fit apart).1]
  have hq : 0 < Q := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hi
  have h := packed_lt ((Nat.div_lt_iff_lt_mul hq).mpr hi) ((Nat.mod_lt i hq).trans_le stride)
  unfold sourceCell
  omega

theorem dest_bounds (L : Layout B Q p) {i : ℕ} (hi : i < B*Q) :
    (dst p (word i)).val = (p 5).val+2*i ∧ (dst p (word i)+1).val = (p 5).val+2*i+1 := by
  have h := L.denseFit
  have hv : (word (w := w) i).val = i := Nat.mod_eq_of_lt (by omega)
  have h₁ : (dst p (word i)).val = (p 5).val+2*i := by
    rw [dst, Fin.val_add, Fin.val_add, hv, Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨h₁, by rw [Fin.val_add, h₁, Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]⟩

private structure Prefix (p : Fin 6 → Word w) (Q k : ℕ) (ref mem : Memory w) : Prop where
  rows : ∀ j < k, mem ((p 5).val+2*j) = ref (sourceCell p Q j 1 3) ∧
    mem ((p 5).val+2*j+1) = ref (sourceCell p Q j 2 4)
  frame : ∀ a, a < (p 5).val ∨ (p 5).val+2*k ≤ a → mem a = ref a

private theorem step (L : Layout B Q p) {ref mem : Memory w} {i : ℕ} (hi : i < B*Q)
    (old : Prefix p Q i ref mem) : Prefix p Q (i+1) ref (after mem (visits p (word i) mem).events) := by
  obtain ⟨ha, fa⟩ := source_bounds L hi 1 3 L.abStride L.abFit L.abApart
  obtain ⟨hb, fb⟩ := source_bounds L hi 2 4 L.cdStride L.cdFit L.cdApart
  obtain ⟨hd, he⟩ := dest_bounds L hi
  have hA := old.frame (sourceCell p Q i 1 3) (by omega)
  have hC := old.frame (sourceCell p Q i 2 4) (by omega)
  rw [visit_after]
  constructor
  · intro j hj
    simp only [writeMemory, ha, hb, hd, he, hA, hC]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with heq | h
    · subst j
      simp
    · simpa only [ite_eq_right (show (p 5).val+2*j ≠ (p 5).val+2*i by omega),
        ite_eq_right (show (p 5).val+2*j ≠ (p 5).val+2*i+1 by omega),
        ite_eq_right (show (p 5).val+2*j+1 ≠ (p 5).val+2*i by omega),
        ite_eq_right (show (p 5).val+2*j+1 ≠ (p 5).val+2*i+1 by omega)] using old.rows j h
  · intro a h
    simpa only [writeMemory, hd, he, ite_eq_right (show a ≠ (p 5).val+2*i by omega),
      ite_eq_right (show a ≠ (p 5).val+2*i+1 by omega)] using old.frame a (by omega)

private def SiteCost (r : Report w) : Prop :=
  r.events.length = cost ∧ countProbes r.events = 4 ∧ choiceBits r.events = [] ∧ r.events.count .tick = 20

private theorem segment (L : Layout B Q p) {ref mem : Memory w} {i cap : ℕ}
    (hcap : cost < cap) (old : Prefix p Q i ref mem) (steps : ℕ) (bound : i+steps ≤ B*Q) :
    ∃ rs, runSegment (program p) cap (some (word i)) mem (List.replicate steps []) = some rs ∧
      endState (some (word i)) rs = some (word (i+steps)) ∧
      Prefix p Q (i+steps) ref (after mem (eventLog rs)) ∧ rs.length = steps ∧ ∀ r ∈ rs, SiteCost r := by
  induction steps generalizing i mem with
  | zero => exact ⟨[], rfl, rfl, old, rfl, by simp⟩
  | succ s ih =>
    let r := visits p (word i) mem
    have hn : word (w := w) i+1 = word (i+1) := by
      apply Fin.ext
      simp [word, Fin.val_add, Nat.add_mod_mod, Nat.mod_add_mod]
    have hr : r.result = some (word (i+1)) := by rw [show r.result = _ from visits_result p (word i) mem, hn]
    have hs : i+1+s = i+(s+1) := by omega
    obtain ⟨rs, run, stop, state, len, costs⟩ := ih (step L (by omega) old) (by omega)
    refine ⟨r::rs, ?_, ?_, ?_, by simp [len], ?_⟩
    · rw [List.replicate_succ, runSegment, visit_run p (word i) mem hcap]
      change (runSegment _ _ r.result (after mem r.events) _).map _ = _
      rw [hr, run]; rfl
    · change endState r.result rs = _
      rw [hr, stop, hs]
    · change Prefix p Q _ ref ((r.events ++ eventLog rs).foldl BurstRAM.update mem)
      rw [List.foldl_append, ← hs]; exact state
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · obtain ⟨e, pr, bs⟩ := visit_cost p (word i) mem
        exact ⟨e, pr, bs, visit_ticks p (word i) mem⟩
      · exact costs z h

/-- Exact execution, dense row contents, frame, and costs of one shrink gather pass. -/
structure Gathered (B Q : ℕ) (p : Fin 6 → Word w) (cap : ℕ) (ref : Memory w) (rs : List (Report w)) : Prop where
  run : runSegment (program p) cap (some 0) ref (List.replicate (B*Q) []) = some rs
  endCursor : endState (some 0) rs = some (Fin.ofNat (2^w) (B*Q))
  readAB : ∀ b < B, ∀ r < Q, after ref (eventLog rs) ((p 5).val+2*(b*Q+r)) =
    ref ((p 3).val+b*(p 1).val+r)
  readCD : ∀ b < B, ∀ r < Q, after ref (eventLog rs) ((p 5).val+2*(b*Q+r)+1) =
    ref ((p 4).val+b*(p 2).val+r)
  frame : ∀ a, a < (p 5).val ∨ (p 5).val+2*(B*Q) ≤ a → after ref (eventLog rs) a = ref a
  count : rs.length = B*Q
  perCall : ∀ r ∈ rs, r.events.length = cost ∧ countProbes r.events = 4 ∧
    choiceBits r.events = [] ∧ r.events.count .tick = 20
  events : (eventLog rs).length = cost*(B*Q)
  probes : countProbes (eventLog rs) = 4*(B*Q)
  ticks : (eventLog rs).count .tick = 20*(B*Q)

private theorem total (rs : List (Report w)) (h : ∀ r ∈ rs, SiteCost r) :
    (eventLog rs).length = cost*rs.length ∧ countProbes (eventLog rs) = 4*rs.length ∧
      (eventLog rs).count .tick = 20*rs.length := by
  induction rs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons r rs ih =>
    obtain ⟨le, pr, _, ticks⟩ := h r List.mem_cons_self
    obtain ⟨ls, ps, ts⟩ := ih fun z hz => h z (List.mem_cons_of_mem r hz)
    change (r.events ++ eventLog rs).length = _ ∧ countProbes (r.events ++ eventLog rs) = _ ∧
      (r.events ++ eventLog rs).count .tick = _
    rw [List.length_append, Greedy.probes_append, List.count_append, le, pr, ticks, ls, ps, ts,
      List.length_cons]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- The scan reads the original source cell at every bundle and rank, even
when earlier rows have already been written to dense memory. -/
theorem gather (L : Layout B Q p) (ref : Memory w) {cap : ℕ} (hcap : cost < cap) :
    ∃ rs, Gathered B Q p cap ref rs := by
  have start : Prefix p Q 0 ref ref := ⟨fun _ h => by omega, fun _ _ => rfl⟩
  obtain ⟨rs, run, stop, state, len, costs⟩ := segment L hcap start (B*Q) (by omega)
  simp only [Nat.zero_add] at stop state
  have row {b r : ℕ} (hb : b<B) (hr : r<Q) := state.rows _ (packed_lt hb hr)
  have decode {b r : ℕ} (hr : r<Q) (s a : Fin 6) : sourceCell p Q (b*Q+r) s a = (p a).val+b*(p s).val+r := by
    have hdiv : (b*Q+r)/Q = b := by rw [Nat.mul_comm b, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    rw [sourceCell, hdiv, Nat.mul_add_mod_of_lt hr]
  obtain ⟨le, pr, ticks⟩ := total rs costs
  rw [len] at le pr ticks
  refine ⟨rs, run, stop, ?_, ?_, state.frame, len, costs, le, pr, ticks⟩
  · intro b hb r hr
    simpa only [decode hr] using (row hb hr).1
  · intro b hb r hr
    simpa only [decode hr] using (row hb hr).2

end CompressorRecords.ShrinkDemandGather

end VPVNP
end Computability
end OAI
