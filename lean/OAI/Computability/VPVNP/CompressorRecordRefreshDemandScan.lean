import OAI.Computability.VPVNP.CompressorRecordRefreshNewSlots
import OAI.Computability.VPVNP.DegreeRefreshPass
import OAI.Computability.VPVNP.CompressorChoicePreparation

/-!
# Dense demand vectors for the degree-refresh term reader

For each ordered tie, one native pass visits the old base vertex and residual
lane of every block. The selected segment column supplies the outgoing or
incoming width at that tie's local half-slot. The resulting contiguous array
is the input used by the motif term verifier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.DemandScan

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM NewSlots
open Compression Compression.Refresh Compression.DegreeRefresh

variable {w N t : ℕ}
/-- Eight public words that specify a tie's ports, the block dimensions, the selected width
column, and the dense demand destination. -/
abbrev Params (w : ℕ) := Fin 8 → W w

/-- Public words are the residual lane count, port count, target port, source
port, tie count, tie index, selected width-column base and dense output base. -/
def visit : List (Op 9 8) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 4 1, .binary .mul 2 2 4, .publicWord 5 2, .binary .add 2 2 5,
   .binary .mul 2 2 1, .binary .add 2 2 3, .binary .mul 2 2 4,
   .publicWord 5 3, .binary .add 2 2 5, .publicWord 6 6, .binary .add 2 6 2, .read 7 2,
   .publicWord 4 4, .binary .mul 3 0 4, .publicWord 5 5, .binary .add 3 3 5,
   .publicWord 6 7, .binary .add 3 6 3, .write 3 7, .constant 8 1, .binary .add 0 0 8]

/-- Address of the selected segment width for the block and ordered tie being scanned. -/
def inputAddr (p : Params w) (i : W w) : W w :=
  let v := BinaryOp.div.eval i (p 0)
  let l := BinaryOp.mod.eval i (p 0)
  p 6 + (((v * p 1 + p 2) * p 0 + l) * p 1 + p 3)

/-- Address of one demand entry, indexed first by block ordinal and then by tie ordinal. -/
def outputAddr (p : Params w) (i : W w) : W w := p 7 + (i * p 4 + p 5)

/-- The 25 events that read a selected width and write it into the block's dense demand vector. -/
def events (p : Params w) (m : Memory w) (i : W w) : List (Event w) :=
  let v := m (inputAddr p i).val
  List.replicate 15 .tick ++ [.read (inputAddr p i) v] ++ List.replicate 6 .tick ++
    [.write (outputAddr p i) v, .tick, .tick]

theorem work (p : Params w) (m : Memory w) (i : W w) :
    (events p m i).length = 25 ∧ countProbes (events p m i) = 2 := by simp [events,countProbes]

theorem after_events (p : Params w) (m : Memory w) (i : W w) :
    after m (events p m i) = writeMemory m (outputAddr p i) (m (inputAddr p i).val) := rfl

set_option maxRecDepth 4096 in
private theorem visit_trace (p : Params w) (m : Memory w) (i : W w) (r : Regs w 9) :
    ∃ s, trace p i visit r m = some (events p m i, s, writeMemory m (outputAddr p i) (m (inputAddr p i).val)) ∧
      s 0 = i+1 := by
  simp (config := {decide := true}) [visit,events,inputAddr,outputAddr,trace,Op.effect,BinaryOp.eval,Function.update]
  rfl

theorem native (p : Params w) (m : Memory w) (i : W w) :
    let M := (template visit 0).instantiate w p
    execute M.program 26 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  obtain ⟨rs,ht,hr⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1+visit.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace,ht]
  simp [hr]

/-- The actual lists of native calls, in tie order and then block order. -/
inductive Runs (p : Fin t → Params w) (N : ℕ) : List (Fin t) → Memory w → List (Report w) → Prop where
  | nil (m) : Runs p N [] m []
  | cons (k : Fin t) {ks m rs ts}
      (head : let M := (template visit 0).instantiate w (p k)
        runSegment M.program 26 (some 0) m (List.replicate N []) = some rs)
      (tail : Runs p N ks (after m (eventLog rs)) ts) : Runs p N (k :: ks) m (rs ++ ts)

variable (p : Fin t → Params w) (ref : Memory w)

/-- Source width address for one tie pass and one finite block index. -/
def src (k : Fin t) (i : Fin N) := inputAddr (p k) (word i.val)
/-- Destination demand address for the same tie pass and block index. -/
def dst (k : Fin t) (i : Fin N) := outputAddr (p k) (word i.val)

/-- Source widths avoid every demand write, and the destination address determines the tie and
block uniquely. -/
structure Layout (N : ℕ) : Prop where
  reads : ∀ k j (i l : Fin N), src p k i ≠ dst p j l
  writes : ∀ k j (i l : Fin N), dst p k i = dst p j l → k = j ∧ i = l

/-- Completed cells for the passes preceding the current tie and the visited
block prefix of the current tie. Outside this set the initial memory is intact. -/
structure Saved (ref m : Memory w) (done : Fin t → Fin N → Prop) : Prop where
  rows : ∀ k i, done k i → m (dst p k i).val = ref (src p k i).val
  frame : ∀ addr, (∀ k i, done k i → addr ≠ (dst p k i).val) → m addr = ref addr

private theorem one_step (layout : Layout p N) (m : Memory w) {done : Fin t → Fin N → Prop}
    (prev : Saved p ref m done) (j : Fin t) (l : Fin N) :
    Saved p ref (after m (events (p j) m (word l.val))) (fun k i => done k i ∨ k = j ∧ i = l) := by
  rw [after_events]
  have live : m (src p j l).val = ref (src p j l).val :=
    prev.frame _ (fun k i _ he => layout.reads j k l i (Fin.ext he))
  constructor
  · intro k i hk
    change writeMemory m (dst p j l) (m (src p j l).val) (dst p k i).val = _
    by_cases he : dst p k i = dst p j l
    · obtain ⟨rfl,rfl⟩ := layout.writes k j i l he
      simpa [writeMemory] using live
    · have hn := Fin.val_ne_of_ne he
      simp only [writeMemory,ite_eq_right hn]
      exact prev.rows k i (hk.resolve_right (fun ⟨h,h'⟩ => he (h ▸ h' ▸ rfl)))
  · intro addr outside
    change writeMemory m (dst p j l) _ addr = _
    rw [writeMemory,ite_eq_right (outside j l (.inr ⟨rfl,rfl⟩))]
    exact prev.frame addr (fun k i h => outside k i (.inl h))

private theorem saved_congr {m : Memory w} {f g : Fin t → Fin N → Prop}
    (h : Saved p ref m f) (eq : ∀ k i, f k i ↔ g k i) : Saved p ref m g :=
  ⟨fun k i hi => h.rows k i ((eq k i).mpr hi), fun addr ha => h.frame addr (fun k i hi => ha k i ((eq k i).mp hi))⟩

/-- One tie's scan, retaining all earlier writes and every unvisited cell. -/
theorem scan_run (layout : Layout p N) (done : Fin t → Fin N → Prop) (j : Fin t)
    (m : Memory w) (k calls : ℕ) (room : k+calls ≤ N)
    (prev : Saved p ref m (fun u i => done u i ∨ u = j ∧ i.val < k)) :
    let M := (template visit 0).instantiate w (p j)
    ∃ rs, runSegment M.program 26 (some (word k)) m (List.replicate calls []) = some rs ∧
      Saved p ref (after m (eventLog rs)) (fun u i => done u i ∨ u = j ∧ i.val < k+calls) ∧
      RAMBuckets.cost Report.probes rs = 3*calls := by
  let M := (template visit 0).instantiate w (p j)
  induction calls generalizing m k with
  | zero => exact ⟨[],rfl,prev,rfl⟩
  | succ n ih =>
    let l : Fin N := ⟨k,by omega⟩
    let b := word (bits := w) k
    let r : Report w := ⟨events (p j) m b,some (b+1)⟩
    let next := after m r.events
    have hprev : Saved p ref next (fun u i => done u i ∨ u=j ∧ i.val<k+1) := by
      apply saved_congr p ref (one_step p ref layout m prev j l)
      intro u i
      have hi : i=l ↔ i.val=k := Fin.ext_iff
      have lt : i.val<k+1 ↔ i.val<k ∨ i.val=k := by omega
      change _ ↔ done u i ∨ u=j ∧ i.val<k+1
      rw [hi,lt]; tauto
    obtain ⟨ts,hr,hs,hc⟩ := ih next (k+1) (by omega) hprev
    have inc : b+1 = word (bits := w) (k+1) := Fin.ext (by simp [b,word,Fin.val_add,Nat.add_mod_mod])
    have hm : after m (eventLog (r :: ts)) = after next (eventLog ts) := by
      change List.foldl BurstRAM.update m (r.events ++ eventLog ts) = _
      rw [List.foldl_append]; rfl
    refine ⟨r::ts,?_,?_,?_⟩
    · change runSegment M.program 26 (some b) m (List.replicate (n+1) []) = _
      rw [List.replicate_succ,runSegment,native]
      simp only [M,r,next,inc,hr,Option.map_some]
    · simpa only [hm,Nat.add_assoc,Nat.add_comm 1 n] using hs
    · have hp : r.probes = 2 := (work (p j) m b).2
      rw [RAMBuckets.cost,hp,hc]; omega

/-- All tie scans share the same memory and source tables. -/
theorem scans (layout : Layout p N) (ks : List (Fin t)) (m : Memory w) (done : Fin t → Fin N → Prop)
    (prev : Saved p ref m done) :
    ∃ rs, Runs p N ks m rs ∧ Saved p ref (after m (eventLog rs)) (fun k i => done k i ∨ k ∈ ks) ∧
      RAMBuckets.cost Report.probes rs = 3*N*ks.length := by
  induction ks generalizing m done with
  | nil => exact ⟨[],.nil _,saved_congr p ref prev (by simp),by simp [RAMBuckets.cost]⟩
  | cons j ks ih =>
    have start : Saved p ref m (fun u i => done u i ∨ u = j ∧ i.val < 0) :=
      saved_congr p ref prev (by simp)
    obtain ⟨rs,hr,hs,hc⟩ := scan_run p ref layout done j m 0 N (by simp) start
    let mid := after m (eventLog rs)
    have saved : Saved p ref mid (fun u i => done u i ∨ u=j) := saved_congr p ref hs (by simp)
    obtain ⟨ts,ht,hf,hw⟩ := ih mid _ saved
    have hm : after m (eventLog (rs++ts)) = after mid (eventLog ts) := by
      change List.foldl BurstRAM.update m ((rs++ts).flatMap Report.events) = _
      rw [List.flatMap_append,List.foldl_append]; rfl
    have zero : word (bits := w) 0 = 0 := Fin.ext (by simp [word])
    rw [zero] at hr
    refine ⟨rs++ts,.cons j hr ht,?_,?_⟩
    · rw [hm]; exact saved_congr p ref hf (by simp [or_assoc])
    · rw [RAMBuckets.cost_append,hc,hw,List.length_cons,Nat.mul_succ]; omega

/-- One public table for each fixed role of the motif. -/
def words {D r t : ℕ} (ties : Fin t ≃ Tie D) (q : Fin 8 → W w) (out : W w)
    (k : Fin t) : Params w :=
  ![word r, word D, word (tieTarget (ties k)).val, word (tieSource (ties k)).val,
    word t, word k.val, if (ties k).1 then q 1 else q 7, out]

private theorem pack_lt {q Q i d : ℕ} (hq : q<Q) (hi : i<d) : q*d+i < Q*d :=
  calc q*d+i < q*d+d := Nat.add_lt_add_left hi _
       _ = (q+1)*d := (Nat.succ_mul ..).symm
       _ ≤ Q*d := Nat.mul_le_mul_right d hq

private theorem add_word (a b : ℕ) : word a + word b = word (bits := w) (a+b) :=
  Fin.ext (Nat.add_mod a b _).symm

private theorem mul_word (a b : ℕ) : word a * word b = word (bits := w) (a*b) :=
  Fin.ext (Nat.mul_mod a b _).symm

section Graph

variable {a g : ℕ} (X : State a (a+g)) (ties : Fin t ≃ Tie (2^a))
  (q : Fin 8 → W w) (out : W w)

local notation "B" => (Fintype.card X.Base * 2^g)
local notation "S" => (Fintype.card X.Base * 2^a * 2^g * 2^a)
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "P" => words (r := 2^g) ties q out

/-- Enumerate blocks by old base vertex and residual lane, with the residual lane varying
fastest. -/
def blocks : X.Base × BitWord g ≃ Fin B :=
  (X.baseIndex.prodCongr (bitWordFinEquiv g)).trans finProdFinEquiv

theorem blocks_val (s : X.Base × BitWord g) :
    (blocks X s).val = (X.baseIndex s.1).val * 2^g + (bitWordFinEquiv g s.2).val := by
  change (bitWordFinEquiv g s.2).val + 2^g * (X.baseIndex s.1).val = _
  ring

private def halfSlot (s : X.Base × BitWord g) (e : Tie (2^a)) : DyadicArc X.Base (BitWord g) a :=
  ((s,tieTarget e),tieSource e)

private theorem source_key (s : X.Base × BitWord g) (e : Tie (2^a)) :
    (numbered O (halfSlot X s e)).val =
      (((X.baseIndex s.1).val * 2^a + (tieTarget e).val) * 2^g +
        (bitWordFinEquiv g s.2).val) * 2^a + (tieSource e).val := by
  rw [halfSlot,numbered_val,sites_val]

private theorem src_eq (fit : S ≤ 2^w) (laneFit : 2^g < 2^w) (k : Fin t) (s : X.Base × BitWord g) :
    src P k (blocks X s) =
      (if (ties k).1 then q 1 else q 7) + idWord O fit (halfSlot X s (ties k)) := by
  have boundB : B ≤ S := by
    calc B ≤ B * (2^a * 2^a) := Nat.le_mul_of_pos_right _ (by positivity)
         _ = S := by ring
  have hval : (word (bits := w) (blocks X s).val).val =
      (X.baseIndex s.1).val * 2^g + (bitWordFinEquiv g s.2).val :=
    (Nat.mod_eq_of_lt ((blocks X s).isLt.trans_le (boundB.trans fit))).trans (blocks_val X s)
  have hr : (word (bits := w) (2^g)).val = 2^g := Nat.mod_eq_of_lt laneFit
  have hv : BinaryOp.div.eval (word (bits := w) (blocks X s).val) (word (2^g)) = word (X.baseIndex s.1).val := by
    apply Fin.ext
    change ((_ : W w).val / (_ : W w).val) % _ = _ % _
    rw [hval,hr,Nat.mul_comm (X.baseIndex s.1).val,Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (bitWordFinEquiv g s.2).isLt,Nat.add_zero]
  have hl : BinaryOp.mod.eval (word (bits := w) (blocks X s).val) (word (2^g)) = word (bitWordFinEquiv g s.2).val := by
    apply Fin.ext
    change ((_ : W w).val % (_ : W w).val) % _ = _ % _
    rw [hval,hr,Nat.mul_add_mod_of_lt (bitWordFinEquiv g s.2).isLt]
  change (if (ties k).1 then q 1 else q 7) + (((BinaryOp.div.eval _ (word (2^g)) * word (2^a) + word (tieTarget (ties k)).val) * word (2^g) +
    BinaryOp.mod.eval _ (word (2^g))) * word (2^a) + word (tieSource (ties k)).val) = _
  rw [hv,hl,mul_word,add_word,mul_word,add_word,mul_word,add_word,← source_key X s (ties k)]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt (idWord O fit (halfSlot X s (ties k))).isLt)

private theorem dst_eq (i : Fin B) (k : Fin t) : dst P k i = out + word (i.val*t+k.val) := by
  change out + (word i.val * word t + word k.val) = _
  rw [mul_word,add_word]

private theorem dst_val (room : out.val+B*t ≤ 2^w) (i : Fin B) (k : Fin t) :
    (dst P k i).val = out.val + i.val*t + k.val := by
  rw [dst_eq X ties q out i k,Fin.val_add]
  have h := pack_lt i.isLt k.isLt
  change (out.val + ((i.val*t+k.val) % (2^w))) % (2^w) = _
  rw [Nat.mod_eq_of_lt (by omega : i.val*t+k.val < 2^w),Nat.mod_eq_of_lt (by omega),Nat.add_assoc]

/-- The source columns are disjoint from the dense output interval. -/
def Apart : Prop :=
  ∀ c : Fin 8, c = 1 ∨ c = 7 → ∀ i : W w, i.val < S →
    (q c+i).val < out.val ∨ out.val+B*t ≤ (q c+i).val

private theorem layout (fit : S ≤ 2^w) (laneFit : 2^g < 2^w)
    (room : out.val+B*t ≤ 2^w) (apart : Apart (t := t) X q out) : Layout P B := by
  constructor
  · intro k j i l he
    let s := (blocks X).symm i
    have hi : i = blocks X s := ((blocks X).apply_symm_apply i).symm
    have hsrc := src_eq X ties q out fit laneFit k s
    rw [← hi] at hsrc
    have hrange := dst_val X ties q out room l j
    let z := idWord O fit (halfSlot X s (ties k))
    have hz : z.val < S := (numbered O (halfSlot X s (ties k))).isLt
    have choose : (src P k i).val < out.val ∨ out.val+B*t ≤ (src P k i).val := by
      rw [hsrc]
      cases h : (ties k).1 with
      | false => exact apart 7 (.inr rfl) z hz
      | true => exact apart 1 (.inl rfl) z hz
    rw [he,hrange] at choose
    have := pack_lt l.isLt j.isLt
    omega
  · intro k j i l he
    have h := congrArg Fin.val he
    rw [dst_val X ties q out room i k,dst_val X ties q out room l j] at h
    have key : i.val*t+k.val = l.val*t+j.val := by omega
    have hkj : k=j := Fin.ext ((Nat.mul_add_mod_of_lt k.isLt).symm.trans
      ((congrArg (· % t) key).trans (Nat.mul_add_mod_of_lt j.isLt)))
    subst j
    exact ⟨rfl,Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt k.isLt) (Nat.add_right_cancel key))⟩

/-- Recover the exact tie width from the completed external segment pass. At an
incoming half-slot, its own destination identifier is the incoming-width key. -/
theorem read_demand (fit : S ≤ 2^w) (laneFit : 2^g < 2^w)
    (data : RefreshRAM.Input w) (dir : Directory (splitSlots X) O (splitWidths X) q data fit)
    (done : RefreshRAM.AtCursor q S data ref S)
    (inc : ∀ e : DyadicArc X.Base (BitWord g) a,
      (RefreshRAM.cell q ref 7 (idWord O fit (oldPortMatching (splitSlots X) (bitWordFinEquiv a) e))).val =
        (outgoingRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) e).width)
    (k : Fin t) (s : X.Base × BitWord g) :
    (ref (src P k (blocks X s)).val).val =
      blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s (ties k) := by
  rw [src_eq X ties q out fit laneFit k s]
  let e := halfSlot X s (ties k)
  let perm := oldPortMatching (splitSlots X) (bitWordFinEquiv a)
  change (ref ((if (ties k).1 then q 1 else q 7) + idWord O fit e).val).val =
    internalWidth perm (groupedWidths (bitWordFinEquiv a) (splitWidths X)) s (ties k)
  cases h : (ties k).1 with
  | true =>
    simp [h,internalWidth]
    exact (congrArg Fin.val (done.old (idWord O fit e) (numbered O e).isLt)).trans (dir.old e)
  | false =>
    have hr := inc (perm.symm e)
    change (RefreshRAM.cell q ref 7 (idWord O fit (perm (perm.symm e)))).val = _ at hr
    rw [Equiv.apply_symm_apply] at hr
    simp [h,internalWidth]
    exact hr

/-- Base address handed to the term verifier for this block. -/
def rowBase (t : ℕ) (out : W w) (s : X.Base × BitWord g) : W w :=
  out + word ((blocks X s).val*t)

theorem rowBase_fits (room : out.val+B*t ≤ 2^w) (s : X.Base × BitWord g) :
    (rowBase X t out s).val + t ≤ 2^w := by
  have h : ((blocks X s).val+1)*t ≤ B*t := Nat.mul_le_mul_right _ (blocks X s).isLt
  rw [Nat.succ_mul] at h
  rw [rowBase,Fin.val_add]
  change (out.val + ((blocks X s).val*t) % 2^w) % 2^w + t ≤ _
  have := Nat.mod_le ((blocks X s).val*t) (2^w)
  have := Nat.mod_le (out.val + ((blocks X s).val*t) % 2^w) (2^w)
  omega

/-- Execute all fixed tie scans from the terminal segment directory. The
motif verifier reads exactly the graph's demand function at each row base.
The cost is three calls-plus-probes per pair of a block and a tie. -/
theorem demand_table (fit : S ≤ 2^w) (laneFit : 2^g < 2^w) (room : out.val+B*t ≤ 2^w)
    (apart : Apart (t := t) X q out)
    (data : RefreshRAM.Input w) (dir : Directory (splitSlots X) O (splitWidths X) q data fit)
    (done : RefreshRAM.AtCursor q S data ref S)
    (inc : ∀ e : DyadicArc X.Base (BitWord g) a,
      (RefreshRAM.cell q ref 7 (idWord O fit (oldPortMatching (splitSlots X) (bitWordFinEquiv a) e))).val =
        (outgoingRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) e).width) :
    ∃ rs, Runs P B (List.finRange t) ref rs ∧
      (∀ s, DemandPreparation.demandAt ties (rowBase X t out s) (after ref (eventLog rs)) =
        blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s) ∧
      (∀ addr, addr < out.val ∨ out.val+B*t ≤ addr → after ref (eventLog rs) addr = ref addr) ∧
      RAMBuckets.cost Report.probes rs = 3*B*t := by
  have lay := layout X ties q out fit laneFit room apart
  obtain ⟨rs,run,saved,cost⟩ := scans P ref lay (List.finRange t) ref (fun _ _ => False)
    ⟨fun _ _ h => h.elim, fun _ _ => rfl⟩
  refine ⟨rs,run,?_,?_,by simpa using cost⟩
  · intro s
    funext e
    obtain ⟨k,rfl⟩ := ties.surjective e
    have hrow := saved.rows k (blocks X s) (.inr (List.mem_finRange k))
    have val := (congrArg Fin.val hrow).trans (read_demand ref X ties q out fit laneFit data dir done inc k s)
    rw [dst_eq X ties q out (blocks X s) k] at val
    change ((after ref (eventLog rs)) ((out + word ((blocks X s).val*t)) +
      word (ties.symm (ties k)).val).val).val = _
    rw [Equiv.symm_apply_apply,add_assoc,add_word]
    exact val
  · intro addr outside
    apply saved.frame
    intro k i _
    rw [dst_val X ties q out room i k]
    have := pack_lt i.isLt k.isLt
    omega

end Graph

end CompressorRecords.PortRefresh.DemandScan

end VPVNP
end Computability
end OAI
