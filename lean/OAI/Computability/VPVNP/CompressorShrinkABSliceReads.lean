import OAI.Computability.VPVNP.CompressorShrinkABSliceVisits
import OAI.Computability.VPVNP.CompressorSourceOnline

/-!
# External reads of a whole-level AB slice visit

Clear reads no cell. Pair tests read the two width and two start columns.
Incidence reads the frame length and at most two counts in the current
bundle's bank. These bounds hold even for arbitrary contents of those
cells. The global-row prologue consists entirely of private operations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport IndexedStarts ShrinkABSliceTable SliceRAM
open scoped Fin.CommRing

variable {w m n rows first : ℕ} {data : ℕ → Prop}

open private execute_reads execute_stores reads wordStores from OAI.Computability.VPVNP.CompressorSlicePairVisit
open private appendEvents from OAI.Computability.VPVNP.CompressorSliceAdjacencyNative
open private adj_vals adj_space from OAI.Computability.VPVNP.CompressorSliceIndexedStarts
open private indices_lt from OAI.Computability.VPVNP.CompressorSliceSchedule

private theorem pair_log (p : Fin 6 → Word w) (id : Word w) (mem : Memory w)
    (ok : data (p 1+IndexedPair.oldIndex p id).val ∧ data (p 2+IndexedPair.oldIndex p id).val ∧
      data (p 3+IndexedPair.newIndex p id).val ∧ data (p 4+IndexedPair.newIndex p id).val) :
    let M := IndexedPair.table.instantiate w p
    ∃ r, execute M.program 38 (M.program.start id) mem [] = some r ∧ r.result.isSome ∧ Reads data r.events := by
  intro M
  change ∃ r, execute (IndexedPair.table.instantiate w p).program 38 _ _ _ = some r ∧ _
  rw [execute_reads p id mem 14,execute_stores p id mem _ rfl rfl]
  refine ⟨_,rfl,rfl,?_⟩
  intro a v h
  change Event.read a v ∈ reads p id mem ++ wordStores _ _ _ _ _ at h
  rcases List.mem_append.mp h with rd|wr
  · simp [reads] at rd
    rcases rd with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
    exacts [ok.1,ok.2.1,ok.2.2.1,ok.2.2.2]
  · have noRead (b s t lo hi : Word w) : Event.read a v ∉ wordStores b s t lo hi := by
      by_cases e : lo < hi <;> simp [wordStores,e]
    exact (noRead _ _ _ _ _ wr).elim

private theorem ref_log (q : Fin 7 → Word w) (id : Word w) (mem : Memory w)
    (ok : data (adjFrameLength q id).val ∧ data (adjOldCount q (id/q 0)).val ∧
      data (adjNewCount q (id%q 0)).val) : Reads data (adjEvents q mem id) := by
  intro a v h
  by_cases hz : mem (adjFrameLength q id).val = 0 <;> simp [adjEvents,hz,appendEvents] at h
  · exact h.1.symm ▸ ok.1
  · rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
    exacts [ok.1,ok.2.1,ok.2.2]

private theorem core_log (input : Fin 4 → Word w) (B : Word w) (s : Space input B m n)
    (src : ∀ (c : Fin 4) j, j < (if c.val < 2 then m else n) → data ((input c).val+j))
    (bankOk : ∀ x, B.val ≤ x → x < B.val+capacity m n → data x) (j : Stage m n) (mem : Memory w) :
    let par : Fin j.pass.params → Word w := match j with
      | .clear _ => fun _ => B | .pair _ => IndexedStarts.pair input B m n | .refs _ => adj B m n
    let M := j.pass.table.instantiate w par
    ∃ r, execute M.program j.fuel (M.program.start (j.localIdx : Word w)) mem [] = some r ∧
      r.result.isSome ∧ Reads data r.events := by
  cases j with
  | clear k =>
    exact ⟨_,clearVisit_native B _ _,rfl,fun a v h => by simp [clearReport] at h⟩
  | pair k =>
    let p := IndexedStarts.pair input B m n
    let id : Word w := (k.val : Word w)
    have room := s.fits
    unfold capacity at room
    have hk : id.val = k.val := Nat.mod_eq_of_lt (by have := k.isLt; omega)
    have hn : (p 0).val = n := Nat.mod_eq_of_lt (by omega)
    obtain ⟨old,new⟩ := indices_lt k.isLt
    have lo := (IndexedPair.oldIndex_val p id).trans (by rw [hk,hn])
    have hi := (IndexedPair.newIndex_val p id).trans (by rw [hk,hn])
    have cell (c : Fin 4) (e : Word w) (h : e.val < (if c.val < 2 then m else n)) : data (input c+e).val := by
      have fits := s.reads c
      rw [Fin.val_add,Nat.mod_eq_of_lt (by have := B.isLt; omega)]
      exact src c e.val h
    exact pair_log p id mem ⟨cell 0 _ (lo ▸ old),cell 1 _ (lo ▸ old),cell 2 _ (hi ▸ new),cell 3 _ (hi ▸ new)⟩
  | refs k =>
    let q := adj B m n
    let id : Word w := (k.val : Word w)
    obtain ⟨hn,hm,hf,_,_,hcn,_⟩ := adj_vals s
    have room := s.fits
    unfold capacity at room
    have hk : id.val = k.val := Nat.mod_eq_of_lt (by have := k.isLt; omega)
    have bounded : id.val < (q 1).val*(q 0).val := by rw [hk,hm,hn]; exact k.isLt
    have hf' := adjFrameLength_val (adj_space s) bounded
    obtain ⟨old,new⟩ := indices_lt k.isLt
    have co : (adjOldCount q (id/q 0)).val = B.val+k.val/n := by
      change (B.val+id.val/(q 0).val)%(2^w) = _
      rw [hk,hn,Nat.mod_eq_of_lt (by omega)]
    have cn : (adjNewCount q (id%q 0)).val = B.val+m+k.val%n := by
      change ((q 5).val+id.val%(q 0).val)%(2^w) = _
      rw [hcn,hk,hn,Nat.mod_eq_of_lt (by omega)]
    have klt := k.isLt
    refine ⟨_,adjVisit_native q mem id,rfl,ref_log q id mem ⟨?_,?_,?_⟩⟩
    · rw [hf',hf,hk]; exact bankOk (B.val+m+n+3*k.val+2) (by omega) (by unfold capacity; omega)
    · rw [co]; exact bankOk (B.val+k.val/n) (Nat.le_add_right ..) (by unfold capacity; omega)
    · rw [cn]; exact bankOk (B.val+m+k.val%n) (by omega) (by unfold capacity; omega)

open private stage_flat local_data from OAI.Computability.VPVNP.CompressorShrinkABSliceVisits
open private local_val from OAI.Computability.VPVNP.CompressorShrinkABSliceRecipe

variable (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w)
variable {t p : Fin 5 → Word w} (L : Layout t p rows m n first) (D : Describes I pub state ref t p rows first)

/-- The four physical input rectangles and the interval banks are the only
regions from which this part of the calendar may read. -/
structure ReadRegion (t p : Fin 5 → Word w) (rows m n first : ℕ) (data : ℕ → Prop) : Prop where
  columns : ∀ (i : Fin rows) (c : Fin 4) j, j < (if c.val < 2 then m else n) →
    data (((ShrinkABSliceTable.columns t p i.val) c).val+j)
  bank : ∀ x, first ≤ x → x < first+rows*capacity m n → data x

private theorem noRead {k : ℕ} (a : FlatRows.Public k w) (s : Word w) (mem : Memory w) :
    Reads data (FlatRows.events (fun _ => false) a s mem) := by
  intro x v h
  simp [FlatRows.events,List.mem_flatMap,FlatRows.operandEvents] at h

include L D

private theorem row_log (region : ReadRegion t p rows m n first data)
    (j : Stage m n) (i : Fin rows) (mem : Memory w) (cap : ℕ) (hcap : 95 ≤ cap) :
    let v := stage I j
    let P := (v.worker.table.instantiate w (fun k => (v.params k).eval pub state ref)).program
    ∃ r, execute P cap (P.start (Fin.ofNat _ i.val)) mem [] = some r ∧
      r.result = some (Fin.ofNat _ (i.val+1)) ∧ Reads data r.events := by
  let B := bank (w := w) first m n i.val
  have bounds (x) (lo : B.val ≤ x) (hi : x < B.val+capacity m n) : data x := by
    have hv : B.val = first+i.val*capacity m n := bank_val L i
    have hn := Nat.mul_le_mul_right (capacity m n) i.isLt
    rw [Nat.succ_mul] at hn
    exact region.bank x (by omega) (by omega)
  have source :
      let M := j.pass.table.instantiate w (j.data t p i first)
      ∃ r, execute M.program j.fuel (M.program.start (j.localIdx : Word w)) mem [] = some r ∧
        r.result.isSome ∧ Reads data r.events := by
    cases j <;> apply core_log (columns t p i.val) B (space L i) (region.columns i) bounds _ mem
  obtain ⟨r,run,ret,rd⟩ := source
  rw [stage_flat]
  let args := evaluated pub state ref (j.affineParams I) j.localIdx
  let s : Word w := i.val
  let P := ((FlatRows.compile j.pass.table (fun _ => false)).instantiate w args).program
  have exe := FlatRows.execute_flat j.pass.table (fun _ => false) args s mem [] j.fuel
  dsimp only at exe
  rw [local_data I pub state ref L D j i mem,local_val pub state ref (j.affineParams I) j.localIdx s mem,
    run,Option.map_some] at exe
  have lim : j.fuel+(3+7*(j.pass.params+1)) ≤ cap := by cases j <;> dsimp [Stage.fuel,Stage.pass] <;> omega
  have ok := execute_extend exe (cap-(j.fuel+(3+7*(j.pass.params+1))))
  rw [Nat.add_sub_of_le lim] at ok
  refine ⟨_,ok,?_,?_⟩
  · have hx : r.result.map (fun _ => s+1) = some (s+1) := by
      cases h : r.result <;> simp [h] at ret ⊢
    apply hx.trans
    change some ((i.val : Word w)+1) = some ((i.val+1 : ℕ) : Word w)
    push_cast; rfl
  · intro x v h
    rcases List.mem_append.mp h with h|h
    · exact noRead args s mem x v h
    · exact rd x v h

/-- The real global-bundle cursor advances from zero to the planned stop.
Its emitted events read only the actual columns and bank rectangles. -/
theorem source_progress_reads (region : ReadRegion t p rows m n first data) (limit : rows < 2^w)
    (j : Stage m n) (cap : ℕ) (hcap : 95 ≤ cap) (mem : Memory w) (rs : List (Report w))
    (src : Source I pub state ref rows cap j mem rs) :
    SourceOnline.Progress (Fin.ofNat _ rows) 0 rs ∧ Reads data (eventLog rs) := by
  let v := stage I j
  let P := (v.worker.table.instantiate w (fun k => (v.params k).eval pub state ref)).program
  have loop (k len : ℕ) (span : k+len = rows) (s : Memory w) (xs : List (Report w))
      (h : runSegment P cap (some (Fin.ofNat _ k)) s (List.replicate len []) = some xs) :
      SourceOnline.Progress (Fin.ofNat _ rows) (Fin.ofNat _ k) xs ∧ Reads data (eventLog xs) := by
    induction len generalizing k s xs with
    | zero =>
      obtain rfl := (Option.some.inj h).symm
      exact ⟨.done (by simp_all),fun _ _ h => by simp [eventLog] at h⟩
    | succ len ih =>
      let i : Fin rows := ⟨k,by omega⟩
      obtain ⟨r,exec,ret,rd⟩ := row_log I pub state ref L D region j i s cap hcap
      change execute P cap (P.start (Fin.ofNat _ k)) s [] = some r at exec
      simp only [List.replicate_succ,runSegment,exec,ret] at h
      obtain ⟨more,tail,rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨progress,reads⟩ := ih (k+1) (by omega) _ _ tail
      have live : Fin.ofNat (2^w) k < Fin.ofNat _ rows := by
        change k%(2^w) < rows%(2^w)
        rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt limit]; omega
      refine ⟨.next live ret progress,fun x v h => ?_⟩
      rcases List.mem_append.mp h with hr|ht
      · exact rd x v hr
      · exact reads x v ht
  exact loop 0 rows (Nat.zero_add _) mem rs src

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI
