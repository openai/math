import OAI.Computability.VPVNP.CompressorTermWorkerScan
import OAI.Computability.VPVNP.CompressorDemandFootprint
import OAI.Computability.VPVNP.CompressorPayloadFootprint
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint

/-!
# External addresses accessed by a native term-worker pass

The two demand scans use the current input row. The payload reader probes the
repetition count just stored in the second descriptor header. All stores land
in the current descriptor. These event-level bounds let the same choices run
after a change to the scheduler's control memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker.Footprint

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter SourceTransport
open MotifGrid MotifBlocks MotifConversion MotifSelector TermRecordScan
open scoped Fin.CommRing
open private addr_words grid_words rep_words payload_words prelude_exec fixedPrefix head_left head_rep
  payload_head outRange from OAI.Computability.VPVNP.CompressorTermWorker
open private gridCode gridWords payloadCode payloadWords from OAI.Computability.VPVNP.CompressorTermWorkerRun

variable {w d n g r k : ℕ}

private abbrev Bounds (rd wr : ℕ → Prop) (es : List (Event w)) := Reads rd es ∧ Writes wr es

private theorem append {rd wr : ℕ → Prop} {es fs : List (Event w)} (h : Bounds rd wr es)
    (h' : Bounds rd wr fs) : Bounds rd wr (es ++ fs) :=
  ⟨fun a v hv => (List.mem_append.mp hv).elim (h.1 a v) (h'.1 a v),
   fun a v hv => (List.mem_append.mp hv).elim (h.2 a v) (h'.2 a v)⟩

private theorem store {rd wr : ℕ → Prop} {a v : BurstRAM.Word w} (ha : wr a.val) :
    Bounds rd wr [.write a v] := by
  constructor <;> intro x y hx <;> simp only [List.mem_singleton,reduceCtorEq,Event.write.injEq] at hx
  obtain ⟨rfl,rfl⟩ := hx
  exact ha

private theorem header {G : Flow 8 g} {R : Flow 8 r} (n : ℕ) (addr : Fin 4 → BurstRAM.Word w)
    (x : Fin g → BurstRAM.Word w) (y : Fin r → BurstRAM.Word w) (z : Fin k → BurstRAM.Word w)
    (j : BurstRAM.Word w) {m es out last} {rd wr : ℕ → Prop}
    (grid : ∀ {rs mem gs reg post}, Flow.Exec x (source addr j) G rs mem gs reg post → Bounds rd wr gs)
    (reps : ∀ {rs mem fs reg post}, Flow.Exec y (source addr j) R rs mem fs reg post → Bounds rd wr fs)
    (first : wr (base addr j).val) (second : wr (base addr j+1).val)
    (run : Flow.Exec (words addr x y z) j (headerCode n G R k) (fun _ => 0) m es out last) :
    Bounds rd wr es ∧ out (headReg n 4) = base addr j+2 ∧ out (headReg n 5) = j+1 := by
  cases run with | seq pre rest =>
  cases rest with | seq search rest =>
  cases rest with | seq save rest =>
  cases rest with | seq repeatRow saveCount =>
  let pub := words addr x y z
  obtain ⟨h,hpre,hs,hd,h1,h2,hn⟩ := prelude_exec addr j m
  have hp := (PrimedCounter.restrictExec (headReg n) addrPort pub prelude pre).1
  rw [show pub ∘ addrPort = addr from addr_words ..] at hp
  obtain ⟨e,bank,_⟩ := fixedPrefix hpre (by simp [choiceBits,List.replicate_succ]) hp
  have H i := congrFun bank i
  simp only [Function.comp_apply] at H
  have ga (i : Fin 7) : headReg n i ∉ Set.range (gridReg n) := outRange fun _ => head_left
  have ra (i : Fin 7) : headReg n i ∉ Set.range (repReg n) := outRange fun _ => head_rep
  obtain ⟨hg,ag⟩ := Rebased.restrictExec (gridReg n) gridPort (headReg n 1) (ga 1) pub G search
  have gH i := (ag _ (ga i)).trans (H i)
  rw [show pub ∘ gridPort = x from grid_words ..,(H 1).trans hs] at hg
  cases save with | line he =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  obtain ⟨hr,ar⟩ := Rebased.restrictExec (repReg n) repPort (headReg n 1) (ra 1) pub R repeatRow
  have rH i := (ar _ (ra i)).trans (gH i)
  rw [show pub ∘ repPort = y from rep_words ..,(gH 1).trans hs] at hr
  cases saveCount with | line he =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  refine ⟨append ?_ (append (grid hg) (append (store ?_) (append (reps hr) (store ?_)))),
    (rH 4).trans h2,(rH 5).trans hn⟩
  · rw [e]
    exact FlowFootprint.bounds_of_noProbes _ _ (by rfl)
  · rwa [(gH 2).trans hd]
  · rwa [(rH 3).trans h1]

variable {K : Type*} [Field K] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock K a b P (realWidths p) (realWidths q) H H')
variable (order : Fin d ≃ D) (supply : Fin n ≃ S)

private theorem flow (addr : Fin 4 → BurstRAM.Word w) (j : BurstRAM.Word w) {mem es out last}
    (hsrc : (source addr j).val+d ≤ 2^w) (hdst : (base addr j).val+2+n < 2^w)
    (run : Flow.Exec (motifData B order supply w addr) j
      (code (gridCode B order) (DemandPreparation.repetitionCall d) (payloadCode B n))
      (fun _ => 0) mem es out last) :
    out (headReg n 5) = j+1 ∧
    Bounds (fun i => ((source addr j).val ≤ i ∧ i < (source addr j).val+d) ∨ i = (base addr j).val+1)
      (fun i => (base addr j).val ≤ i ∧ i < (base addr j).val+2+n) es := by
  let src := source addr j
  let dst := base addr j
  let rd := fun i => (src.val ≤ i ∧ i < src.val+d) ∨ i = dst.val+1
  let wr := fun i => dst.val ≤ i ∧ i < dst.val+2+n
  have dfit : dst.val+2+n < 2^w := hdst
  have addOne : (dst+1).val = dst.val+1 := by
    have one : 1 < 2^w := by omega
    rw [Fin.val_add,show (1 : BurstRAM.Word w).val = 1 from Nat.mod_eq_of_lt one,Nat.mod_eq_of_lt (by omega)]
  have addTwo : (dst+2).val = dst.val+2 := by
    have two : 2 < 2^w := by omega
    rw [Fin.val_add,show (2 : BurstRAM.Word w).val = 2 from Nat.mod_eq_of_lt two,Nat.mod_eq_of_lt (by omega)]
  have narrow {fs : List (Event w)} (h : DemandFootprint.Footprint src d fs) : Bounds rd wr fs := by
    obtain ⟨r,w⟩ := h.interval hsrc
    exact ⟨fun a v hv => Or.inl (r a v hv),fun a v hv => (w a v hv).elim⟩
  cases run with | seq head payload =>
  obtain ⟨hh,arg,next⟩ := header n addr (gridWords B order w) (DemandPreparation.publicWords order p B.scale w)
    (payloadWords B supply w) j (rd := rd) (wr := wr)
    (fun hg => narrow (DemandFootprint.gridCode order p (DemandGridRAM.fixedRows B) _ src hg))
    (fun hr => narrow (DemandFootprint.repetition _ src hr))
    (show wr dst.val by dsimp [wr]; omega) (show wr (dst+1).val by dsimp [wr]; rw [addOne]; omega) head
  have away (i : Fin 7) : headReg n i ∉ Set.range (payloadReg n) := outRange fun _ => payload_head
  let pub := words addr (gridWords B order w) (DemandPreparation.publicWords order p B.scale w)
    (payloadWords B supply w)
  obtain ⟨hp,unmoved⟩ := Rebased.restrictExec (payloadReg n) payloadPort (headReg n 4) (away 4) pub
    (payloadCode B n) payload
  rw [show pub ∘ payloadPort = payloadWords B supply w from payload_words ..,arg] at hp
  obtain ⟨read,write⟩ := PayloadFootprint.storedCall _ (dst+2) (by rw [addTwo]; exact dfit.le) hp
  refine ⟨(unmoved _ (away 5)).trans next,append hh ⟨?_,?_⟩⟩
  · intro a v hv
    exact Or.inr ((read a v hv).trans ((congrArg Fin.val (show dst+2-1 = dst+1 by ring)).trans addOne))
  · intro a v hv
    obtain ⟨lo,hi⟩ := write a v hv
    rw [addTwo] at lo hi
    exact ⟨by omega,hi⟩

/-- At any successful call, even with an arbitrary tape and fuel, the worker
advances one ordinal. It reads its own demand row and repetition header and
writes exclusively in the term row. -/
theorem call (addr : Fin 4 → BurstRAM.Word w) (j : BurstRAM.Word w) (mem : Memory w)
    (cap : ℕ) (bits : List Bool) (rep : Report w) (hsrc : (source addr j).val+d ≤ 2^w)
    (hdst : (base addr j).val+2+n < 2^w)
    (run : execute (program B order supply addr) cap ((program B order supply addr).start j) mem bits = some rep) :
    rep.result = some (j+1) ∧
      Reads (fun i => ((source addr j).val ≤ i ∧ i < (source addr j).val+d) ∨ i = (base addr j).val+1) rep.events ∧
      Writes (fun i => (base addr j).val ≤ i ∧ i < (base addr j).val+2+n) rep.events := by
  obtain ⟨_,_,he,result,_,_⟩ := (Flow.template_execute_iff
    (code (gridCode B order) (DemandPreparation.repetitionCall d) (payloadCode B n)) (some (headReg n 5))
    (motifData B order supply w addr) j (fun _ => 0) (fun _ => 0) mem cap bits rep).mp run
  obtain ⟨inc,fp⟩ := flow B order supply addr j hsrc hdst he
  exact ⟨result.trans (congrArg some inc),fp⟩

variable {m : ℕ}

/-- The footprints of any contiguous segment are contained in the union of
its rows. The predicates can be widened to fit the scheduler's memory layout. -/
theorem segment (L : Layout m d n w) (addr : Fin 4 → BurstRAM.Word w) (ha : Addresses L addr)
    (rd wr : ℕ → Prop)
    (demand : ∀ i x, (L.source i).val ≤ x → x < (L.source i).val+d → rd x)
    (header : ∀ i, rd ((L.base i).val+1))
    (term : ∀ i x, (L.base i).val ≤ x → x < (L.base i).val+2+n → wr x)
    (start cap : ℕ) (mem : Memory w) (bs : List (List Bool)) (rs : List (Report w))
    (size : start+bs.length ≤ m)
    (run : runSegment (program B order supply addr) cap (some (start : BurstRAM.Word w)) mem bs = some rs) :
    Reads rd (eventLog rs) ∧ Writes wr (eventLog rs) := by
  apply OrdinalRun.footprint (program B order supply addr) cap (fun j => (j : BurstRAM.Word w)) m
    (fun _ _ => True) rd wr _ start bs mem rs size trivial run
  intro j hj mem _ bits rep he
  let i : Fin m := ⟨j,hj⟩
  obtain ⟨hs,ht⟩ := ha i
  have fitS := hs.symm ▸ L.sourceFits i
  have fitT := ht.symm ▸ L.termFits i
  obtain ⟨inc,reads,writes⟩ := call B order supply addr (i.val : BurstRAM.Word w) mem cap bits rep fitS fitT he
  rw [hs,ht] at reads
  rw [ht] at writes
  refine ⟨by simpa [i,Nat.cast_add] using inc,trivial,fun a v hv => ?_,fun a v hv => ?_⟩
  · rcases reads a v hv with ⟨lo,hi⟩ | eq
    · exact demand i _ lo hi
    · exact eq ▸ header i
  · obtain ⟨lo,hi⟩ := writes a v hv
    exact term i _ lo hi

/-- With the paper's strided layout, every successful segment reads between
the first demand cell and the end of the descriptor arena. Its writes are
confined to that arena, including for a partial pass starting at a later row. -/
theorem strided_segment (src dst srcStride termStride : ℕ) (hd : d ≤ srcStride) (hn : 2+n ≤ termStride)
    (sep : src+m*srcStride ≤ dst) (fit : dst+m*termStride < 2^w)
    (start cap : ℕ) (mem : Memory w) (bs : List (List Bool)) (rs : List (Report w))
    (size : start+bs.length ≤ m)
    (run : runSegment (program B order supply ![src,srcStride,dst,termStride]) cap
      (some (start : BurstRAM.Word w)) mem bs = some rs) :
    Reads (fun x => src ≤ x ∧ x < dst+m*termStride) (eventLog rs) ∧
      Writes (fun x => dst ≤ x ∧ x < dst+m*termStride) (eventLog rs) := by
  let L := strided m d n w src dst srcStride termStride hd hn sep fit
  have stops (i : Fin m) (stride : ℕ) : i.val*stride+stride ≤ m*stride := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right stride (Nat.succ_le_of_lt i.isLt)
  have s (i : Fin m) : (L.source i).val = src+i.val*srcStride := by
    exact Nat.mod_eq_of_lt (by have := stops i srcStride; omega)
  have t (i : Fin m) : (L.base i).val = dst+i.val*termStride := by
    exact Nat.mod_eq_of_lt (by have := stops i termStride; omega)
  apply segment B order supply L _ (addresses_strided src dst srcStride termStride hd hn sep fit)
    _ _ _ _ _ start cap mem bs rs size run
  · intro i x lo hi
    rw [s] at lo hi
    have := stops i srcStride
    exact ⟨by omega,by omega⟩
  · intro i
    rw [t]
    have := stops i termStride
    exact ⟨by omega,by omega⟩
  · intro i x lo hi
    rw [t] at lo hi
    have := stops i termStride
    exact ⟨by omega,by omega⟩

end CompressorRecords.TermWorker.Footprint

end VPVNP
end Computability
end OAI
