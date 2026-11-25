import OAI.Computability.BorderVNP.RoutingISAFiniteScalarMemory
import OAI.Computability.BorderVNP.TeamContractionPaths

/-! # Finite-field suffix execution in the actual validator output memory

Only live header words, the preceding signed tasks' original source data and
the ordinary arena layout are needed. The second call at each cell uses at most
the first call's word budget and adds linear work in the actual reported bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarBatch

open VPVNP.BurstRAM TypedTaskBuilder FiniteScalarRounds FiniteScalarLibrary

/-- The second burst is at most the first cell-validator burst, even on an empty tail. -/
theorem Row.burst_le {w : ℕ} (r : Row) (hw : 0 < w) (bank : r.task.cell.external=r.supplied++r.claims) :
    (r.words w).length ≤ (r.task.cell.burst w).length := by
  have len (xs : List Bool) : (CompactFrame.pack w xs).length = (2*xs.length)/w+1 := by
    rw [CompactFrame.length_pack,← CompactFrame.wordCount,CompactFrame.wordCount_terminator hw]
  rw [Row.words,CellPacket.Task.burst,len,len]
  apply Nat.succ_le_succ
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  simp [CellPacket.Task.payload,CellPacket.envelope,bank]
  omega

/-- The per-team charge of the suffix consists of fixed overhead per local cell and
one linear scan of the true checked bits. -/
theorem charge_le {w : ℕ} (rows : ℕ → Row) (count : ℕ) (hw : 0 < w) :
    setup.slots+(∑ j ∈ Finset.range count, ((rows j).cost w+1))+1 ≤
      setup.slots+1+(locate.slots+CompactWrite.setup.slots+FiniteScalarCall.count.slots+6)*count +
        (CompactWrite.step.slots+3)*(∑ j ∈ Finset.range count, (rows j).claims.length) := by
  let C := locate.slots+CompactWrite.setup.slots+FiniteScalarCall.count.slots+6
  let D := CompactWrite.step.slots+3
  have bound (j : ℕ) : (rows j).cost w+1 ≤ C+D*(rows j).claims.length := by
    have q : ((rows j).words w).length ≤ 2*(rows j).claims.length+1 := by
      rw [Row.words,CompactFrame.length_pack,← CompactFrame.wordCount,CompactFrame.wordCount_terminator hw]
      exact Nat.succ_le_succ (Nat.div_le_self ..)
    dsimp [Row.cost,C,D]
    rw [Nat.add_mul,Nat.add_mul]
    omega
  have all := Finset.sum_le_sum (s:=Finset.range count) (fun j _ => bound j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,←Finset.mul_sum] at all
  change _ ≤ setup.slots+1+C*count+D*(∑ j ∈ Finset.range count, (rows j).claims.length)
  rw [Nat.mul_comm C count]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

/-- A physically prepared finite team executes the scalar correction on the exact
reported words that survived the signed validators. Its accepting path is unique,
its field returns are the original multipliers, and all actual resources fit the
signed argument cap plus the stated linear suffix cost. -/
theorem prepared_field {Q : Type} {w m fuel n : ℕ} (F : Type*) [Field F] [Fintype F]
    (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth) (old : FieldProcessor.Returns Q (Option Bool) F m 8)
    (pub : Arg → Word w) (s : Bank w) (original : Memory w) (l : Layout) (publicMem : ℕ → ℕ)
    (rows : ℕ → Row) (d : ℕ → ℕ) (claim : (i : ℕ) → Index F → Fin (d i) → Bool)
    (hp : (pub 0).val=l.frame) (fields : l.Fields (readings original))
    (width : (original (l.frame+30)).val=w) (len : (original (l.frame+90)).val=l.before publicMem l.cells)
    (room : l.Room publicMem w) (ar : l.Arenas publicMem w (fun j => (rows j).task))
    (headerRange : l.SourceRange l.control 8) (tailRange : l.SourceRange l.tails l.cells)
    (ids : ∀ i < l.before publicMem l.cells, (rows i).cell=globalCell l publicMem i)
    (stored : ∀ i < l.before publicMem l.cells, (rows i).task.Stored original l.tasks i)
    (data : ∀ i < l.before publicMem l.cells, (rows i).task.cell.Stored original)
    (bank : ∀ i < l.before publicMem l.cells, (rows i).task.cell.external=(rows i).supplied++(rows i).claims)
    (tail : ∀ i < l.before publicMem l.cells, (original (l.tails+(rows i).cell)).val=(rows i).claims.length)
    (streamAt : ∀ i < l.before publicMem l.cells, (rows i).claims=stream F (claim i))
    (clock : ∀ i < l.before publicMem l.cells, 2*d i*Fintype.card F < fuel)
    (cap : ∀ i < l.before publicMem l.cells, ((rows i).task.cell.burst w).length ≤ TeamScales.width n (1/2)) :
    let mac := TeamSiteEvents.macros (combine F lib) fuel
    let count := l.before publicMem l.cells
    let after := TypedBatch.written original (fun j => (rows j).task) count
    ∃ es t, Runs pub mac code s after es t (written after rows count) ∧
      TeamContraction.Within (setup.slots+1+(locate.slots+CompactWrite.setup.slots+FiniteScalarCall.count.slots+6)*count +
        (CompactWrite.step.slots+3)*(∑ j ∈ Finset.range count, (rows j).claims.length)) (TeamScales.width n (1/2)) (n^25) es ∧
      bursts es = (List.range count).map (fun j => (rows j).event w) ∧
      (bursts es).map (FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel) =
        (List.range count).map (fun j => some (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (claim j i)))) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ gs v mu, Runs pub mac code s after gs v mu → gs=es ∧ v=t ∧ mu=written after rows count := by
  intro mac count after
  have keep (a : ℕ) (below : a < l.scratch) (apart : a < l.calls ∨ l.calls+3*l.cells ≤ a) :
      after a = original a :=
    TypedBatch.preserve original _ (i:=0) (Nat.zero_le _) a (fun j _ hj => TypedTaskBuilder.below l publicMem ar hj below apart)
  have frame (k : ℕ) (hk : k < 112) : after ((pub 0).val+k)=original (l.frame+k) := by
    rw [hp]
    apply keep
    · have := room.outputs.1; have := ar.calls; omega
    · left; have := room.outputs.1; omega
  have control : (after ((pub 0).val+92)).val=l.control := (congrArg Fin.val (frame 92 (by decide))).trans fields.outer.2.2.2.2.2.2.2
  have tailWord : (after ((after ((pub 0).val+92)).val+7)).val=l.tails := by
    rw [control,keep _ (by have := headerRange.end_le; omega) (by rcases headerRange.calls with h|h <;> omega)]
    exact fields.header.2.2.2.2.2.2.2
  have liveRows := live l publicMem rows room ar tailRange ids stored data bank tail
  have fits : (pub 0).val+92 < 2^w := by rw [hp]; have := room.frame; omega
  have hw : 0 < w := by cases w with
    | zero => simp at fits
    | succ w => exact Nat.zero_lt_succ w
  obtain ⟨es,t,run,cost,events,vals,clean,unique⟩ := field_run F lib old pub s after rows d claim fits
    ((congrArg Fin.val (frame 30 (by decide))).trans width)
    ((congrArg Fin.val (frame 89 (by decide))).trans fields.outer.2.2.2.2.2.2.1)
    ((congrArg Fin.val (frame 90 (by decide))).trans len)
    ((congrArg Fin.val (frame 14 (by decide))).trans fields.outer.2.2.1)
    (by rw [control]; have := room.control; omega) tailWord
    (by have := room.tasks; have := l.before_le publicMem l.cells; omega)
    (fun i hi => (liveRows i hi).1) (fun i hi => (liveRows i hi).2) streamAt clock
  refine ⟨es,t,run,⟨cost.trans (charge_le rows count hw),?_,?_⟩,events,vals,clean,unique⟩
  · intro e he
    by_cases b : isBurst e
    · have mem : e ∈ bursts es := List.mem_filter.mpr ⟨he,b⟩
      rw [events] at mem
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
      have h := List.mem_range.mp hi
      exact ((rows i).burst_le hw (bank i h)).trans (cap i h)
    · cases ha : e.action with
      | ordinary a => simp [TeamTranscript.Action.extra]
      | burst a q => simp [isBurst,ha] at b
  · intro e he
    rw [(clean _ he).1]
    exact Nat.zero_le _

end RoutingISA.FiniteScalarBatch

end BorderVNP
end Computability
end OAI
