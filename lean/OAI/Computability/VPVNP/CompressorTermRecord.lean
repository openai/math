import OAI.Computability.VPVNP.CompressorChoiceGridStage
import OAI.Computability.VPVNP.CompressorPayloadCall

/-!
# Constructing a motif term descriptor in external memory

A local demand record supplies the widths. A sequence of fixed native calls
writes the selected rounded-grid row and repetition count, followed by one
word per admitted supply coordinate. Every transition carries just the
previous return word and the post-call memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermRecord

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open MotifGrid MotifBlocks MotifConversion MotifSelector
open scoped Fin.CommRing

variable {w : ℕ}

/-- A returned row number or repetition word is stored in its descriptor cell.
The second public word is the cursor passed to the next native call. -/
def saveFlow : Flow 3 2 :=
  .seq (.line (.stateWord 0)) <|
  .seq (.line (.publicWord 1 0)) <|
  .seq (.line (.write 1 0)) (.line (.publicWord 2 1))

/-- Run the native store that saves the incoming value at `target` and returns `next` for the
following call. -/
def save (target next value : BurstRAM.Word w) (mem : Memory w) : Option (Report w) :=
  let prog := (saveFlow.template (some 2)).instantiate w ![target,next]
  execute prog.program 5 (prog.program.start value) mem []

/-- Exact four-event report of the single-cell save, including the return word for the next
call. -/
def saved (target next value : BurstRAM.Word w) : Report w :=
  ⟨[.tick,.tick,.write target value,.tick],some next⟩

theorem save_native (target next value : BurstRAM.Word w) (mem : Memory w) :
    save target next value mem = some (saved target next value) ∧
      after mem (saved target next value).events = writeMemory mem target value := by
  let pub : Fin 2 → BurstRAM.Word w := ![target,next]
  let rs : Regs w 3 := fun _ => 0
  let a := Function.update rs 0 value
  let b := Function.update a 1 target
  let out := Function.update b 2 next
  let mem' := writeMemory mem target value
  have ha : Flow.Exec pub value (.line (.stateWord 0)) rs mem [.tick] a mem := .line rfl
  have hb : Flow.Exec pub value (.line (.publicWord 1 0)) a mem [.tick] b mem := .line rfl
  have hc : Flow.Exec pub value (.line (.write 1 0)) b mem [.write target value] b mem' := by
    apply Flow.Exec.line
    simp (config := {decide := true}) [Op.effect,b,a,Function.update,mem']
  have hd : Flow.Exec pub value (.line (.publicWord 2 1)) b mem' [.tick] out mem' := .line rfl
  exact ⟨DemandPreparation.execute_return saveFlow pub 2 value mem mem' (saved target next value).events out
    (.seq ha (.seq hb (.seq hc hd))) rfl 4 le_rfl,rfl⟩

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- Read the actual demands, select and store the grid row, read the same
demand words for the repetition count, then store it next to the row. -/
noncomputable def headers {d : ℕ} (order : Fin d ≃ D) (src base : BurstRAM.Word w)
    (mem : Memory w) (prepFuel : ℕ) : Option (List (Report w)) := do
  let rows := DemandGridRAM.fixedRows B
  let grid := DemandGridRAM.machine order p rows w
  let g ← execute grid.program (6*d+(11*d+4)*B.grid.demands.toList.length+8)
    (grid.program.start src) mem []
  let row ← g.result
  let m₁ := after mem g.events
  let sr ← save base src row m₁
  let src' ← sr.result
  let m₂ := after m₁ sr.events
  let reps := DemandPreparation.repetitionMachine order p B.scale w
  let r ← execute reps.program prepFuel (reps.program.start src') m₂ []
  let u ← r.result
  let su ← save (base+1) (base+2) u (after m₂ r.events)
  return [g,sr,r,su]

/-- Generated descriptor headers use adjacent external words. -/
def withHeaders (mem : Memory w) (base row u : BurstRAM.Word w) : Memory w :=
  writeMemory (writeMemory mem base row) (base+1) u

private theorem demands_write {d : ℕ} {X : Type*} (order : Fin d ≃ X) (src base row : BurstRAM.Word w)
    (mem : Memory w) (hsrc : src.val+d ≤ 2^w) (hsep : src.val+d ≤ base.val ∨ base.val < src.val) :
    DemandPreparation.demandAt order src (writeMemory mem base row) =
      DemandPreparation.demandAt order src mem := by
  funext e
  obtain ⟨i,rfl⟩ := order.surjective e
  rw [DemandPreparation.demandAt_address _ _ _ hsrc, DemandPreparation.demandAt_address _ _ _ hsrc]
  have hne : src.val+i.val ≠ base.val := by have := i.isLt; omega
  simp [writeMemory,hne]

theorem headers_native {d : ℕ} (order : Fin d ≃ D) (hp : ∀ i, 0 < p i) :
    ∃ K : ℕ, ∀ M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (src base : BurstRAM.Word w) (mem : Memory w),
      src.val+d ≤ 2^w → (src.val+d ≤ base.val ∨ base.val < src.val) →
      (∀ i, DemandPreparation.demandAt order src mem i ≤ M) →
      let demand := DemandPreparation.demandAt order src mem
      let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
      ∃ (row u : BurstRAM.Word w) (gs rs : List (Event w)),
        B.grid.demands.toList[row.val]? = some (demandGrid B hp demand).val ∧ u.val = repetitions B demand ∧
        headers B order src base mem fuel =
          some [⟨gs,some row⟩, saved base src row, ⟨rs,some u⟩, saved (base+1) (base+2) u] ∧
        after mem gs = mem ∧ after (writeMemory mem base row) rs = writeMemory mem base row ∧
        choiceBits gs = [] ∧ choiceBits rs = [] ∧ countProbes gs ≤ d+B.grid.demands.toList.length*d ∧
        countProbes rs = d ∧ gs.length < 6*d+(11*d+4)*B.grid.demands.toList.length+8 ∧ rs.length < fuel := by
  let table := B.grid.demands.toList
  let rows := DemandGridRAM.fixedRows B
  obtain ⟨kg,hg⟩ := DemandGridRAM.native order p rows
  obtain ⟨kr,hr⟩ := DemandPreparation.repetition_native order p B.scale B.scale_pos
  obtain ⟨ku,hu⟩ := MotifChoiceRAM.native_word_fit p q B.scale B.scale_pos B.radius
  let K := max table.length.size (max ku (max kg kr))
  refine ⟨K,fun M w hW src base mem hsrc hsep hD => ?_⟩
  have hmax₁ := le_max_left table.length.size (max ku (max kg kr))
  have hmax₂ := le_max_right table.length.size (max ku (max kg kr))
  have hmax₃ := le_max_left ku (max kg kr)
  have hmax₄ := le_max_right ku (max kg kr)
  have hmax₅ := le_max_left kg kr
  have hmax₆ := le_max_right kg kr
  dsimp [K] at hW
  let b := DemandPreparation.demandAt order src mem
  let idx := GridRAM.firstRow p b rows
  let row : BurstRAM.Word w := Fin.ofNat _ idx
  let u : BurstRAM.Word w := Fin.ofNat _ (repetitions B b)
  let m₂ := writeMemory mem base row
  obtain ⟨gs,hgr,hgb,hgp,hgm,hgl⟩ := hg M w (by omega) src mem hD
  have hi : idx < 2^w := (List.findIdx_le_length (xs := List.ofFn rows) (p := _)).trans_lt
    (by rw [List.length_ofFn]; exact Nat.size_le.mp (show table.length.size ≤ w by omega))
  have hz := GridRAM.firstRow_getElem? p b rows
  rw [show List.ofFn rows = table from DemandGridRAM.fixedRows_list B,selectGrid_eq B hp b] at hz
  have he : DemandPreparation.demandAt order src m₂ = b := demands_write order src base row mem hsrc hsep
  obtain ⟨rs,hrr,hrb,hrp,hrm,hrl⟩ := hr M w (by omega) src m₂ (he ▸ hD)
  have uf := (hu M b hD).1
  have huv : u.val = repetitions B b := Nat.mod_eq_of_lt
    (uf.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  refine ⟨row,u,gs,rs,?_,huv,?_,hgm,hrm,hgb,hrb,hgp,hrp,hgl,by omega⟩
  · rw [show row.val = idx from Nat.mod_eq_of_lt hi]
    exact hz
  · dsimp only [rows] at hgr
    rw [he] at hrr
    let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
    change execute _ fuel _ m₂ [] = some ⟨rs,some u⟩ at hrr
    change headers B order src base mem fuel = _
    unfold headers
    simp only [hgr, bind, Option.bind_some, hgm]
    change ((save base src row mem).bind _) = _
    rw [(save_native base src row mem).1]
    simp only [Option.bind_some, saved]
    change ((execute _ fuel _ m₂ []).bind _) = _
    rw [hrr]
    simp only [Option.bind_some]
    change ((save (base+1) (base+2) u (after m₂ rs)).bind _) = _
    rw [hrm,(save_native (base+1) (base+2) u m₂).1]
    rfl


/-- Execute the five descriptor calls and keep their reports in order. The
payload call reads its own repetition word from the preceding record cell. -/
noncomputable def run {d n : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S) (src base : BurstRAM.Word w)
    (mem : Memory w) (prepFuel : ℕ) (bits : List Bool) : Option (List (Report w)) := do
  let hs ← headers B order src base mem prepFuel
  let payload ← endState (some src) hs
  let m := after mem (eventLog hs)
  let prog := PayloadWrite.storedMachine B supply w
  let choice ← execute prog.program (PayloadWrite.storedFuel B n w) (prog.program.start payload) m bits
  return hs ++ [choice]

private def headerReports (src base row u : BurstRAM.Word w) (gs rs : List (Event w)) : List (Report w) :=
  [⟨gs,some row⟩,saved base src row,⟨rs,some u⟩,saved (base+1) (base+2) u]

private theorem after_append (m : Memory w) (es fs : List (Event w)) :
    after m (es ++ fs) = after (after m es) fs := List.foldl_append

private theorem headerMemory (src base row u : BurstRAM.Word w) (gs rs : List (Event w))
    (mem : Memory w) (hg : after mem gs = mem)
    (hr : after (writeMemory mem base row) rs = writeMemory mem base row) :
    after mem (eventLog (headerReports src base row u gs rs)) = withHeaders mem base row u := by
  simp only [headerReports,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [after_append, hg, after_append]
  change after (writeMemory mem base row) (rs ++ _) = _
  rw [after_append, hr]; rfl

/-- The descriptor memory image contains precisely the two headers and the
selected integer vector. All other external addresses retain their input. -/
def recordMemory {n : ℕ} (mem : Memory w) (base row u : BurstRAM.Word w) (supply : Fin n ≃ S)
    (v : S → ℕ) : Memory w :=
  PayloadWrite.overlay (withHeaders mem base row u) (base+2).val (List.ofFn fun i => (v (supply i) : BurstRAM.Word w))


omit [Fintype S] in
/-- Read the physical fields of a term record. The layout is the rounded-grid
index, the repetition count, and then the outer supply coordinates in order. -/
theorem recordMemory_fields {n : ℕ} (mem : Memory w) (base row u : BurstRAM.Word w)
    (supply : Fin n ≃ S) (v : S → ℕ) (hfit : base.val + 2 + n < 2^w) :
    let m := recordMemory mem base row u supply v
    m base.val = row ∧ m (base.val+1) = u ∧
      (∀ i, m (base.val+2+i.val) = (v (supply i) : BurstRAM.Word w)) ∧
      ∀ j, j < base.val ∨ base.val+2+n ≤ j → m j = mem j := by
  let vec := fun i => (v (supply i) : BurstRAM.Word w)
  let m := withHeaders mem base row u
  have htwo : 2 < 2^w := by omega
  have hone : 1 < 2^w := by omega
  have one : (base+1).val = base.val+1 := by
    rw [Fin.val_add, show (1 : BurstRAM.Word w).val = 1 from Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt (by omega)]
  have two : (base+2).val = base.val+2 := by
    rw [Fin.val_add, show (2 : BurstRAM.Word w).val = 2 from Nat.mod_eq_of_lt htwo, Nat.mod_eq_of_lt (by omega)]
  dsimp only [recordMemory]
  rw [two]
  refine ⟨?_,?_,PayloadWrite.overlay_slot m (base.val+2) vec,?_⟩
  · rw [PayloadWrite.overlay_outside m (base.val+2) vec base.val (Or.inl (by omega))]
    simp [m,withHeaders,writeMemory,one]
  · rw [PayloadWrite.overlay_outside m (base.val+2) vec (base.val+1) (Or.inl (by omega))]
    simp [m,withHeaders,writeMemory,one]
  · intro j hj
    rw [PayloadWrite.overlay_outside m (base.val+2) vec j (by omega)]
    simp [m,withHeaders,writeMemory,one,show j ≠ base.val by omega,show j ≠ base.val+1 by omega]

/-- The stored words read back as the original natural widths in every
admitted block. This is the integer readout needed by the supply-width pass. -/
theorem recordMemory_supply {n : ℕ} (mem : Memory w) (base row u : BurstRAM.Word w)
    (supply : Fin n ≃ S) (hq : ∀ i, 0 < q i) (demand : D → ℕ) (v : ↥(outerIndices B demand))
    (hw : outerCap B demand < 2^w) (hfit : base.val+2+n < 2^w) (hu : u.val = repetitions B demand) :
    let m := recordMemory mem base row u supply v.val
    ∀ i, (m (base.val+2+i.val)).val + (m (base.val+1)).val * B.selectorBits =
      supplyWidths B demand v.val (supply i) := by
  dsimp only
  intro i
  obtain ⟨_,hrep,hv,_⟩ := recordMemory_fields mem base row u supply v.val hfit
  rw [hv i,hrep,hu,Fin.val_natCast]
  apply congrArg (· + repetitions B demand * B.selectorBits)
  exact Nat.mod_eq_of_lt ((MotifAdmission.payload_le_cap q hq _ _ _ _
    ((mem_outerIndices_iff B hq _ _).mp v.property) _).trans_lt hw)

/-- The native term phase produces exactly one external-memory descriptor for
each stream admitted by the motif. The two headers, every payload word, all
five reports and the probe allowance are accounted for on each admitted path. -/
theorem run_spec {d n : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (src base : BurstRAM.Word w) (mem : Memory w),
      src.val+d ≤ 2^w → base.val+2+n < 2^w →
      (src.val+d ≤ base.val ∨ base.val+2+n ≤ src.val) →
      (∀ i, DemandPreparation.demandAt order src mem i ≤ M) →
      let demand := DemandPreparation.demandAt order src mem
      let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
      ∃ (hw : outerCap B demand < 2^w) (row u : BurstRAM.Word w),
        B.grid.demands.toList[row.val]? = some (demandGrid B hp demand).val ∧ u.val = repetitions B demand ∧
        (∀ bits, (run B order supply src base mem fuel bits).isSome ↔
          ∃ v, (outerReader B supply hq demand w hw).read bits = some (v, [])) ∧
        ∀ v, ∃ reports, run B order supply src base mem fuel ((outerReader B supply hq demand w hw).encode v) =
          some reports ∧ reports.length = 5 ∧ after mem (eventLog reports) = recordMemory mem base row u supply v.val ∧
          branchPaths reports = [[],[],[],[],(outerReader B supply hq demand w hw).encode v] ∧
          countProbes (eventLog reports) ≤ d+B.grid.demands.toList.length*d+d+n+3 ∧
          (eventLog reports).length ≤ 6*d+(11*d+4)*B.grid.demands.toList.length+8 +
            fuel + 8 + PayloadWrite.storedFuel B n w := by
  obtain ⟨kh,hh⟩ := headers_native B order hp
  obtain ⟨kv,hv⟩ := PayloadWrite.stored_outer_paths B supply hq
  refine ⟨max kh kv,fun M w hW src base mem hsrc hbase hsep hD => ?_⟩
  have hk₁ := le_max_left kh kv
  have hk₂ := le_max_right kh kv
  let demand := DemandPreparation.demandAt order src mem
  let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
  obtain ⟨row,u,gs,rs,hrow,hu,header,hgm,hrm,hgb,hrb,hgp,hrp,hgl,hrl⟩ :=
    hh M w (by omega) src base mem hsrc (by omega) hD
  let hs := headerReports src base row u gs rs
  let dst := base+2
  let m := withHeaders mem base row u
  change headers B order src base mem fuel = some hs at header
  have hm : after mem (eventLog hs) = m := headerMemory src base row u gs rs mem hgm hrm
  have hd : dst.val = base.val+2 := by
    have two : 2 < 2^w := by omega
    change (base+2).val = _
    rw [Fin.val_add, show (2 : BurstRAM.Word w).val = 2 from Nat.mod_eq_of_lt two, Nat.mod_eq_of_lt (by omega)]
  have hsub : dst-1 = base+1 := by dsimp [dst]; ring
  have hread : (m (dst-1).val).val = repetitions B demand := by simp [hsub,m,withHeaders,writeMemory,hu,demand]
  obtain ⟨hw,har,paths⟩ := hv M demand hD w (by omega) dst m (by omega) hread
  let prog := PayloadWrite.storedMachine B supply w
  let read (bits : List Bool) := execute prog.program (PayloadWrite.storedFuel B n w) (prog.program.start dst) m bits
  have reduce (bits : List Bool) : run B order supply src base mem fuel bits = (read bits).map (hs ++ [·]) := by
    simp only [run, header, bind, Option.bind_some, show endState (some src) hs = some dst from rfl, hm, pure]
    change ((read bits).bind fun r => some (hs ++ [r])) = _
    cases read bits <;> rfl
  refine ⟨hw,row,u,hrow,hu,fun bits => ?_,fun v => ?_⟩
  · change (run B order supply src base mem fuel bits).isSome ↔ _
    rw [reduce,Option.isSome_map]
    exact har bits
  · obtain ⟨es,he,hmem,hp,hes,hb⟩ := paths v
    change read _ = some ⟨es,none⟩ at he
    refine ⟨hs ++ [⟨es,none⟩],?_,rfl,?_,?_,?_,?_⟩
    · change run B order supply src base mem fuel _ = _
      rw [reduce, he]; rfl
    · rw [show eventLog (hs ++ [⟨es,none⟩]) = eventLog hs ++ es by simp [eventLog],
        after_append, hm]
      exact hmem
    · simp [hs,headerReports,branchPaths,saved,choiceBits,hgb,hrb,hb,demand]
    · simp [hs,headerReports,eventLog,DemandPreparation.probes_append,saved,countProbes,hrp,hp]
      simp only [Finset.length_toList] at hgp
      omega
    · change (eventLog (hs ++ [⟨es,none⟩])).length ≤ 6*d+(11*d+4)*B.grid.demands.toList.length+8 + fuel + 8 + _
      simp [hs,headerReports,eventLog,saved]
      simp only [Finset.length_toList] at hgl
      change rs.length < fuel at hrl
      omega

end CompressorRecords.TermRecord

end VPVNP
end Computability
end OAI
