import OAI.Computability.VPVNP.LiveHeaderPrefix
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PairedChain

/-!
# Native primed index stages in the live header program

The setup stage initializes the borrow and both low bits. The following
bounded stage reads one unpacked group digit per call and writes the shifted
digits of the two primed indices. The all-zero low digits of the last group
are included in the same execution, with the borrow still set at the end.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.PrimedStages

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM LiveHeaderSchedule
open LiveHeader.PrimedGroupIndices
open scoped Fin.CommRing

variable {w : ℕ}

/-- The four addresses of the original group digits, the two primed digit arrays, and the
shared borrow cell. -/
def operands (w : ℕ) (s : Sizes) (base : ℕ) : Fin 4 → Word w :=
  ![(indexBase base : Word w), (leftIndexBase s base : Word w),
    (rightIndexBase s base : Word w), (borrowAddr base : Word w)]

private theorem init_row (s : Sizes) (base : ℕ) :
    rowData w s base .primedInit ∘ includeFin (by decide : 4 ≤ 17) = operands w s base := by
  funext j
  fin_cases j <;> rfl

private theorem digits_row (s : Sizes) (base : ℕ) :
    rowData w s base .primedDigits ∘ includeFin (by decide : 5 ≤ 17) =
      LiveHeaderBounded.publicData (operands w s base) ((s.h+1 : ℕ) : Word w) := by
  funext j
  fin_cases j <;> rfl

theorem operand_values (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) :
    ((operands w s base) 0).val = indexBase base ∧
      ((operands w s base) 1).val = leftIndexBase s base ∧
      ((operands w s base) 2).val = rightIndexBase s base ∧
      ((operands w s base) 3).val = borrowAddr base ∧ base < 2^w ∧ s.h+1 < 2^w := by
  rw [limit_eq] at fit
  change (indexBase base : Word w).val = _ ∧ (leftIndexBase s base : Word w).val = _ ∧
    (rightIndexBase s base : Word w).val = _ ∧ (borrowAddr base : Word w).val = _ ∧ _
  simp only [Fin.val_natCast, indexBase, leftIndexBase, rightIndexBase, populationAddr,
    highAddr, borrowAddr]
  repeat' constructor
  all_goals first | apply Nat.mod_eq_of_lt; omega | omega

/-- The three operands addressed by a digit are disjoint, fit in word memory,
and all input digits are outside the two output buffers and borrow cell. -/
theorem layout_of_fit (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) :
    Layout (operands w s base) (s.h+1) := by
  obtain ⟨ha,hl,hr,hb,-,-⟩ := operand_values s base fit
  rw [limit_eq] at fit
  constructor
  all_goals simp only [outside, ha,hl,hr,hb, rightIndexBase,leftIndexBase,populationAddr,
    highAddr,indexBase,borrowAddr]
  all_goals omega

theorem tag_outside (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) :
    outside (operands w s base) (s.h+1) base := by
  obtain ⟨-,hl,hr,hb,-,-⟩ := operand_values s base fit
  simp only [outside, hl, hr, hb, rightIndexBase,leftIndexBase,populationAddr,
    highAddr,indexBase,borrowAddr]
  omega

private def setupEvents (pub : Fin 4 → Word w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .tick, .write (pub 1) 1, .write (pub 2) 0, .write (pub 3) 1]

private theorem setup_exec (pub : Fin 4 → Word w) (m : Memory w) :
    let P := (((lines setup (by decide)).template none).instantiate w pub).program
    execute P 9 (P.start 0) m [] = some ⟨setupEvents pub,none⟩ := by
  have ht : ∃ rs', trace pub 0 setup (fun _ => 0) m = some (setupEvents pub,rs',initialized pub m) := by
    simp (config := { decide := true }) [setup,setupEvents,trace,Op.effect,Function.update,initialized]
  obtain ⟨rs',h⟩ := ht
  apply (Flow.template_execute_iff _ none pub 0 (fun _ => 0) (fun _ => 0) m 9 [] _).mpr
  exact ⟨rs', initialized pub m,(PrimedCounter.Admin.exec_lines_iff_trace (by decide)).mpr h,
    rfl, by change 8 < 9; decide, rfl⟩

/-- The accepting setup call has exactly three writes and initializes the
three scalar cells before the enclosing linker advances the stage tag. -/
theorem init_run (s : Sizes) (base : ℕ) (m : Memory w) :
    let pub := operands w s base
    let P := ((stageTemplate .primedInit).2.instantiate w (rowData w s base .primedInit)).program
    ∃ rs, runSegment P 9 (some 0) m [[]] = some rs ∧ endState (some 0) rs = none ∧
      after m (eventLog rs) = initialized pub m ∧ rs.length = calls s .primedInit ∧
      (∀ rep ∈ rs, rep.probes = 3 ∧ choiceBits rep.events = []) ∧
      RAMBuckets.cost Report.probes rs = 4 ∧
      LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m rs := by
  dsimp only
  let rep : Report w := ⟨setupEvents (operands w s base),none⟩
  have he := entry_start ((lines setup (by decide)).template none) (by decide) (by decide)
    (rowData w s base .primedInit) 9 0 m []
  rw [init_row] at he
  refine ⟨[rep], ?_, rfl, rfl, rfl, ?_, rfl,
    LiveStageLink.PreservesTagOnReturns.singleton_accept _ _ _ rfl⟩
  · simp only [stageTemplate, runSegment]
    rw [he, setup_exec]
    rfl
  · intro y hy
    obtain rfl := List.mem_singleton.mp hy
    exact ⟨rfl, rfl⟩

/-- Values supplied by the primed initialization stage. -/
structure Ready (pub : Fin 4 → Word w) (m : Memory w) : Prop where
  borrow : m (pub 3).val = 1
  left : m (pub 1).val = 1
  right : m (pub 2).val = 0

theorem ready_initialized (pub : Fin 4 → Word w) (n : ℕ) (layout : Layout pub n) (m : Memory w) :
    Ready pub (initialized pub m) := by
  have hl := layout.borrowLeft
  have hr := layout.borrowRight
  have hsep := layout.outputsApart
  constructor <;> simp only [initialized,writeMemory,ite_true,show (pub 1).val ≠ (pub 3).val by omega,
    show (pub 1).val ≠ (pub 2).val by omega,show (pub 2).val ≠ (pub 3).val by omega,ite_false]

private theorem ready_inv {pub : Fin 4 → Word w} {i n : ℕ} (hi : 0 < i) {m : Memory w}
    (ready : Ready pub m) : Invariant pub i n 0 m m := by
  have hodd : (2*i-1).testBit 0 = true := by simp [Nat.testBit_eq_decide_div_mod_eq]; omega
  have heven : (2*i).testBit 0 = false := by simp [Nat.testBit_eq_decide_div_mod_eq]
  refine ⟨ready.borrow, ?_, ?_, fun _ _ => rfl⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa [hodd,encodeBit] using ready.left
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa [heven,encodeBit] using ready.right

private abbrev digitMachine (w : ℕ) (s : Sizes) (base : ℕ) :=
  ((stageTemplate .primedDigits).2.instantiate w (rowData w s base .primedDigits)).program

private theorem digits_execute (s : Sizes) (base : ℕ) (st : Word w) (m : Memory w) :
    let P := digitMachine w s base
    let S := (LiveHeaderBounded.machine (template digit 11) (operands w s base) ((s.h+1 : ℕ) : Word w)).program
    execute P 24 (P.start st) m [] = execute S 24 (S.start st) m [] := by
  have h := entry_start (LiveHeaderBounded.bounded (template digit 11)) (by decide) (by decide)
    (rowData w s base .primedDigits) 24 st m []
  rw [digits_row] at h
  exact h

/-- Prefix of the bounded source stage, including each active call's choices
and probes and preservation of the linker's tag at every returned cursor. -/
private theorem active_digits (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (i : ℕ) (hi : 0 < i)
    (m : Memory w) (ready : Ready (operands w s base) m) (input : stores m (operands w s base 0) (s.h+1) i)
    (n : ℕ) (hn : n ≤ s.h+1) :
    let pub := operands w s base
    let P := digitMachine w s base
    ∃ rs, runSegment P 24 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (n : Word w) ∧
      Invariant pub i (s.h+1) n m (after m (eventLog rs)) ∧ rs.length = n ∧
      (∀ rep ∈ rs, rep.probes = 5 ∧ choiceBits rep.events = []) ∧
      LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m rs := by
  dsimp only
  let pub := operands w s base
  have layout : Layout pub (s.h+1) := layout_of_fit s base fit
  obtain ⟨-,-,-,-,hbase,hsize⟩ := operand_values s base fit
  have baseval : (Fin.ofNat (2^w) base).val = base := Nat.mod_eq_of_lt hbase
  induction n with
  | zero => exact ⟨[],rfl,rfl,ready_inv hi ready,rfl,by simp,trivial⟩
  | succ j ih =>
    obtain ⟨rs,hr,hs,inv,hlen,hcounts,htags⟩ := ih (by omega)
    let mem := after m (eventLog rs)
    change Invariant pub i (s.h+1) j m mem at inv
    have hj : j < s.h+1 := by omega
    have hx : mem (pub 0 + (j : Word w)).val = encodeBit w (i.testBit j) := by
      rw [offset_val _ j (by have := layout.inputFit; omega),inv.frame _ (layout.inputOutside j hj)]
      exact input j hj
    obtain ⟨es,hd,hm,_,hp,hb⟩ := digit_native pub (j : Word w) mem _ _ hx inv.borrowCell
    let rep : Report w := ⟨.tick :: .tick :: .tick :: es, some ((j+1 : ℕ) : Word w)⟩
    have ha : (j : Word w) < ((s.h+1 : ℕ) : Word w) := by
      change j % 2^w < (s.h+1) % 2^w
      rwa [Nat.mod_eq_of_lt (hj.trans hsize),Nat.mod_eq_of_lt hsize]
    have hrun : execute (digitMachine w s base) 24 ((digitMachine w s base).start (j : Word w)) mem [] = some rep := by
      rw [digits_execute,LiveHeaderBounded.execute_active _ _ _ 21 _ ha,hd]
      simp only [rep,Nat.cast_add,Nat.cast_one,Option.map_some]
    have hmem : after mem rep.events = updated pub (j : Word w) mem (i.testBit j) (borrow i j) := hm
    have inv' : Invariant pub i (s.h+1) (j+1) m (after mem rep.events) := by
      rw [hmem]
      exact invariant_succ pub hi layout hj inv
    have hframe : after mem rep.events (Fin.ofNat (2^w) base).val = mem (Fin.ofNat (2^w) base).val := by
      rw [baseval,inv'.frame base (tag_outside s base fit), inv.frame base (tag_outside s base fit)]
    refine ⟨rs ++ [rep], ?_, ?_, ?_, by simp [hlen], ?_, htags.append ⟨fun _ => hframe,trivial⟩⟩
    · rw [List.replicate_succ',PrimedSchedule.runSegment_append,hr]
      simp only [Option.bind_some,hs,runSegment,hrun,mem,Option.map_some]
    · rw [endState_append]; rfl
    · simpa only [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append,mem] using inv'
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hcounts x hx
      · obtain rfl := List.mem_singleton.mp hx
        exact ⟨hp,hb⟩

private theorem cost_five (rs : List (Report w)) (h : ∀ x ∈ rs, x.probes = 5) :
    RAMBuckets.cost Report.probes rs = 6*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost,h r (by simp),ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp only [List.length_cons,Nat.mul_add]
    omega

/-- Readback at the actual scheduled addresses. Every entry is one RAM word
containing one low-endian digit. The borrow distinguishes the last group.
All scratch words outside those three output regions retain their values. -/
structure Output (s : Sizes) (base : ℕ) (g : Fin (2^(s.h+1))) (m out : Memory w) : Prop where
  left : ∀ j < s.h+2, out (leftIndexBase s base+j) = encodeBit w ((2*(g.val+1)-1).testBit j)
  right : ∀ j < s.h+2, out (rightIndexBase s base+j) = encodeBit w ((2*(g.val+1)).testBit j)
  borrow : out (borrowAddr base) = encodeBit w (decide (g.val+1 = 2^(s.h+1)))
  frame : ∀ a, a ≠ borrowAddr base →
    (a < leftIndexBase s base ∨ leftIndexBase s base+(s.h+2) ≤ a) →
    (a < rightIndexBase s base ∨ rightIndexBase s base+(s.h+2) ≤ a) → out a = m a

/-- The complete bounded stage on an arbitrary physical group, including
the last all-zero scanned index. It accepts after precisely one closing
call, having used exactly five probes and zero choice bits per active digit. -/
theorem digits_run (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (g : Fin (2^(s.h+1)))
    (m : Memory w) (ready : Ready (operands w s base) m)
    (input : ∀ j < s.h+1, m (indexBase base+j) = encodeBit w ((g.val+1).testBit j)) :
    let P := ((stageTemplate .primedDigits).2.instantiate w (rowData w s base .primedDigits)).program
    ∃ rs, runSegment P 24 (some 0) m (List.replicate (calls s .primedDigits) []) = some rs ∧
      endState (some 0) rs = none ∧ Output s base g m (after m (eventLog rs)) ∧
      rs.length = calls s .primedDigits ∧
      (∀ rep ∈ rs, rep.probes ≤ probes .primedDigits ∧ choiceBits rep.events = []) ∧
      RAMBuckets.cost Report.probes rs = 6*(s.h+1)+1 ∧
      LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m rs := by
  dsimp only
  let pub := operands w s base
  let z := LiveHeaderBounded.closedReport w
  let bound : Word w := (s.h+1 : ℕ)
  have hi : 0 < g.val+1 := Nat.zero_lt_succ _
  obtain ⟨ha,hl,hr,hb,-,-⟩ := operand_values s base fit
  have hx : stores m (pub 0) (s.h+1) (g.val+1) := by
    simpa only [pub,stores,ha] using input
  obtain ⟨rs,hactive,hs,inv,hlen,hcounts,htags⟩ := active_digits s base fit _ hi m ready hx _ le_rfl
  let mem := after m (eventLog rs)
  have hclosed : execute (digitMachine w s base) 24 ((digitMachine w s base).start bound) mem [] = some z := by
    rw [digits_execute,LiveHeaderBounded.execute_closed _ _ _ 20 _ le_rfl]
    rfl
  have hfinal : after m (eventLog (rs ++ [z])) = mem := by
    simp only [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append]
    rfl
  refine ⟨rs ++ [z], ?_, ?_, ?_, by simp [hlen,calls], ?_, ?_,
    htags.append (LiveStageLink.PreservesTagOnReturns.singleton_accept _ _ z rfl)⟩
  · change runSegment (digitMachine w s base) 24 (some 0) m (List.replicate ((s.h+1)+1) []) = _
    rw [List.replicate_succ',PrimedSchedule.runSegment_append,hactive]
    dsimp only [bound,mem] at hclosed
    simp only [Option.bind_some,hs,runSegment,hclosed,Option.map_some]
  · rw [endState_append]; rfl
  · rw [hfinal]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [stores,hl] using inv.left
    · simpa only [stores,hr] using inv.right
    · simpa only [hb,borrow_endpoint hi g.isLt] using inv.borrowCell
    · intro a ha₁ ha₂ ha₃
      exact inv.frame a (by simp only [outside,hl,hr,hb]; omega)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hcounts x hx).1.le,(hcounts x hx).2⟩
    · obtain rfl := List.mem_singleton.mp hx
      exact ⟨Nat.zero_le _,rfl⟩
  · rw [RAMBuckets.cost_append,cost_five rs (fun r hr => (hcounts r hr).1),hlen]
    rfl

/-- The initialization-to-digit handoff preserves the copied input and
the three freshly initialized words. -/
theorem handoff_ready {d : ℕ} (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w)
    (dest : Option (Fin d)) (m : Memory w) :
    let pub := operands w s base
    let out := LiveStageLink.transferMemory (Fin.ofNat _ base) dest (initialized pub m)
    Ready pub out ∧ (∀ j < s.h+1, out (indexBase base+j) = m (indexBase base+j)) := by
  dsimp only
  let pub := operands w s base
  have layout := layout_of_fit s base fit
  obtain ⟨ha,hl,hr,hb,hbase,-⟩ := operand_values s base fit
  have hz : (Fin.ofNat (2^w) base).val = base := Nat.mod_eq_of_lt hbase
  have hnon (a : ℕ) (h : a ≠ base) :
      LiveStageLink.transferMemory (Fin.ofNat (2^w) base) dest (initialized pub m) a = initialized pub m a := by
    cases dest with
    | none => rfl
    | some next => simp only [LiveStageLink.transferMemory,writeMemory,hz,ite_eq_right h]
  have ready := ready_initialized _ _ layout m
  have ho := tag_outside s base fit
  simp only [outside,hl,hr,hb] at ho
  constructor
  · refine ⟨?_,?_,?_⟩
    · rw [hnon _ (by rw [hb]; omega)]; exact ready.borrow
    · rw [hnon _ (by rw [hl]; omega)]; exact ready.left
    · rw [hnon _ (by rw [hr]; omega)]; exact ready.right
  · intro j hj
    have hf := layout.inputOutside j hj
    simp only [outside,ha,hl,hr,hb] at hf
    rw [hnon _ (by simp [indexBase]; omega)]
    simp only [pub,initialized,writeMemory,hb,hl,hr,ite_eq_right hf.1,
      ite_eq_right (show indexBase base+j ≠ rightIndexBase s base by omega),
      ite_eq_right (show indexBase base+j ≠ leftIndexBase s base by omega)]

/-- For every group whose doubled index fits, the arrays decode to the
two primed indices. This includes the whole first half, where they are used. -/
theorem Output.values {s : Sizes} {base : ℕ} {g : Fin (2^(s.h+1))} {m out : Memory w}
    (result : Output s base g m out) (hw : 0 < w) (fit : limit s base ≤ 2^w)
    (hle : g.val+1 < 2^(s.h+1)) :
    let pub := operands w s base
    PrimedCounter.GuessWord.value (storedBits out (pub 1) (s.h+2)) = 2*(g.val+1)-1 ∧
      PrimedCounter.GuessWord.value (storedBits out (pub 2) (s.h+2)) = 2*(g.val+1) := by
  obtain ⟨-,hl,hr,-,-,-⟩ := operand_values s base fit
  exact pair_values hw hle (by simpa only [stores,hl] using result.left)
    (by simpa only [stores,hr] using result.right)

/-- In the last group the mathematical even primed index is the next power
of two. Its low buffer is zero, its predecessor buffer is all ones, and
the scalar retains the final borrow. -/
theorem Output.last_group {s : Sizes} {base : ℕ} {g : Fin (2^(s.h+1))} {m out : Memory w}
    (result : Output s base g m out) (last : g.val+1 = 2^(s.h+1)) :
    (∀ j < s.h+2, out (leftIndexBase s base+j) = 1 ∧ out (rightIndexBase s base+j) = 0) ∧
      out (borrowAddr base) = 1 := by
  have hpow : 2*(g.val+1) = 2^(s.h+2) := by rw [last,pow_succ 2 (s.h+1),Nat.mul_comm]
  refine ⟨?_,by simpa [last,encodeBit] using result.borrow⟩
  intro j hj
  rw [result.left j hj,result.right j hj,hpow,Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow_of_ne hj.ne']
  simp [encodeBit,hj]

/-- The first-half buffers are precisely the two group fields queried in
the auxiliary input. Address arithmetic is the RAM's modular addition;
the scratch layout ensures that these additions do not wrap. -/
theorem Output.auxiliary_group_bits {s : Sizes} {base : ℕ} {g : Fin (2^(s.h+1))} {m out : Memory w}
    (result : Output s base g m out) (fit : limit s base ≤ 2^w) (i : Fin (2^s.h)) (same : g.val = i.val)
    (advice : CutSchedule.Bits s.advice) (exterior : ExponentTrace.Exterior s.h s.delta) :
    let pub := operands w s base
    let hdr := PairedChain.headers advice exterior i
    ∀ j : Fin (s.h+2),
      out (pub 1+(j.val : Word w)).val = encodeBit w (hdr (.group 0 j)) ∧
      out (pub 2+(j.val : Word w)).val = encodeBit w (hdr (.group 1 j)) := by
  dsimp only
  intro j
  have layout := layout_of_fit s base fit
  have hj := j.isLt
  obtain ⟨-,hl,hr,-,-,-⟩ := operand_values s base fit
  have hleft : (2*(g.val+1)-1) = (PairedChain.groupIndex i 0).val := by
    change 2*(g.val+1)-1 = 2*i.val+0+1
    omega
  have hright : 2*(g.val+1) = (PairedChain.groupIndex i 1).val := by
    change 2*(g.val+1) = 2*i.val+1+1
    omega
  rw [offset_val _ j.val (by have := layout.leftFit; omega),
    offset_val _ j.val (by have := layout.rightFit; omega),hl,hr,
    result.left j.val hj,result.right j.val hj,hleft,hright]
  exact ⟨congrArg (encodeBit w) (LiveHeader.testBit_wordBits _ j),congrArg (encodeBit w) (LiveHeader.testBit_wordBits _ j)⟩

private abbrev initId : StageId := ⟨13,by decide⟩
private abbrev digitId : StageId := ⟨14,by decide⟩
private abbrev descriptorId : StageId := ⟨15,by decide⟩

/-- Execute and link the two primed stages in their actual positions. The
frame in the returned output includes the final handoff at the reserved
stage tag. Every preceding width, flag, physical header and input digit
outside the writable regions retains its value. -/
theorem primed_prefix (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (g : Fin (2^(s.h+1)))
    (m : Memory w) (input : ∀ j < s.h+1, m (indexBase base+j) = encodeBit w ((g.val+1).testBit j)) :
    ∃ xs out, StagePrefix s base (some (⟨13,by decide⟩ : StageId)) m xs
      (some (⟨15,by decide⟩ : StageId)) out ∧ (∀ x ∈ xs, x.Good s) ∧
      Output s base g (LiveStageLink.transferMemory (Fin.ofNat _ base) (some (⟨15,by decide⟩ : StageId)) m) out := by
  let addr : Word w := Fin.ofNat _ base
  let pub := operands w s base
  obtain ⟨ri,hir,hia,him,hil,hip,-,hif⟩ := init_run s base m
  let x : StageTrace w := ⟨initId,9,[[]],ri⟩
  have hx : x.Exec s base m := ⟨hir,hia,hif⟩
  have gx : x.Good s := ⟨by change 9 ≤ 40; decide,rfl,hil,fun r h => (hip r h).1.le⟩
  let m₁ := LiveStageLink.transferMemory addr (some digitId) (initialized pub m)
  have hmem : x.finalMem addr m = m₁ := by
    change LiveStageLink.transferMemory addr (some digitId) (after m (eventLog ri)) = _
    rw [him]
  obtain ⟨ready,keep⟩ := handoff_ready s base fit (some digitId) m
  obtain ⟨rd,hdr,hda,result,hdl,hdp,-,hdf⟩ := digits_run s base fit g m₁ ready
    (fun j hj => (keep j hj).trans (input j hj))
  let y : StageTrace w := ⟨digitId,24,List.replicate (calls s .primedDigits) [],rd⟩
  have hy : y.Exec s base m₁ := ⟨hdr,hda,hdf⟩
  have gy : y.Good s := ⟨by change 24 ≤ 40; decide,rfl,hdl,fun r h => (hdp r h).1⟩
  have px : StagePrefix s base (some initId) m [x] (some digitId) m₁ := hmem ▸ StagePrefix.single hx
  have py : StagePrefix s base (some digitId) m₁ [y] (some descriptorId) (y.finalMem addr m₁) := StagePrefix.single hy
  refine ⟨[x,y],y.finalMem addr m₁,px.append py,?_,?_⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact gx
    · exact (List.mem_singleton.mp hz) ▸ gy
  · let raw := after m₁ (eventLog rd)
    change Output s base g m₁ raw at result
    change Output s base g (LiveStageLink.transferMemory addr (some descriptorId) m)
      (LiveStageLink.transferMemory addr (some descriptorId) raw)
    obtain ⟨-,hl,hr,hb,hbase,-⟩ := operand_values s base fit
    have va : addr.val = base := Nat.mod_eq_of_lt hbase
    have transfer (a : ℕ) (h : a ≠ base) (id : StageId) (mem : Memory w) :
        LiveStageLink.transferMemory addr (some id) mem a = mem a := by
      simp only [LiveStageLink.transferMemory,writeMemory,va,ite_eq_right h]
    have lessLeft : base < leftIndexBase s base := by
      simp only [leftIndexBase,populationAddr,highAddr,indexBase]; omega
    have lessRight : base < rightIndexBase s base := by unfold rightIndexBase; omega
    constructor
    · intro j hj
      rw [transfer _ (by omega)]
      exact result.left j hj
    · intro j hj
      rw [transfer _ (by omega)]
      exact result.right j hj
    · rw [transfer _ (by unfold borrowAddr; omega)]
      exact result.borrow
    · intro a ab al ar
      by_cases eq : a = base
      · rw [eq,← va,LiveStageLink.transferMemory_tag,LiveStageLink.transferMemory_tag]
      · rw [transfer a eq, transfer a eq,result.frame a ab al ar]
        change LiveStageLink.transferMemory addr (some digitId) (initialized pub m) a = m a
        rw [transfer a eq]
        simp only [pub,initialized,writeMemory,hb,hl,hr,ite_eq_right ab,
          ite_eq_right (show a ≠ rightIndexBase s base by omega),
          ite_eq_right (show a ≠ leftIndexBase s base by omega)]

end LiveHeaderProgram.PrimedStages

end VPVNP
end Computability
end OAI
