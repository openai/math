import OAI.Computability.VPVNP.CompressorChoiceRAM
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete

/-!
# Writing the selected motif payload to descriptor memory

The incoming persistent word gives the base of a contiguous descriptor. The
admission block receives the prepared registers of the motif choice reader.
After admission, the write block copies every supply coordinate, in order,
from its retained register to an external memory word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PayloadWrite

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open PrimedCounter.GuessWord MotifChoiceRAM
open scoped Fin.CommRing

variable {w n p : ℕ}

/-- Replace a contiguous slice of external memory with the given words. -/
def overlay (m : Memory w) (base : ℕ) (vs : List (Word w)) : Memory w :=
  fun a => if base ≤ a then vs[a-base]?.getD (m a) else m a

@[simp] theorem overlay_nil (m : Memory w) (base : ℕ) : overlay m base [] = m := by
  funext a
  simp [overlay]

theorem overlay_slot (m : Memory w) (base : ℕ) (v : Fin n → Word w) (i : Fin n) :
    overlay m base (List.ofFn v) (base+i.val) = v i := by
  simp [overlay, i.isLt]

theorem overlay_outside (m : Memory w) (base : ℕ) (v : Fin n → Word w) (a : ℕ)
    (h : a < base ∨ base+n ≤ a) : overlay m base (List.ofFn v) a = m a := by
  rcases h with h | h
  · simp [overlay, Nat.not_le.mpr h]
  · have hn : n ≤ a-base := by omega
    simp [overlay, List.getElem?_eq_none (by simpa using hn : (List.ofFn v).length ≤ a-base)]

private theorem overlay_cons (m : Memory w) (base : ℕ) (v : Word w) (vs : List (Word w))
    (h : base < 2^w) :
    overlay m base (v :: vs) = overlay (writeMemory m (base : Word w) v) (base+1) vs := by
  funext a
  have hb : (base : Word w).val = base := Nat.mod_eq_of_lt h
  rcases lt_trichotomy a base with ha | rfl | ha
  · simp [overlay, writeMemory, hb, ha.ne, Nat.not_le.mpr ha, show ¬ base+1 ≤ a by omega]
  · simp [overlay, writeMemory, hb]
  · have hs : a-base = (a-(base+1))+1 := by omega
    simp [overlay, writeMemory, hb, ha.ne', hs, ha.le, Nat.succ_le_of_lt ha]

/-- The cursor and its increment use registers 0 and 1. Each coordinate costs
one external write and one cursor increment. The terminal copy provides a
continuation even for a motif with empty supply. -/
def writeSlots : List (Fin n) → Flow (6+n) n
  | [] => .line (.copy (low n 0) (low n 0))
  | i :: rest =>
    .seq (.line (.write (low n 0) (slot i))) <|
    .seq (.line (.binary .add (low n 0) (low n 0) (low n 1))) (writeSlots rest)

/-- Instructions that take the descriptor base from persistent state and write every retained
supply coordinate to its slot. -/
def writePayload (n : ℕ) : Flow (6+n) n :=
  .seq (.line (.stateWord (low n 0))) <|
  .seq (.line (.constant (low n 1) 1)) (writeSlots (List.finRange n))

/-- A single linked table admits a motif vector and writes it at the persistent
base address. -/
def chooseAndStore (n : ℕ) : Flow (6+n) n := .seq (choosePayload n) (writePayload n)

private def storeEvents (base : ℕ) : List (Word w) → List (Event w)
  | [] => [.tick]
  | v :: vs => .write (base : Word w) v :: .tick :: storeEvents (base+1) vs

private theorem storeEvents_cost (base : ℕ) (vs : List (Word w)) :
    (storeEvents base vs).length = 2*vs.length+1 ∧ countProbes (storeEvents base vs) = vs.length ∧
      choiceBits (storeEvents base vs) = [] := by
  induction vs generalizing base with
  | nil => simp [storeEvents, countProbes, choiceBits]
  | cons v vs ih =>
    obtain ⟨hl,hp,hb⟩ := ih (base+1)
    simp [storeEvents, countProbes, choiceBits, hl, hp, hb]; omega

private theorem storeEvents_after (base : ℕ) (vs : List (Word w)) (m : Memory w)
    (h : base+vs.length ≤ 2^w) :
    after m (storeEvents base vs) = overlay m base vs := by
  induction vs generalizing base m with
  | nil => simp [storeEvents, after, update]
  | cons v vs ih =>
    simp only [List.length_cons] at h
    rw [overlay_cons m base v vs (by omega)]
    exact ih (base+1) _ (by omega)

private theorem low_ne : low n 1 ≠ low n 0 := fun h =>
  (by decide : (1 : Fin 6) ≠ 0) ((Fin.castAddEmb n).injective h)

private theorem writeSlots_exec (is : List (Fin n)) (base : ℕ) (v : Fin n → Word w)
    (pub : Fin n → Word w) (state : Word w) (rs : Regs w (6+n)) (m : Memory w)
    (haddr : rs (low n 0) = (base : Word w)) (hone : rs (low n 1) = 1)
    (hslot : ∀ i, rs (slot i) = v i) (hfit : base + is.length ≤ 2^w) :
    ∃ out, Flow.Exec pub state (writeSlots is) rs m (storeEvents base (is.map v)) out
      (overlay m base (is.map v)) := by
  induction is generalizing rs m base with
  | nil =>
    rw [List.map_nil, overlay_nil]
    exact ⟨_, .line rfl⟩
  | cons i is ih =>
    let m' := writeMemory m (base : Word w) (v i)
    let rs' := Function.update rs (low n 0) ((base+1 : ℕ) : Word w)
    have hwrite : Flow.Exec pub state (.line (.write (low n 0) (slot i))) rs m
        [.write (base : Word w) (v i)] rs m' := by
      apply Flow.Exec.line
      simp only [Op.effect,haddr,hslot,m']
    have hinc : Flow.Exec pub state (.line (.binary .add (low n 0) (low n 0) (low n 1)))
        rs m' [.tick] rs' m' := by
      apply Flow.Exec.line
      simp [Op.effect,BinaryOp.eval,haddr,hone,rs']
    simp only [List.length_cons] at hfit
    obtain ⟨out,hr⟩ := ih (base+1) rs' m' (by simp [rs']) (by simp [rs',hone])
      (fun j => by simp [rs',hslot]) (by omega)
    rw [List.map_cons,overlay_cons m base _ _ (by omega)]
    exact ⟨out,.seq hwrite (.seq hinc hr)⟩

/-- Exact events of the write block, including the two setup instructions. -/
def writeEvents (base : Word w) (v : Fin n → Word w) : List (Event w) :=
  .tick :: .tick :: storeEvents base.val (List.ofFn v)

theorem writePayload_exec (pub : Fin n → Word w) (base : Word w) (rs : Regs w (6+n))
    (m : Memory w) (v : Fin n → Word w) (hslot : ∀ i, rs (slot i) = v i)
    (hfit : base.val + n ≤ 2^w) :
    ∃ out, Flow.Exec pub base (writePayload n) rs m (writeEvents base v) out
      (overlay m base.val (List.ofFn v)) := by
  let q := Function.update rs (low n 0) base
  let r := Function.update q (low n 1) 1
  have ha : Flow.Exec pub base (.line (.stateWord (low n 0))) rs m [.tick] q m := .line rfl
  have hb : Flow.Exec pub base (.line (.constant (low n 1) 1)) q m [.tick] r m := .line rfl
  obtain ⟨out,ht⟩ := writeSlots_exec (List.finRange n) base.val v pub base r m
    (by simp [r,q,Ne.symm low_ne]) (by simp [r]) (fun i => by simp [r,q,hslot]) (by simpa using hfit)
  rw [← List.ofFn_eq_map] at ht
  exact ⟨out,.seq ha (.seq hb ht)⟩

theorem writeEvents_spec (base : Word w) (v : Fin n → Word w) (m : Memory w)
    (hfit : base.val + n ≤ 2^w) :
    (writeEvents base v).length = 2*n+3 ∧ countProbes (writeEvents base v) = n ∧
      choiceBits (writeEvents base v) = [] ∧ after m (writeEvents base v) = overlay m base.val (List.ofFn v) := by
  obtain ⟨hl,hp,hb⟩ := storeEvents_cost base.val (List.ofFn v)
  have hm := storeEvents_after base.val (List.ofFn v) m (by simpa using hfit)
  simp only [List.length_ofFn] at hl hp
  exact ⟨by simp [writeEvents,hl], hp, hb, hm⟩

/-- The arithmetic input contract of the admission reader. Zero repetitions
produce the unit descriptor, whose coordinates are all zero. -/
def Admitted (pub : Fin n → Word w) (rs : Regs w (6+n)) (v : Fin n → Word w) : Prop :=
  if rs (low n 2) = rs (low n 4) then ∀ i, v i = 0 else
    (∀ i, v i < rs (low n 3)) ∧
      (rs (low n 4)).val + score (List.finRange n) pub v < (rs (low n 5)).val

/-- Choice stream for the payload, empty on the forced branch and otherwise the ordered word
encoding of the supply vector. -/
def payloadBits (rs : Regs w (6+n)) (v : Fin n → Word w) : List Bool :=
  if rs (low n 2) = rs (low n 4) then [] else encoding (List.finRange n) v

/-- Number of admission steps for the forced branch or the full word-by-word vector choice, as
selected by the prepared registers. -/
def admissionSteps (rs : Regs w (6+n)) : ℕ :=
  if rs (low n 2) = rs (low n 4) then n+2 else n*(4*w+10)+2

private theorem admitted_prefix {M : Machine w p (6+n) n}
    {label : (choosePayload n).Label → Fin p} {stop bad : Fin p}
    (hl : Flow.Linked M (choosePayload n) label stop bad)
    (c : Config w p (6+n)) (hpc : c.pc = label (choosePayload n).entry)
    (v : Fin n → Word w) (ha : Admitted M.publicData c.reg v) :
    ∃ out es, Prefix M c es out ∧ es.length = admissionSteps c.reg ∧
      choiceBits es = payloadBits c.reg v ∧ out.pc = stop ∧
      (∀ i, out.reg (slot i) = v i) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  by_cases hu : c.reg (low n 2) = c.reg (low n 4)
  · obtain ⟨out,es,h,hl',hb,hpc',hz,hp,hs⟩ := choosePayload_unit hl c hpc hu
    have hz' : ∀ i, v i = 0 := by simpa [Admitted,hu] using ha
    exact ⟨out,es,h,by simpa [admissionSteps,hu] using hl',by simpa [payloadBits,hu] using hb,
      hpc',fun i => (hz i).trans (hz' i).symm,hp,hs⟩
  · simp only [Admitted,hu,↓reduceIte] at ha
    obtain ⟨hc,hs⟩ := ha
    simpa only [admissionSteps,payloadBits,hu,↓reduceIte] using choosePayload_vector hl c hpc hu v hc hs

private theorem prefix_memory {M : Machine w p (6+n) n} {c c' : Config w p (6+n)} {es}
    (h : Prefix M c es c') (m : Memory w) :
    countProbes es = 0 ∧ after m es = m := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | tick _ _ ih | choice _ _ ih => exact ih

private theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes,ih,Nat.add_assoc]

/-- Exact execution of the linked admission and emission code. It hands the
next native instruction its original bit suffix and the updated external
memory. The probe count is exactly the number of supply coordinates. -/
theorem chooseAndStore_execute {M : Machine w p (6+n) n}
    {label : (chooseAndStore n).Label → Fin p} {stop bad : Fin p}
    (hl : Flow.Linked M (chooseAndStore n) label stop bad) (hbad : M.code bad = .reject)
    (base : Word w) (priv : Word w → Word w) (rs : Regs w (6+n)) (m : Memory w)
    (v : Fin n → Word w) (ha : Admitted M.publicData rs v) (hfit : base.val+n ≤ 2^w) :
    ∃ es out, es.length = admissionSteps rs + (2*n+3) ∧ countProbes es = n ∧
      choiceBits es = payloadBits rs v ∧ after m es = overlay m base.val (List.ofFn v) ∧
      ∀ fuel bits, execute M.program (es.length + fuel)
        ⟨label (chooseAndStore n).entry,base,rs,priv⟩ m (payloadBits rs v ++ bits) =
        (execute M.program fuel ⟨stop,base,out,priv⟩ (overlay m base.val (List.ofFn v)) bits).map
          (Flow.prependEvents es) := by
  let c : Config w p (6+n) := ⟨label (chooseAndStore n).entry,base,rs,priv⟩
  obtain ⟨q,es,hpre,hlen,hbits,hpc,hslot,hpriv,hbase⟩ := admitted_prefix hl.seqLeft c rfl v ha
  have hq : q = ⟨label (.inr (writePayload n).entry),base,q.reg,priv⟩ := by
    cases q
    simp_all [c]
  obtain ⟨out,hstore⟩ := writePayload_exec M.publicData base q.reg m v hslot hfit
  obtain ⟨hslen,hsprobes,hsbits,hsm⟩ := writeEvents_spec base v m hfit
  obtain ⟨hprobes,hm⟩ := prefix_memory hpre m
  refine ⟨es ++ writeEvents base v,out,by simp [hlen,hslen,c],by simp [probes_append,hprobes,hsprobes],
    by simp [Flow.choiceBits_append,hbits,c,hsbits],?_,fun fuel bits => ?_⟩
  · rw [show after m (es ++ _) = after (after m es) (writeEvents base v) from List.foldl_append,hm,hsm]
  · have h₁ := hpre.execute ((writeEvents base v).length + fuel) m bits
    have h₂ := hstore.execute hl.seqRight hbad priv fuel bits
    rw [hsbits, List.nil_append] at h₂
    rw [hq] at h₁
    change choiceBits es = payloadBits rs v at hbits
    rw [hbits] at h₁
    rw [List.length_append, Nat.add_assoc, Nat.add_comm es.length, ← show c =
      ⟨label (chooseAndStore n).entry,base,rs,priv⟩ from rfl, h₁]
    erw [h₂, Option.map_map]
    congr 1
    funext r
    simp [Flow.prependEvents, List.append_assoc]

private def linear {r k : ℕ} : Flow r k → Prop
  | .line _ => True
  | .seq a b => linear a ∧ linear b
  | _ => False

private theorem linear_trace {r k : ℕ} {a : Flow r k} {pub : Fin k → Word w} {s rs m es out m'}
    (h : Flow.Exec pub s a rs m es out m') (ha : linear a) :
    es.length = a.length ∧ choiceBits es = [] := by
  induction h with
  | line he => exact ⟨rfl,Flow.line_choices he⟩
  | seq _ _ iha ihb =>
    obtain ⟨hla,hba⟩ := iha ha.1
    obtain ⟨hlb,hbb⟩ := ihb ha.2
    simp [Flow.length,Flow.choiceBits_append,hla,hlb,hba,hbb]
  | ifEqYes | ifEqNo | ifLtYes | ifLtNo | branchYes | branchNo | whileDone | whileStep => contradiction

private theorem writer_linear : linear (writePayload n) ∧ (writePayload n).length = 2*n+3 := by
  have slots (is : List (Fin n)) : linear (writeSlots is) ∧ (writeSlots is).length = 2*is.length+1 := by
    induction is with
    | nil => simp [writeSlots,linear,Flow.length]
    | cons i is ih => simp [writeSlots,linear,Flow.length,ih]; omega
  obtain ⟨hl,hlen⟩ := slots (List.finRange n)
  simp [writePayload,linear,Flow.length,hl,hlen]; omega

private theorem split_seq {r k : ℕ} {a b : Flow r k} {pub : Fin k → Word w} {s rs m es out m'}
    (h : Flow.Exec pub s (.seq a b) rs m es out m') :
    ∃ fs mid mem gs, Flow.Exec pub s a rs m fs mid mem ∧ Flow.Exec pub s b mid mem gs out m' ∧
      es = fs ++ gs := by
  cases h with
  | seq h₁ h₂ => exact ⟨_,_,_,_,h₁,h₂,rfl⟩

/-- Appending the writer preserves exactly the complete bit streams of the
standalone admission template. The additional budget is its exact native
step count. The assertion holds at every admission budget. -/
theorem template_store_iff (pub : Fin n → Word w) (base : Word w) (priv : Word w → Word w)
    (rs : Regs w (6+n)) (m : Memory w) (hfit : base.val+n ≤ 2^w) (fuel : ℕ) (bits : List Bool) :
    let code := chooseAndStore n
    let choice := choosePayload n
    (execute ((code.template none).instantiate w pub).program (fuel+(2*n+3))
      ⟨code.pc code.entry,base,rs,priv⟩ m bits).isSome ↔
    (execute ((choice.template none).instantiate w pub).program fuel
      ⟨choice.pc choice.entry,base,rs,priv⟩ m bits).isSome := by
  dsimp only
  let code := chooseAndStore n
  let choice := choosePayload n
  have whole := Flow.template_execute_iff code none pub base priv rs m (fuel+(2*n+3)) bits
  have part := Flow.template_execute_iff choice none pub base priv rs m fuel bits
  rw [Option.isSome_iff_exists, Option.isSome_iff_exists]
  constructor
  · rintro ⟨r,hr⟩
    obtain ⟨out,m',he,_,hlen,hbits⟩ := (whole r).mp hr
    obtain ⟨es,r₁,m₁,fs,left,right,hevents⟩ := split_seq (a := choice) (b := writePayload n) he
    obtain ⟨hfl,hfb⟩ := linear_trace right writer_linear.1
    rw [writer_linear.2] at hfl
    simp only [hevents,List.length_append,hfl] at hlen
    simp only [hevents,Flow.choiceBits_append,hfb,List.append_nil] at hbits
    exact ⟨⟨es,none⟩,(part _).mpr ⟨r₁,m₁,left,rfl,by dsimp; omega,hbits⟩⟩
  · rintro ⟨r,hr⟩
    obtain ⟨mid,mem,he,_,hlen,hbits⟩ := (part r).mp hr
    let v := fun i => mid (slot i)
    obtain ⟨out,hs⟩ := writePayload_exec pub base mid mem v (fun _ => rfl) hfit
    obtain ⟨hsl,_,hsb,_⟩ := writeEvents_spec base v mem hfit
    refine ⟨⟨r.events ++ writeEvents base v,none⟩,(whole _).mpr ⟨out,_,.seq he hs,rfl,?_,?_⟩⟩
    · simp only [List.length_append,hsl]; omega
    · simp [Flow.choiceBits_append,hsb,hbits]

end CompressorRecords.PayloadWrite

end VPVNP
end Computability
end OAI
