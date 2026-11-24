import OAI.Computability.VPVNP.CompressorChoiceRoot
import OAI.Computability.VPVNP.CompressorChoiceRAM

/-!
# Reading actual demand widths and preparing a compressor term

The local demand widths are contiguous words in external memory. Starting at
their base address, a fixed call reads each width once, accumulates the cleared
quadratic energy, and computes the repetition count by native bisection. The
next call uses that count for the actual motif's outer payload choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandPreparation

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w d : ℕ}

/-- The weights occupy the first public positions. The last position holds the
fixed squared block scale times the common denominator of the demand masses. -/
def readCoordinate (i : Fin d) : Flow 8 (d+1) :=
  .seq (.line (.read 3 2)) <|
  .seq (.line (.publicWord 4 i.castSucc)) <|
  .seq (.line (.binary .mul 5 3 3)) <|
  .seq (.line (.binary .mul 5 4 5)) <|
  .seq (.line (.binary .add 0 0 5)) (.line (.binary .add 2 2 6))

/-- Reading the fixed denominator closes the scan. -/
def scan : List (Fin d) → Flow 8 (d+1)
  | [] => .line (.publicWord 1 (Fin.last d))
  | i :: is => .seq (readCoordinate i) (scan is)

private def score (pub : Fin (d+1) → Word w) (mem : Memory w) (addr : Word w) :
    List (Fin d) → Word w
  | [] => 0
  | i :: is => pub i.castSucc * mem addr.val ^ 2 + score pub mem (addr + 1) is

private theorem score_ofFn (pub : Fin (d+1) → Word w) (mem : Memory w) (n : ℕ)
    (ids : Fin n → Fin d) (addr : Word w) :
    score pub mem addr (List.ofFn ids) = ∑ j, pub (ids j).castSucc * mem (addr + (j.val : Word w)).val ^ 2 := by
  induction n generalizing addr with
  | zero => simp [score]
  | succ n ih =>
    rw [List.ofFn_succ, score, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero,Nat.cast_zero,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show addr + 1 + (i.val : Word w) = addr + (i.val + 1 : Word w) by abel]

private def rowEvents (addr val : Word w) : List (Event w) := [.read addr val,.tick,.tick,.tick,.tick,.tick]

private theorem read_exec (pub : Fin (d+1) → Word w) (s : Word w) (mem : Memory w)
    (rs : Regs w 8) (one : rs 6 = 1) (i : Fin d) :
    ∃ out, Flow.Exec pub s (readCoordinate i) rs mem (rowEvents (rs 2) (mem (rs 2).val)) out mem ∧
      out 0 = rs 0 + pub i.castSucc * (mem (rs 2).val)^2 ∧ out 2 = rs 2 + 1 ∧ out 6 = 1 := by
  let a := Function.update rs 3 (mem (rs 2).val)
  let b := Function.update a 4 (pub i.castSucc)
  let c := Function.update b 5 (b 3 * b 3)
  let f := Function.update c 5 (c 4 * c 5)
  let g := Function.update f 0 (f 0 + f 5)
  let out := Function.update g 2 (g 2 + g 6)
  have h₁ : Flow.Exec pub s (.line (.read 3 2)) rs mem [.read (rs 2) (mem (rs 2).val)] a mem := .line rfl
  have h₂ : Flow.Exec pub s (.line (.publicWord 4 i.castSucc)) a mem [.tick] b mem := .line rfl
  have h₃ : Flow.Exec pub s (.line (.binary .mul 5 3 3)) b mem [.tick] c mem := .line rfl
  have h₄ : Flow.Exec pub s (.line (.binary .mul 5 4 5)) c mem [.tick] f mem := .line rfl
  have h₅ : Flow.Exec pub s (.line (.binary .add 0 0 5)) f mem [.tick] g mem := .line rfl
  have h₆ : Flow.Exec pub s (.line (.binary .add 2 2 6)) g mem [.tick] out mem := .line rfl
  exact ⟨out, .seq h₁ (.seq h₂ (.seq h₃ (.seq h₄ (.seq h₅ h₆)))), by
    simp (config := {decide := true}) [out,g,f,c,b,a,Function.update,one,pow_two]⟩

private theorem scan_exec (pub : Fin (d+1) → Word w) (s : Word w) (mem : Memory w)
    (is : List (Fin d)) (rs : Regs w 8) (one : rs 6 = 1) :
    ∃ es out, Flow.Exec pub s (scan is) rs mem es out mem ∧ choiceBits es = [] ∧
      es.length = 6 * is.length + 1 ∧ countProbes es = is.length ∧ after mem es = mem ∧
      out 0 = rs 0 + score pub mem (rs 2) is ∧ out 1 = pub (Fin.last d) := by
  induction is generalizing rs with
  | nil =>
    refine ⟨[.tick],Function.update rs 1 (pub (Fin.last d)),.line rfl,rfl,rfl,rfl,rfl,?_⟩
    simp (config := {decide := true}) [score,Function.update]
  | cons i is ih =>
    obtain ⟨mid,h₁,hs,ha,ho⟩ := read_exec pub s mem rs one i
    obtain ⟨es,out,h₂,hb,hl,hp,hmem,hv,hd⟩ := ih mid ho
    refine ⟨rowEvents _ _ ++ es,out,.seq h₁ h₂,?_,?_,?_,?_,?_,hd⟩
    · simpa [rowEvents,choiceBits] using hb
    · simp [rowEvents,hl]; omega
    · simp [rowEvents,countProbes,hp,Nat.add_comm]
    · exact hmem
    · rw [hv,hs,ha,score,add_assoc]

/-- Recover the demand vector in the fixed order from actual machine memory. -/
def demandAt {D : Type*} (order : Fin d ≃ D) (addr : Word w) (mem : Memory w) (e : D) : ℕ :=
  (mem (addr + ((order.symm e).val : Word w)).val).val

theorem demandAt_address {D : Type*} (order : Fin d ≃ D) (addr : Word w) (mem : Memory w)
    (fit : addr.val + d ≤ 2^w) (i : Fin d) :
    demandAt order addr mem (order i) = (mem (addr.val + i.val)).val := by
  simp only [demandAt,Equiv.symm_apply_apply,Fin.val_add,Fin.val_natCast,Nat.add_mod_mod]
  rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]

private theorem score_eq_energy {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ)
    (pub : Fin (d+1) → Word w) (mem : Memory w) (addr : Word w)
    (hw : ∀ i : Fin d, (pub i.castSucc).val = MotifAdmission.weight p (order i)) :
    score pub mem addr (List.finRange d) = (MotifAdmission.energy p (demandAt order addr mem) : Word w) := by
  rw [List.finRange,score_ofFn]
  simp only [MotifAdmission.energy, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply Fintype.sum_equiv order
  intro i
  simp [demandAt, ← hw]

/-- Shared deterministic prefix for the rounded-grid and repetition procedures.
Its first register holds the quadratic energy of the actual demand words. -/
def energyPrefix (d : ℕ) : Flow 8 (d+1) :=
  .seq (.line (.stateWord 2)) <|
  .seq (.line (.constant 0 0)) <|
  .seq (.line (.constant 6 1)) (scan (List.finRange d))

/-- After reading the fixed demand motif, bisection computes its copy count. -/
def repetitionCall (d : ℕ) : Flow 8 (d+1) := (energyPrefix d).seq RepetitionRAM.root

theorem energyPrefix_exec {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ)
    (pub : Fin (d+1) → Word w) (addr : Word w) (mem : Memory w) (rs : Regs w 8)
    (hw : ∀ i : Fin d, (pub i.castSucc).val = MotifAdmission.weight p (order i)) :
    ∃ es out, Flow.Exec pub addr (energyPrefix d) rs mem es out mem ∧ choiceBits es = [] ∧
      countProbes es = d ∧ after mem es = mem ∧ es.length = 6*d+4 ∧
      out 0 = (MotifAdmission.energy p (demandAt order addr mem) : Word w) ∧ out 1 = pub (Fin.last d) := by
  let a := Function.update rs 2 addr
  let b := Function.update a 0 0
  let c := Function.update b 6 (Fin.ofNat (2^w) 1)
  have init₁ : Flow.Exec pub addr (.line (.stateWord 2)) rs mem [.tick] a mem := .line rfl
  have init₂ : Flow.Exec pub addr (.line (.constant 0 0)) a mem [.tick] b mem := .line rfl
  have init₃ : Flow.Exec pub addr (.line (.constant 6 1)) b mem [.tick] c mem := .line rfl
  obtain ⟨es,out,h,hb,hl,hp,hm,he,hd⟩ := scan_exec pub addr mem (List.finRange d) c rfl
  refine ⟨.tick :: .tick :: .tick :: es,out,.seq init₁ (.seq init₂ (.seq init₃ h)),hb,by simpa [countProbes] using hp,hm,
    by simp [hl],?_,hd⟩
  rw [he,show c 0 = 0 by simp (config := {decide := true}) [c,b,Function.update], zero_add]
  exact score_eq_energy order p pub mem addr hw

private theorem noChoices_ticks (t : ℕ) : choiceBits (List.replicate t (.tick : Event w)) = [] := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [List.replicate_succ,choiceBits] using ih

theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem ticks_after (mem : Memory w) (t : ℕ) : after mem (List.replicate t .tick) = mem := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [List.replicate_succ, after, BurstRAM.update] using ih

private theorem noProbes_ticks (t : ℕ) : countProbes (List.replicate t (.tick : Event w)) = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [List.replicate_succ,countProbes] using ih

/-- The complete demand-to-repetition execution preserves memory, reads exactly
the demand coordinates, and consumes no branch choices. -/
theorem repetition_exec {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ)
    (L : ℕ) (hL : 0 < L) (pub : Fin (d+1) → Word w) (addr : Word w) (mem : Memory w) (rs : Regs w 8)
    (hw : ∀ i : Fin d, (pub i.castSucc).val = MotifAdmission.weight p (order i))
    (hden : (pub (Fin.last d)).val = L^2 * MotifAdmission.denominator p) (htwo : 2 < 2^w)
    (hsum : 2 * MotifAdmission.energy p (demandAt order addr mem) < 2^w)
    (hsq : (MotifAdmission.energy p (demandAt order addr mem))^2 * (L^2 * MotifAdmission.denominator p) < 2^w) :
    ∃ es out, Flow.Exec pub addr (repetitionCall d) rs mem es out mem ∧
      choiceBits es = [] ∧ countProbes es = d ∧ after mem es = mem ∧
      es.length ≤ 6*d + 7*(MotifAdmission.energy p (demandAt order addr mem)).size + 9 ∧
      (out 2).val = MotifAdmission.copies p (demandAt order addr mem) L := by
  obtain ⟨es,out,hr,hb,hp,hm,hl,he,hd⟩ := energyPrefix_exec order p pub addr mem rs hw
  let n := MotifAdmission.energy p (demandAt order addr mem)
  have he' : (out 0).val = n := by rw [he]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨t,last,hroot,ht,hval⟩ := RepetitionRAM.root_exec pub addr mem out n (L^2 * MotifAdmission.denominator p)
    he' (hd ▸ hden) (Nat.mul_pos (pow_pos hL _) (MotifAdmission.denominator_pos p)) htwo hsum hsq
  let ticks := List.replicate t (Event.tick : Event w)
  refine ⟨es ++ ticks,last,.seq hr hroot,?_,?_,?_,?_,hval⟩
  · simp [Flow.choiceBits_append,hb,ticks,noChoices_ticks]
  · simp [probes_append,hp,ticks,noProbes_ticks]
  · rw [show after mem (es ++ ticks) = after (after mem es) ticks by simp [after], hm]
    exact ticks_after mem t
  · simp only [List.length_append, hl, ticks, List.length_replicate]
    dsimp [n] at ht
    omega

/-- A fixed coefficient plus four logarithmic digits per demand-width bit
covers the midpoint sums, all squared comparisons, and the fixed public table. -/
theorem preparation_fit {D : Type*} [Fintype D] (p : D → ℚ) (L : ℕ) :
    ∃ K : ℕ, ∀ M (b : D → ℕ), (∀ i, b i ≤ M) →
      let energy := MotifAdmission.energy p b
      let den := L^2 * MotifAdmission.denominator p
      let modulus := 2^(K + 4*Nat.clog 2 (M+1))
      2 < modulus ∧ 2*energy < modulus ∧ energy^2*den < modulus ∧ den < modulus ∧
        ∀ i, MotifAdmission.weight p i < modulus := by
  let W := ∑ i, MotifAdmission.weight p i
  let den := L^2 * MotifAdmission.denominator p
  let C := 2 + 2*W + W^2*den + den + W
  refine ⟨C.size, fun M b hb => ?_⟩
  dsimp only
  let A := M + 1
  let E := MotifAdmission.energy p b
  have hE : E ≤ W * A^2 := MotifAdmission.energy_le p b A (fun i => (hb i).trans (Nat.le_succ _))
  have grow : A^2 ≤ A^4 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have fit (z c : ℕ) (hz : z ≤ c*A^4) (hc : c ≤ C) : z < 2^(C.size + 4*Nat.clog 2 A) := by
    rw [pow_add, Nat.mul_comm 4, pow_mul]
    apply hz.trans_lt
    apply mul_lt_mul_of_lt_of_le_of_pos_of_nonneg (hc.trans_lt (Nat.lt_size_self _))
      (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 4) (pow_pos (Nat.succ_pos _) _) (Nat.zero_le _)
  have fixed (c : ℕ) (hc : c ≤ C) : c < 2^(C.size + 4*Nat.clog 2 A) :=
    fit c c (Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _)) hc
  have hsum : 2*E ≤ (2*W)*A^4 := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hE.trans (Nat.mul_le_mul_left _ grow))
  have hsq : E^2*den ≤ (W^2*den)*A^4 :=
    (Nat.mul_le_mul_right den (Nat.pow_le_pow_left hE 2)).trans_eq (by ring)
  refine ⟨fixed 2 (by dsimp [C]; omega), fit _ _ hsum (by dsimp [C]; omega),
    fit _ _ hsq (by dsimp [C]; omega), fixed den (by dsimp [C]; omega), fun i => ?_⟩
  apply fixed
  exact (Finset.single_le_sum (f := MotifAdmission.weight p) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (show W ≤ C by dsimp [C]; omega)

/-- The fixed integer data stored at the public indices of the preparation program. -/
def publicWords {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (L : ℕ) (w : ℕ) :
    Fin (d+1) → Word w :=
  Fin.lastCases (Fin.ofNat _ (L^2 * MotifAdmission.denominator p))
    (fun i => Fin.ofNat _ (MotifAdmission.weight p (order i)))

/-- Instantiate the repetition-count worker with the ordered demand weights and the supplied
repetition parameter. -/
def repetitionMachine {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (L : ℕ) (w : ℕ) :=
  ((repetitionCall d).template (some 2)).instantiate w (publicWords order p L w)

/-- A deterministic structured derivation gives a complete native call at
every budget covering its executed instructions and the returning halt. -/
theorem execute_return {r k : ℕ} (code : Flow r k) (pub : Fin k → Word w) (result : Fin r)
    (state : Word w) (mem mem' : Memory w) (es : List (Event w)) (out : Regs w r)
    (hr : Flow.Exec pub state code (fun _ => 0) mem es out mem') (hbits : choiceBits es = [])
    (budget : ℕ) (hlen : es.length ≤ budget) :
    let machine := (code.template (some result)).instantiate w pub
    execute machine.program (budget+1) (machine.program.start state) mem [] = some ⟨es,some (out result)⟩ := by
  let machine := (code.template (some result)).instantiate w pub
  have hbad : machine.code code.rejectPC = .reject := by
    change ((code.template (some result)).code code.rejectPC).resize w = _
    rw [Flow.template_reject]; rfl
  have hout : machine.code code.exitPC = .returnState result := by
    change ((code.template (some result)).code code.exitPC).resize w = _
    rw [Flow.template_exit]; rfl
  have he := hr.execute (Flow.template_linked code (some result) pub) hbad (fun _ => 0) (budget-es.length+1) []
  simp only [hbits, List.nil_append] at he
  change execute machine.program (es.length + (budget-es.length+1)) (machine.program.start state) mem [] = _ at he
  change execute machine.program (budget+1) (machine.program.start state) mem [] = _
  rw [show budget+1 = es.length + (budget-es.length+1) by omega, he]
  change (execute machine.program (budget-es.length+1) ⟨code.exitPC,state,out,fun _ => 0⟩ mem' []).map _ = _
  simp only [execute,Machine.program,hout,Instr.run,ite_true,Option.map_some,Flow.prependEvents,List.append_nil]

/-- The first actual call returns the computed repetition word from the demand
array. Its event count is logarithmic in the largest demand width. -/
theorem repetition_native {D : Type*} [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (L : ℕ) (hL : 0 < L) :
    ∃ K : ℕ, ∀ M w, K + 4*Nat.clog 2 (M+1) ≤ w → ∀ (addr : Word w) (mem : Memory w),
      (∀ i, demandAt order addr mem i ≤ M) →
      let machine := repetitionMachine order p L w
      let b := demandAt order addr mem
      let budget := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 9
      ∃ es, execute machine.program (budget+1) (machine.program.start addr) mem [] =
        some ⟨es,some (Fin.ofNat _ (MotifAdmission.copies p b L))⟩ ∧ choiceBits es = [] ∧
        countProbes es = d ∧ after mem es = mem ∧ es.length ≤ budget := by
  obtain ⟨K,hK⟩ := preparation_fit p L
  refine ⟨K,fun M w hW addr mem hb => ?_⟩
  obtain ⟨ht,hs,hsq,hd,hweights⟩ := hK M (demandAt order addr mem) hb
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hW
  let pub := publicWords order p L w
  have hpub (i : Fin d) : (pub i.castSucc).val = MotifAdmission.weight p (order i) := by
    simp [pub, publicWords, Nat.mod_eq_of_lt ((hweights (order i)).trans_le hpow)]
  have hden : (pub (Fin.last d)).val = L^2 * MotifAdmission.denominator p := by
    simp only [pub,publicWords,Fin.lastCases_last]
    exact Nat.mod_eq_of_lt (hd.trans_le hpow)
  obtain ⟨es,out,hr,hb',hp,hm,hlen,ho⟩ := repetition_exec order p L hL pub addr mem (fun _ => 0)
    hpub hden (ht.trans_le hpow) (hs.trans_le hpow) (hsq.trans_le hpow)
  let budget := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 9
  have hbits := MotifAdmission.operand_bits_le (MotifAdmission.energy p (demandAt order addr mem))
    (∑ i, MotifAdmission.weight p i) M
    (MotifAdmission.energy_le p (demandAt order addr mem) (M+1) (fun i => (hb i).trans (Nat.le_succ M)))
  have hl : es.length ≤ budget := hlen.trans (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left 7 hbits) _) _)
  have hr' := execute_return (repetitionCall d) pub 2 addr mem mem es out hr hb' budget hl
  refine ⟨es,?_,hb',hp,hm,hl⟩
  have ho' : out 2 = Fin.ofNat _ (MotifAdmission.copies p (demandAt order addr mem) L) := by
    rw [← ho]; simp
  exact ho' ▸ hr'


open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- Two ordinary calls, with the repetition call's returned word and external
memory passed to the payload reader. The sole dynamic input to the first call
is the base address of the motif's demand widths. -/
def chooseFromDemand {n : ℕ} (demandOrder : Fin d ≃ D) (supplyOrder : Fin n ≃ S)
    (addr : BurstRAM.Word w) (mem : Memory w) (prepFuel : ℕ) (bits : List Bool) : Option (Report w) := do
  let first := repetitionMachine demandOrder p B.scale w
  let rep ← execute first.program prepFuel (first.program.start addr) mem []
  let u ← rep.result
  let factor := B.scale * B.radius.num.natAbs
  let den := MotifAdmission.denominator q
  let code := MotifChoiceRAM.choiceCall n factor den
  let weights := fun i => Fin.ofNat (2^w) (MotifAdmission.weight q (supplyOrder i) * B.radius.den^2)
  let next := (code.template none).instantiate w weights
  let fuel := 1 + (MotifChoiceRAM.prepareBounds n factor den).length + (n*(4*w+10)+3)
  execute next.program fuel (next.program.start u) (after mem rep.events) bits

theorem chooseFromDemand_iff {n : ℕ} (demandOrder : Fin d ≃ D) (supplyOrder : Fin n ≃ S)
    (hq : ∀ e, 0 < q e) :
    ∃ K : ℕ, ∀ M w, K + 4*Nat.clog 2 (M+1) ≤ w → ∀ (addr : BurstRAM.Word w) (mem : Memory w),
      (∀ i, demandAt demandOrder addr mem i ≤ M) →
      let demand := demandAt demandOrder addr mem
      let budget := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
      ∃ hw : outerCap B demand < 2^w, ∀ bits,
        (chooseFromDemand B demandOrder supplyOrder addr mem budget bits).isSome ↔
          ∃ v, (outerReader B supplyOrder hq demand w hw).read bits = some (v, []) := by
  obtain ⟨k₀,h₀⟩ := repetition_native demandOrder p B.scale B.scale_pos
  obtain ⟨k₁,h₁⟩ := MotifChoiceRAM.compiled_outer_choices B supplyOrder hq
  refine ⟨max k₀ k₁,fun M w hW addr mem hD => ?_⟩
  have a := le_max_left k₀ k₁
  have b := le_max_right k₀ k₁
  obtain ⟨es,hr,_,_,hm,_⟩ := h₀ M w (by omega) addr mem hD
  obtain ⟨hw,hchoose⟩ := h₁ M (demandAt demandOrder addr mem) hD w (by omega)
  refine ⟨hw,fun bits => ?_⟩
  simpa [chooseFromDemand, hr, hm, repetitions] using hchoose mem bits

end CompressorRecords.DemandPreparation

end VPVNP
end Computability
end OAI
