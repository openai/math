import OAI.Computability.VPVNP.CompressorPayloadWrite

/-!
# A native descriptor call from a stored repetition count

The persistent word gives the first payload address. Its predecessor holds
the repetition word computed for this motif. The call reads that word, sets
the bounds, admits the outer vector, and writes all of its supply coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PayloadWrite

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open MotifChoiceRAM
open scoped Fin.CommRing

variable {w n : ℕ}

/-- Read the repetition word immediately preceding the output slice. -/
def loadRepetition (n : ℕ) : Flow (6+n) n :=
  .seq (.line (.stateWord (low n 0))) <|
  .seq (.line (.constant (low n 1) 1)) <|
  .seq (.line (.binary .sub (low n 0) (low n 0) (low n 1))) (.line (.read (low n 2) (low n 0)))

/-- Native flow that reads a motif's stored repetition word, prepares the admission bounds,
chooses its payload, and writes it. -/
def storedCall (n factor denominator : ℕ) : Flow (6+n) n :=
  .seq ((loadRepetition n).seq (prepareBounds n factor denominator)) (chooseAndStore n)

private def loadEvents (base : Word w) (mem : Memory w) : List (Event w) :=
  [.tick,.tick,.tick,.read (base-1) (mem (base-1).val)]

private theorem load_exec (pub : Fin n → Word w) (base : Word w) (rs : Regs w (6+n)) (m : Memory w) :
    ∃ out, Flow.Exec pub base (loadRepetition n) rs m (loadEvents base m) out m ∧
      out (low n 2) = m (base-1).val := by
  let q := Function.update rs (low n 0) base
  let r := Function.update q (low n 1) 1
  let t := Function.update r (low n 0) (base-1)
  let z := Function.update t (low n 2) (m (base-1).val)
  have ha : Flow.Exec pub base (.line (.stateWord (low n 0))) rs m [.tick] q m := .line rfl
  have hb : Flow.Exec pub base (.line (.constant (low n 1) 1)) q m [.tick] r m := .line rfl
  have hc : Flow.Exec pub base (.line (.binary .sub (low n 0) (low n 0) (low n 1))) r m [.tick] t m := by
    apply Flow.Exec.line
    simp (config := { decide := true }) [Op.effect,BinaryOp.eval,r,q,t,Function.update]
  have hd : Flow.Exec pub base (.line (.read (low n 2) (low n 0))) t m
      [.read (base-1) (m (base-1).val)] z m := by
    apply Flow.Exec.line
    simp [Op.effect,t,z]
  exact ⟨z,.seq ha (.seq hb (.seq hc hd)),by simp [z]⟩

private theorem accept_linked {p r k : ℕ} {a : Flow r k} {M : Machine w p r k}
    {label : a.Label → Fin p} {stop bad : Fin p} (hl : Flow.Linked M a label stop bad)
    (hstop : M.code stop = .accept) (hbad : M.code bad = .reject)
    (state : Word w) (priv : Word w → Word w) (fuel : ℕ) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    execute M.program fuel ⟨label a.entry,state,rs,priv⟩ m bits =
      execute ((a.template none).instantiate w M.publicData).program fuel ⟨a.pc a.entry,state,rs,priv⟩ m bits := by
  let N := (a.template none).instantiate w M.publicData
  have hb : N.code a.rejectPC = .reject := by simp [N,Template.instantiate,Flow.template_reject,Instr.resize]
  have hs : N.code a.exitPC = .accept := by simp [N,Template.instantiate,Flow.template_exit,Instr.resize]
  have hn := Flow.template_linked a none M.publicData
  rw [hl.execute hbad state priv fuel a.entry rs m bits, hn.execute hb state priv fuel a.entry rs m bits]
  congr 1
  funext left regs mem bs
  cases left with
  | zero => rfl
  | succ left =>
    change execute M.program (left+1) ⟨stop,state,regs,priv⟩ mem bs =
      execute N.program (left+1) ⟨a.exitPC,state,regs,priv⟩ mem bs
    simp [execute,Machine.program,hstop,hs,Instr.run]

private theorem ticks_spec (t : ℕ) (m : Memory w) :
    let es := List.replicate t (.tick : Event w)
    choiceBits es = [] ∧ countProbes es = 0 ∧ after m es = m := by
  induction t with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ t ih =>
    rw [List.replicate_succ]
    exact ih

private theorem count_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes,ih,Nat.add_assoc]

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

private abbrev factor := B.scale * B.radius.num.natAbs
private abbrev denominator (_B : FixedBlock k a b P (realWidths p) (realWidths q) H H') :=
  MotifAdmission.denominator q

/-- Word-width instance of the stored-payload worker with the selected supply order and scaled
admission weights as public operands. -/
def storedMachine (order : Fin n ≃ S) (w : ℕ) :=
  ((storedCall n (factor B) (denominator B)).template none).instantiate w
    (fun i => Fin.ofNat (2^w) (MotifAdmission.weight q (order i) * B.radius.den^2))

/-- Fuel bound for reading the repetition count, preparing bounds, admitting coordinates, and
writing the payload. -/
def storedFuel (n w : ℕ) : ℕ :=
  (4 + (prepareBounds n (factor B) (denominator B)).length) + (n*(4*w+10)+3+(2*n+3))

/-- Only the word reader scales with the machine width. The threshold
preparation cost depends on the fixed binary motif coefficients. -/
theorem storedFuel_le (n w : ℕ) :
    storedFuel B n w ≤ n*(4*w+12) + 2*(B.scale*B.radius.num.natAbs).size +
      4*(MotifAdmission.denominator q).size + 20 := by
  have h := prepareBounds_length n (factor B) (denominator B)
  unfold storedFuel
  simp only [Nat.mul_add]
  dsimp only [factor,denominator] at h ⊢
  omega

private theorem outer_admitted (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) (demand : D → ℕ)
    (hw : outerCap B demand < 2^w) (rs : Regs w (6+n)) (weights : Fin n → BurstRAM.Word w)
    (hreps : (rs (low n 2)).val = repetitions B demand) (hzero : rs (low n 4) = 0)
    (hcap : (rs (low n 3)).val = outerCap B demand + 1)
    (hlimit : (rs (low n 5)).val =
      (repetitions B demand * B.scale * B.radius.num.natAbs)^2 * MotifAdmission.denominator q + 1)
    (hweights : ∀ i, (weights i).val = MotifAdmission.weight q (order i) * B.radius.den^2)
    (v : ↥(outerIndices B demand)) :
    let vec := fun i => (v.val (order i) : BurstRAM.Word w)
    Admitted weights rs vec ∧ payloadBits rs vec = (outerReader B order hq demand w hw).encode v := by
  dsimp only
  let vec := fun i => (v.val (order i) : BurstRAM.Word w)
  have ha := (mem_outerIndices_iff B hq _ _).mp v.property
  have hbox e := MotifAdmission.payload_le_cap q hq _ _ _ _ ha e
  have hval (i : Fin n) : (vec i).val = v.val (order i) := Nat.mod_eq_of_lt ((hbox _).trans_lt hw)
  by_cases hu : repetitions B demand = 0
  · have hz : rs (low n 2) = rs (low n 4) := by rw [hzero]; exact Fin.ext (hreps.trans hu)
    simp only [Admitted,payloadBits,hz,↓reduceIte]
    constructor
    · intro i
      have h := hbox (order i)
      simp only [MotifAdmission.payloadCap,hu,zero_mul,Nat.le_zero] at h
      rw [h]; rfl
    · apply Eq.symm
      apply List.length_eq_zero_iff.mp
      simp [outerReader_length,coordinateBits,hu]
  · have hz : rs (low n 2) ≠ rs (low n 4) := by
      intro he
      apply hu
      rw [← hreps,he,hzero]; rfl
    simp only [Admitted,payloadBits,hz,↓reduceIte]
    refine ⟨⟨fun i => ?_,?_⟩,?_⟩
    · apply Fin.lt_def.mpr
      change (vec i).val < _
      rw [hval,hcap]; exact Nat.lt_succ_of_le (hbox _)
    · change (rs (low n 4)).val + score (List.finRange n) weights vec < _
      rw [hzero,hlimit,full_score order q B.radius weights vec hweights]
      simpa only [Fin.val_zero,Nat.zero_add,hval,Equiv.apply_symm_apply,Nat.lt_succ_iff] using
        (of_decide_eq_true ha)
    · have hr : (outerReader B order hq demand w hw).read ((outerReader B order hq demand w hw).encode v) =
          some (v,[]) := (ChoiceReader.read_iff ..).mpr (by simp)
      have he := (read_outer_iff B order hq demand w hw _ [] v).mp hr
      rw [he,List.append_nil,full_encoding,show coordinateBits B demand w = w from ite_eq_right hu]
      rfl

private theorem setup_exec (u factor den : ℕ) (pub : Fin n → BurstRAM.Word w) (base : BurstRAM.Word w)
    (m : Memory w) (hrep : (m (base-1).val).val = u)
    (hcap : u*factor*den+1 < 2^w) (hlimit : (u*factor)^2*den+1 < 2^w) :
    let prep := prepareBounds n factor den
    ∃ es rs, Flow.Exec pub base ((loadRepetition n).seq prep) (fun _ => 0) m es rs m ∧
      es.length = 4+prep.length ∧ choiceBits es = [] ∧ countProbes es = 1 ∧ after m es = m ∧
      (rs (low n 2)).val = u ∧ (rs (low n 3)).val = u*factor*den+1 ∧ rs (low n 4) = 0 ∧
      (rs (low n 5)).val = (u*factor)^2*den+1 := by
  let prep := prepareBounds n factor den
  obtain ⟨mid,hload,hu⟩ := load_exec pub base (fun _ => 0) m
  obtain ⟨out,hr,_,_,h2,h3,h4,h5,_⟩ := prepareBounds_exec factor den u pub base m mid
    (by rw [hu,hrep]) hcap hlimit
  obtain ⟨htbits,htp,htm⟩ := ticks_spec prep.length m
  let ticks := List.replicate prep.length (.tick : Event w)
  have hm : after m (loadEvents base m) = m := rfl
  refine ⟨loadEvents base m ++ ticks,out,.seq hload hr,?_,?_,?_,?_,by rw [h2,hu,hrep],h3,h4,h5⟩
  · simp [loadEvents,ticks,prep]; omega
  · rw [Flow.choiceBits_append,htbits]; rfl
  · rw [count_append,htp]; rfl
  · rw [show after m (loadEvents base m ++ ticks) = after (after m (loadEvents base m)) ticks from
      List.foldl_append,hm,htm]

/-- Starting at reset with the descriptor base as persistent state, the
accepted streams are precisely the motif's outer encodings. On each stream
the output memory contains the chosen coordinates and agrees elsewhere with
the input. The call reads the repetition word once and writes each supply coordinate once. -/
theorem stored_outer_paths (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) :
    ∃ K : ℕ, ∀ M (demand : D → ℕ), (∀ i, demand i ≤ M) → ∀ w,
      K + 2*Nat.clog 2 (M+1) ≤ w → ∀ (base : BurstRAM.Word w) (m : Memory w), base.val+n ≤ 2^w →
      (m (base-1).val).val = repetitions B demand →
      ∃ hw : outerCap B demand < 2^w,
        (∀ bits, (execute (storedMachine B order w).program (storedFuel B n w)
          ((storedMachine B order w).program.start base) m bits).isSome ↔
          ∃ v, (outerReader B order hq demand w hw).read bits = some (v,[])) ∧
        ∀ v : ↥(outerIndices B demand), ∃ es,
          execute (storedMachine B order w).program (storedFuel B n w)
            ((storedMachine B order w).program.start base) m ((outerReader B order hq demand w hw).encode v) =
              some ⟨es,none⟩ ∧ after m es = overlay m base.val (List.ofFn fun i => (v.val (order i) : BurstRAM.Word w)) ∧
          countProbes es = n+1 ∧ es.length < storedFuel B n w ∧
          choiceBits es = (outerReader B order hq demand w hw).encode v := by
  obtain ⟨K,hK⟩ := native_word_fit p q B.scale B.scale_pos B.radius
  refine ⟨K,fun M demand hD w hW base m haddr hu => ?_⟩
  obtain ⟨_,hc,hl,hs,ht⟩ := hK M demand hD
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hW
  let u := repetitions B demand
  let den := denominator B
  let fac := factor B
  let code := storedCall n fac den
  let machine := storedMachine B order w
  let pub := machine.publicData
  let prep := prepareBounds n fac den
  let chooseFuel := n*(4*w+10)+3
  let remaining := chooseFuel+(2*n+3)
  have hpub i : (pub i).val = MotifAdmission.weight q (order i) * B.radius.den^2 :=
    Nat.mod_eq_of_lt ((ht _).trans_le hpow)
  have hcap : u*fac*den+1 < 2^w := by
    simpa [u,fac,factor,den,denominator,MotifAdmission.payloadCap,repetitions,Nat.mul_assoc] using hc.trans_le hpow
  have hlim : (u*fac)^2*den+1 < 2^w := by
    simpa [u,fac,factor,den,denominator,repetitions,Nat.mul_assoc] using hl.trans_le hpow
  obtain ⟨pre,rs,hpre,hplen,hpbits,hpp,hpm,h2,h3,h4,h5⟩ := setup_exec u fac den pub base m hu hcap hlim
  have hbox : (rs (low n 3)).val = outerCap B demand+1 := by
    simpa [u,fac,factor,den,denominator,MotifAdmission.payloadCap,Nat.mul_assoc] using h3
  have hbound : (rs (low n 5)).val =
      (u*B.scale*B.radius.num.natAbs)^2*MotifAdmission.denominator q+1 := by
    simpa [fac,factor,den,denominator,Nat.mul_assoc] using h5
  have hw : outerCap B demand < 2^w := by have hh := (rs (low n 3)).isLt; omega
  have hscore : score (List.finRange n) pub (fun _ => rs (low n 3)) < 2^w := by
    rw [full_score order q B.radius _ _ hpub]
    simpa [hbox,outerCap,repetitions] using hs.trans_le hpow
  have link := Flow.template_linked (w := w) code none pub
  have hstop : machine.code code.exitPC = .accept := by
    change ((code.template none).code code.exitPC).resize w = _
    rw [Flow.template_exit]; rfl
  have hbad : machine.code code.rejectPC = .reject := by
    change ((code.template none).code code.rejectPC).resize w = _
    rw [Flow.template_reject]; rfl
  let mid : Config w (code.length+2) (6+n) := ⟨code.pc (.inr (chooseAndStore n).entry),base,rs,fun _ => 0⟩
  have start (bits : List Bool) :
      execute machine.program (storedFuel B n w) (machine.program.start base) m bits =
        (execute machine.program remaining mid m bits).map (Flow.prependEvents pre) := by
    have hr := hpre.execute link.seqLeft hbad (fun _ => 0) remaining bits
    rw [hpbits,List.nil_append,hplen] at hr
    exact hr
  refine ⟨hw,?_,fun v => ?_⟩
  · intro bits
    rw [start,Option.isSome_map]
    have hlift := accept_linked link.seqRight hstop hbad base (fun _ => 0) remaining rs m bits
    change execute machine.program remaining mid m bits = _ at hlift
    rw [hlift]
    refine (template_store_iff pub base (fun _ => 0) rs m haddr chooseFuel bits).trans ?_
    let choice := choosePayload n
    let ch := (choice.template none).instantiate w pub
    have ca : ch.code choice.exitPC = .accept := by simp [ch,Template.instantiate,Flow.template_exit,Instr.resize]
    have cb : ch.code choice.rejectPC = .reject := by simp [ch,Template.instantiate,Flow.template_reject,Instr.resize]
    exact choosePayload_execute_iff B order hq demand (Flow.template_linked choice none pub) ca cb
      ⟨choice.pc choice.entry,base,rs,fun _ => 0⟩ rfl hpub h2 hbox (by simp [h4]) hbound hscore m bits
  · let vec := fun i => (v.val (order i) : BurstRAM.Word w)
    let bits := (outerReader B order hq demand w hw).encode v
    obtain ⟨ha,hb⟩ := outer_admitted B order hq demand hw rs pub h2 h4 hbox hbound hpub v
    obtain ⟨es,out,hlen,hprobes,hbits,hm,hfinish⟩ :=
      chooseAndStore_execute link.seqRight hbad base (fun _ => 0) rs m vec ha haddr
    have hsmall : admissionSteps rs ≤ n*(4*w+10)+2 := by
      have h := Nat.le_mul_of_pos_right n (by omega : 0 < 4*w+10)
      unfold admissionSteps
      split <;> omega
    have he : es.length < remaining := by dsimp [remaining,chooseFuel]; omega
    let extra := remaining-es.length-1
    have hrem : es.length+(extra+1) = remaining := by dsimp [extra]; omega
    have hr := hfinish (extra+1) []
    rw [hrem,List.append_nil,hb] at hr
    change execute machine.program remaining mid m bits =
      (execute machine.program (extra+1) ⟨code.exitPC,base,out,fun _ => 0⟩ _ []).map _ at hr
    simp only [execute,Machine.program,hstop,Instr.run,ite_true,Option.map_some,Flow.prependEvents,List.append_nil] at hr
    change execute machine.program remaining mid m bits = some ⟨es,none⟩ at hr
    refine ⟨pre++es,?_,?_,?_,?_,?_⟩
    · rw [start,hr]; rfl
    · rw [show after m (pre++es) = after (after m pre) es from List.foldl_append,hpm,hm]
    · rw [count_append,hpp,hprobes,Nat.add_comm]
    · change (pre++es).length < (4+prep.length)+remaining
      rw [List.length_append,hplen]; exact Nat.add_lt_add_left he _
    · rw [Flow.choiceBits_append,hpbits,List.nil_append,hbits,hb]

end CompressorRecords.PayloadWrite

end VPVNP
end Computability
end OAI
