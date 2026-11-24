import OAI.Computability.VPVNP.LiveEvaluatorAdviceBanks
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackStep
import OAI.Computability.VPVNP.RAMSuccessor
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Native sweeps for packing the evaluator's bit banks

Each output row begins with one reset call. Further calls install the row's
occupied source bits and leave its padding zero. The resulting memory is
specified at every address. Every nonempty sweep has a single accepting
branch stream and incurs at most four calls-plus-probes per cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM
open BurstRAM.PrivateRAM (BinaryOp)
open scoped Fin.CommRing

variable {w : ℕ}

/-- The cursor for an unfinished call, or the halted control after all rows. -/
def packControl (w count i : ℕ) : Option (Word w) :=
  if i = count then none else some (Fin.ofNat (2^w) i)

/-- The reported memory, call count, clock and total probe cost of a native
deterministic scan, with an exact characterization on arbitrary branch streams. -/
theorem deterministic_scan {C : Type*} (P : Program w C) (fuel count bound : ℕ)
    (inv : ℕ → Memory w → Prop)
    (step : ∀ i < count, ∀ m, inv i m → ∃ es,
      (∀ bs, execute P fuel (P.start (Fin.ofNat (2^w) i)) m bs =
        if bs = [] then some ⟨es, packControl w count (i+1)⟩ else none) ∧
      inv (i+1) (after m es) ∧ countProbes es ≤ bound)
    (n i : ℕ) (hn : i+n = count) (m : Memory w) (hi : inv i m) :
    ∃ reports, inv count (after m (eventLog reports)) ∧ reports.length = n ∧
      RAMBuckets.cost Report.probes reports ≤ (1+bound)*n ∧
      (∀ r ∈ reports, r.probes ≤ bound ∧ r.events.length < fuel) ∧
      ∀ bits rs, (runSegment P fuel (packControl w count i) m bits = some rs ∧
        endState (packControl w count i) rs = none) ↔ bits = List.replicate n [] ∧ rs = reports := by
  induction n generalizing i m with
  | zero =>
    simp only [Nat.add_zero] at hn
    subst i
    refine ⟨[], hi, rfl, by simp [RAMBuckets.cost], by simp, ?_⟩
    intro bits rs
    cases bits <;> cases rs <;> simp [packControl, runSegment, endState]
  | succ n ih =>
    have hlt : i < count := by omega
    obtain ⟨es, hrun, hnext, hprobes⟩ := step i hlt m hi
    let r : Report w := ⟨es, packControl w count (i+1)⟩
    have he : execute P fuel (P.start (Fin.ofNat (2^w) i)) m [] = some r := by simpa [r] using hrun []
    have hclock := (execute_spec he).1.length_lt
    obtain ⟨tail, hm, hl, hc, hcaps, hu⟩ := ih (i+1) (by omega) (after m es) hnext
    refine ⟨r :: tail, ?_, by simp [hl], ?_, ?_, ?_⟩
    · simpa only [eventLog, List.flatMap_cons, after, List.foldl_append, r] using hm
    · change 1 + countProbes es + _ ≤ _
      rw [Nat.mul_succ]
      omega
    · rw [List.forall_mem_cons]
      exact ⟨⟨hprobes, hclock⟩, hcaps⟩
    · intro bits rs
      rw [packControl, ite_eq_right hlt.ne]
      cases bits with
      | nil => cases rs <;> simp [runSegment, endState, List.replicate_succ]
      | cons bs more =>
        by_cases hb : bs = []
        · subst bs
          rw [runSegment, he]
          simp only [Option.map_eq_some_iff, List.replicate_succ, List.cons.injEq, true_and]
          constructor
          · rintro ⟨⟨rest, hr, rfl⟩, hhalt⟩
            obtain ⟨hbits, rfl⟩ := (hu more rest).mp ⟨hr, hhalt⟩
            exact ⟨hbits, rfl⟩
          · rintro ⟨hbits, rfl⟩
            obtain ⟨hr, hhalt⟩ := (hu more tail).mpr ⟨hbits, rfl⟩
            exact ⟨⟨tail, hr, rfl⟩, hhalt⟩
        · rw [runSegment, hrun bs, ite_eq_right hb]
          simp [List.replicate_succ, hb]


/-- Each row is overwritten when its reset call occurs. Subsequent calls in
the same row expose one more little-endian bit, up to the fixed field width. -/
def packMemory (pub : Fin 5 → Word w) (raw : List Bool) (original : Memory w) (i : ℕ) : Memory w :=
  fun a =>
    let base := (pub 1).val
    let fw := (pub 2).val
    let j := a-base
    if base ≤ a ∧ j < (pub 4).val ∧ j*(fw+1) < i then
      packedPrefix w fw raw j (min fw (i-(j*(fw+1)+1)))
    else original a

/-- Number of native calls, including the initial reset of every row. -/
def packCalls (pub : Fin 5 → Word w) : ℕ := (pub 4).val*((pub 2).val+1)

/-- The public geometry and the word bounds used for packing. Addresses are
ordinary naturals until they are shown to fit in a native word. -/
structure PackLayout (pub : Fin 5 → Word w) (raw : List Bool) : Prop where
  width : 2 ≤ w
  fieldWidth : (pub 2).val ≤ w
  rawLength : (pub 3).val = raw.length
  cursorFit : packCalls pub < 2^w
  srcFit : (pub 0).val + raw.length ≤ 2^w
  dstFit : (pub 1).val + (pub 4).val ≤ 2^w
  disjoint : (pub 1).val + (pub 4).val ≤ (pub 0).val ∨ (pub 0).val + raw.length ≤ (pub 1).val

/-- Source advice occupies one Boolean word at each actual bit address. -/
def PackSource (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) : Prop :=
  ∀ k < raw.length, m ((pub 0).val+k) = PrimedInputRAM.encodeBit w (raw[k]?.getD false)

theorem packMemory_zero (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) :
    packMemory pub raw m 0 = m := by
  funext a
  simp [packMemory]

theorem packMemory_outside (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) (i a : ℕ)
    (ha : a < (pub 1).val ∨ (pub 1).val+(pub 4).val ≤ a) :
    packMemory pub raw m i a = m a := by
  have hn : ¬((pub 1).val ≤ a ∧ a-(pub 1).val < (pub 4).val ∧
    (a-(pub 1).val)*((pub 2).val+1) < i) := by omega
  exact ite_eq_right hn

theorem packMemory_source (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (L : PackLayout pub raw) (src : PackSource pub raw m) (i : ℕ) :
    PackSource pub raw (packMemory pub raw m i) := by
  intro k hk
  rw [packMemory_outside]
  · exact src k hk
  · rcases L.disjoint with h | h <;> omega

theorem packMemory_row (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) (i j : ℕ)
    (hj : j < (pub 4).val) :
    packMemory pub raw m i ((pub 1).val+j) =
      if j*((pub 2).val+1) < i then
        packedPrefix w (pub 2).val raw j (min (pub 2).val (i-(j*((pub 2).val+1)+1)))
      else m ((pub 1).val+j) := by
  simp [packMemory, hj]

/-- At the end all row words are fully written, even if padding calls have
been needed after the end of the raw advice. -/
theorem packMemory_full (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) (j : ℕ)
    (hj : j < (pub 4).val) :
    packMemory pub raw m (packCalls pub) ((pub 1).val+j) =
      packedPrefix w (pub 2).val raw j (pub 2).val := by
  have h := Nat.mul_le_mul_right ((pub 2).val+1) hj
  rw [Nat.succ_mul] at h
  rw [packMemory_row, packCalls, ite_eq_left (by omega), min_eq_left (by omega)]
  exact hj

private theorem packMemory_succ_other (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (i j c a : ℕ) (hij : i = j*((pub 2).val+1)+c) (hc : c ≤ (pub 2).val)
    (ha : a ≠ (pub 1).val+j) :
    packMemory pub raw m (i+1) a = packMemory pub raw m i a := by
  by_cases hOut : a < (pub 1).val ∨ (pub 1).val+(pub 4).val ≤ a
  · rw [packMemory_outside _ _ _ _ _ hOut, packMemory_outside _ _ _ _ _ hOut]
  let r := a-(pub 1).val
  have har : a = (pub 1).val+r := by dsimp [r]; omega
  have hr : r < (pub 4).val := by dsimp [r]; omega
  have hne : r ≠ j := by intro he; rw [he] at har; contradiction
  rw [har, packMemory_row _ _ _ _ _ hr, packMemory_row _ _ _ _ _ hr]
  rcases lt_or_gt_of_ne hne with h | h
  · have hx := Nat.mul_le_mul_right ((pub 2).val+1) h
    rw [Nat.succ_mul] at hx
    rw [ite_eq_left (by omega), ite_eq_left (by omega), min_eq_left (by omega), min_eq_left (by omega)]
  · have hx := Nat.mul_le_mul_right ((pub 2).val+1) h
    rw [Nat.succ_mul] at hx
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem packMemory_current (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w)
    (j c : ℕ) (hj : j < (pub 4).val) (hc : c ≤ (pub 2).val) :
    packMemory pub raw m (j*((pub 2).val+1)+c+1) ((pub 1).val+j) =
      packedPrefix w (pub 2).val raw j c := by
  rw [packMemory_row _ _ _ _ _ hj, ite_eq_left (by omega), min_eq_right (by omega)]
  congr 1
  omega


private theorem pack_stride {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw) :
    (stride pub).val = (pub 2).val+1 := by
  apply Fin.val_add_one_of_lt'
  have h := L.fieldWidth
  have h₁ := L.width
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le h₁
  have hp := Nat.lt_two_pow_self (n := u)
  have hh : w+1 < 2^w := by rw [hu, pow_add]; omega
  omega

private theorem pack_total {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw) :
    (total pub).val = packCalls pub := by
  rw [total, Fin.val_mul, pack_stride L]
  exact Nat.mod_eq_of_lt L.cursorFit

private theorem packCoordinates {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (i : ℕ) (hi : i < packCalls pub) :
    let st := Fin.ofNat (2^w) i
    let j := (row pub st).val
    let c := (column pub st).val
    i = j*((pub 2).val+1)+c ∧ c ≤ (pub 2).val ∧ j < (pub 4).val ∧
      (dst pub st).val = (pub 1).val+j := by
  intro st j c
  have hst : st.val = i := Nat.mod_eq_of_lt (hi.trans L.cursorFit)
  have hj : j = i/((pub 2).val+1) := by
    change (st.val / (stride pub).val) % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt st.isLt), hst, pack_stride L]
  have hc : c = i%((pub 2).val+1) := by
    change (st.val % (stride pub).val) % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt st.isLt), hst, pack_stride L]
  have hjlt : j < (pub 4).val := by
    rw [hj, Nat.div_lt_iff_lt_mul (by omega)]
    exact hi
  refine ⟨?_, ?_, hjlt, ?_⟩
  · rw [hj, hc, Nat.div_add_mod']
  · rw [hc]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
  · change ((pub 1).val+j) % 2^w = _
    have := L.dstFit
    exact Nat.mod_eq_of_lt (by omega)

/-- On a nonreset column the live source offset is the ordinary row-major
bit index. All arithmetic in the native registers stays within the modulus. -/
private theorem pack_index {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (i : ℕ) (hi : i < packCalls pub) {k : ℕ}
    (hk : (column pub (Fin.ofNat (2^w) i)).val = k+1) :
    let st := Fin.ofNat (2^w) i
    let j := (row pub st).val
    (column pub st - 1) = Fin.ofNat (2^w) k ∧ (index pub st).val = j*(pub 2).val+k := by
  intro st j
  have ⟨he, _, _, _⟩ := packCoordinates L i hi
  change i = j*((pub 2).val+1)+(column pub st).val at he
  have hf := hi.trans L.cursorFit
  have hu : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := L.width; omega))
  have hle : (1 : Word w) ≤ column pub st := by rw [Fin.le_def, hu, hk]; omega
  have hv : (column pub st - 1).val = k := by rw [Fin.sub_val_of_le hle, hu, hk]; omega
  have hkj : k < 2^w := by have := (column pub st).isLt; rw [hk] at this; omega
  have hsub : column pub st-1 = Fin.ofNat (2^w) k := Fin.ext (hv.trans (Nat.mod_eq_of_lt hkj).symm)
  refine ⟨hsub, ?_⟩
  rw [Nat.mul_add, Nat.mul_one, hk] at he
  change ((j*(pub 2).val) % 2^w + (column pub st-1).val) % 2^w = _
  rw [Nat.mod_eq_of_lt (by omega : j*(pub 2).val < 2^w), hv, Nat.mod_eq_of_lt (by omega)]

private theorem pack_src {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (st : Word w) (h : index pub st < pub 3) :
    (src pub st).val = (pub 0).val+(index pub st).val := by
  change ((pub 0).val+(index pub st).val) % 2^w = _
  change (index pub st).val < (pub 3).val at h
  rw [L.rawLength] at h
  have := L.srcFit
  exact Nat.mod_eq_of_lt (by omega)

/-- The natural row-prefix invariant advances exactly once for the native
reset, active bit, or padding call. -/
theorem packMemory_step {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) (i : ℕ) (hi : i < packCalls pub) :
    stepMemory pub (Fin.ofNat (2^w) i) (packMemory pub raw m i) = packMemory pub raw m (i+1) := by
  let st := Fin.ofNat (2^w) i
  let j := (row pub st).val
  let c := (column pub st).val
  obtain ⟨he, hc, hj, hd⟩ := packCoordinates L i hi
  change i = j*((pub 2).val+1)+c at he
  change c ≤ (pub 2).val at hc
  change j < (pub 4).val at hj
  change (dst pub st).val = (pub 1).val+j at hd
  change stepMemory pub st _ = _
  funext a
  by_cases ha : a = (pub 1).val+j
  · subst a
    have hpost := packMemory_current pub raw m j c hj hc
    rw [← he] at hpost
    rw [hpost]
    cases hx : c with
    | zero =>
      have hz : column pub st = 0 := Fin.ext hx
      simp [stepMemory, hz, writeMemory, hd, packedPrefix_zero]
    | succ k =>
      have hz : column pub st ≠ 0 := by
        intro h
        have hh := congrArg Fin.val h
        change c = 0 at hh
        omega
      have ⟨hsub, hidx⟩ := pack_index L i hi hx
      have hk : k < (pub 2).val := by omega
      have hprev := packMemory_current pub raw m j k hj (by omega)
      rw [show j*((pub 2).val+1)+k+1 = i by omega] at hprev
      rw [stepMemory, ite_eq_right hz]
      by_cases hactive : index pub st < pub 3
      · have hsrc := pack_src L st hactive
        have hidx' : j*(pub 2).val+k < raw.length := by
          change (index pub st).val < (pub 3).val at hactive
          rwa [L.rawLength, hidx] at hactive
        rw [ite_eq_left hactive, writeMemory, hd, ite_eq_left rfl]
        unfold packedValue
        rw [hd, hprev, hsrc, hidx, packMemory_source pub raw m L hs i _ hidx', hsub]
        exact packedPrefix_succ w _ raw j k hk L.fieldWidth
      · rw [ite_eq_right hactive, hprev, packedPrefix_skip]
        change ¬(index pub st).val < (pub 3).val at hactive
        rw [L.rawLength, hidx] at hactive
        exact Nat.le_of_not_gt hactive
  · rw [packMemory_succ_other pub raw m i j c a he hc ha]
    have hne : a ≠ (dst pub st).val := hd ▸ ha
    unfold stepMemory
    split_ifs <;> simp [writeMemory, hne]


/-- The valid natural cursor satisfies both native guards, and its footer
publishes the next ordinary cursor unless the complete scan has ended. -/
theorem packStep_guards {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) (i : ℕ) (hi : i < packCalls pub) :
    let st := Fin.ofNat (2^w) i
    st < total pub ∧
      (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w)) ∧
      (stepReport pub st m).result = packControl w (packCalls pub) (i+1) := by
  intro st
  have hst : st.val = i := Nat.mod_eq_of_lt (hi.trans L.cursorFit)
  have htotal := pack_total L
  have hsuc : (st+1).val = i+1 := by
    rw [Fin.val_add_one_of_lt' (by rw [hst]; exact Nat.lt_of_le_of_lt hi L.cursorFit), hst]
  refine ⟨by rw [Fin.lt_def, hst, htotal]; exact hi, ?_, ?_⟩
  · intro _ hindex
    have haddr := pack_src L st hindex
    change (index pub st).val < (pub 3).val at hindex
    rw [L.rawLength] at hindex
    rw [haddr, hs _ hindex]
    have hpow : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) L.width
    cases raw[(index pub st).val]?.getD false <;>
      simp [PrimedInputRAM.encodeBit, Fin.lt_def, Nat.mod_eq_of_lt (by omega : 2 < 2^w),
        Nat.mod_eq_of_lt (by omega : 1 < 2^w)]
  · have he : st+1 = total pub ↔ i+1 = packCalls pub := by rw [Fin.ext_iff, hsuc, htotal]
    have hword : st+1 = Fin.ofNat (2^w) (i+1) :=
      Fin.ext (hsuc.trans (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hi L.cursorFit)).symm)
    change (if st+1 = total pub then none else some (st+1)) = _
    rw [packControl, if_congr he rfl (congrArg some hword)]

/-- All accepted runs of the actual packed-advice program, including streams
of unintended lengths or surplus bits, with exact final memory. -/
theorem packSweep {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) (hpos : 0 < packCalls pub) {fuel : ℕ} (hf : callFuel ≤ fuel) :
    let P := (stepTable.instantiate w pub).program
    ∃ reports, after m (eventLog reports) = packMemory pub raw m (packCalls pub) ∧
      reports.length = packCalls pub ∧ RAMBuckets.cost Report.probes reports ≤ 4*packCalls pub ∧
      (∀ r ∈ reports, r.probes ≤ 3 ∧ r.events.length < fuel) ∧
      ∀ bits rs, (runSegment P fuel (some 0) m bits = some rs ∧ endState (some 0) rs = none) ↔
        bits = List.replicate (packCalls pub) [] ∧ rs = reports := by
  intro P
  let inv := fun i mem => mem = packMemory pub raw m i
  have initial : inv 0 m := (packMemory_zero pub raw m).symm
  have step (i : ℕ) (hi : i < packCalls pub) (mem : Memory w) (hm : inv i mem) :
      ∃ es, (∀ bs, execute P fuel (P.start (Fin.ofNat (2^w) i)) mem bs =
        if bs = [] then some ⟨es, packControl w (packCalls pub) (i+1)⟩ else none) ∧
        inv (i+1) (after mem es) ∧ countProbes es ≤ 3 := by
    let st := Fin.ofNat (2^w) i
    let rep := stepReport pub st mem
    have hsrc : PackSource pub raw mem := hm ▸ packMemory_source pub raw m L hs i
    obtain ⟨hcur, hb, hstate⟩ := packStep_guards L mem hsrc i hi
    refine ⟨rep.events, ?_, ?_, stepReport_probes_le pub st mem⟩
    · intro bs
      have hx := execute_step pub st mem hcur hb (fun _ => 0) (fun _ => 0) bs hf
      have hr : rep = ⟨rep.events, packControl w (packCalls pub) (i+1)⟩ := by
        change stepReport pub st mem = ⟨_, _⟩
        rw [← hstate]
      change execute P fuel (P.start st) mem bs = if bs = [] then some _ else none
      rw [← hr]
      change execute P fuel (P.start st) mem bs = if bs.isEmpty then some rep else none at hx
      cases bs <;> exact hx
    · change after mem (stepReport pub st mem).events = _
      rw [stepReport_memory, hm]
      exact packMemory_step L m hs i hi
  have hc : packControl w (packCalls pub) 0 = some 0 := by simp [packControl, hpos.ne]
  simpa only [hc] using deterministic_scan P fuel (packCalls pub) 3 inv step (packCalls pub) 0
    (Nat.zero_add _) m initial

/-- A zero-row interval takes zero calls. Its starting cursor and memory are
available to the next phase. -/
theorem packSweep_zero (pub : Fin 5 → Word w) (raw : List Bool) (m : Memory w) (fuel : ℕ)
    (h : packCalls pub = 0) :
    runSegment (stepTable.instantiate w pub).program fuel (some 0) m
      (List.replicate (packCalls pub) []) = some [] ∧
      endState (some (0 : Word w)) [] = some 0 ∧
      after m (eventLog []) = packMemory pub raw m (packCalls pub) := by
  rw [h, packMemory_zero]
  exact ⟨rfl, rfl, rfl⟩

/-- The nonempty advice sweep contributes exactly one native path under the
paper's per-call and global transcript caps. -/
theorem packPathCount {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) (hpos : 0 < packCalls pub) {fuel : ℕ} (hf : callFuel ≤ fuel)
    {S H : ℕ} (hcost : 4*packCalls pub ≤ S*H) (hcap : 4 ≤ H) :
    Nat.card (ActualPaths (stepTable.instantiate w pub).program fuel 0 m (withinCaps S H)) = 1 := by
  let paths := ActualPaths (stepTable.instantiate w pub).program fuel 0 m (withinCaps S H)
  obtain ⟨reports, _, _, hc, hcalls, hall⟩ := packSweep L m hs hpos hf
  have hwithin : withinCaps S H reports :=
    ⟨hc.trans hcost, fun r hr => by have := (hcalls r hr).1; omega⟩
  have uniq (b : paths) : b.val = List.replicate (packCalls pub) [] := by
    obtain ⟨rs, hr, he, _⟩ := b.property
    exact ((hall b.val rs).mp ⟨hr, he⟩).1
  have ⟨hr, he⟩ := (hall (List.replicate (packCalls pub) []) reports).mpr ⟨rfl, rfl⟩
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun a b => Subtype.ext ((uniq a).trans (uniq b).symm)⟩,
      ⟨⟨List.replicate (packCalls pub) [], reports, hr, he, hwithin⟩⟩⟩

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI
