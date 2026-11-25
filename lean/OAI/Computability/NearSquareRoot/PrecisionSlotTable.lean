import OAI.Computability.NearSquareRoot.PrecisionLocalTables
import OAI.Computability.NearSquareRoot.SynchronizedSlotTable

/-! # Physical coefficient selection for the compiled local Fourier word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry Dusk Grid ShortFourier ChirpTable AxisWord

/-- The coordinate and opcode fields consumed by the coefficient generator. -/
structure SlotQuery where
  axis : ℕ
  width : ℕ
  bits : ℕ
  tag : ℕ
  arg : ℕ
  half : Bool
  adj : Bool
  rank : Fin (2^width)
  axis_pos : 0 < axis

instance (q : SlotQuery) : NeZero q.axis := ⟨q.axis_pos.ne'⟩

def SlotQuery.address (q : SlotQuery) : Ambient q.width :=
  bif q.half then Sum.inr q.rank else Sum.inl q.rank

/-- Availability of the actual header fields. The opcode and coordinate can
be binary. The precision and bit position support unary precision loops. -/
structure SlotQuery.Available {J : Type} (s : Regime J) (q : J → SlotQuery) : Prop where
  axis : Realizes s (fun j ↦ (q j).axis)
  width : Realizes s (fun j ↦ (q j).width)
  bits : Realizes s (fun j ↦ (q j).bits)
  arg : Realizes s (fun j ↦ (q j).arg)
  tag : Figure s (fun j ↦ (q j).tag)
  rank : Figure s (fun j ↦ (q j).rank.val)
  half : s.Has (fun j ↦ (q j).half)
  adj : s.Has (fun j ↦ (q j).adj)

variable {J : Type} {s : Regime J} {bits : J → ℕ} {q : J → SlotQuery}

theorem Prepared.conditional {cond : J → Prop} [DecidablePred cond]
    {x y : J → ℂ} (C : Classified s cond) (X : Prepared s bits x) (Y : Prepared s bits y) :
    Prepared s bits (fun j ↦ if cond j then x j else y j) := by
  obtain ⟨f,h,eq⟩ := C
  convert Prepared.branch h X Y using 2
  rename_i j
  cases hf : f j <;> simp [eq j, hf]

theorem Prepared.one (P : Realizes s bits) : Prepared s bits (fun _ ↦ 1) := by
  simpa [Fourier.phase] using Prepared.root P (Brief.Signed.fixed 0) (.natural 1) (fun _ ↦ by decide)

private theorem preparedNegOne (P : Realizes s bits) : Prepared s bits (fun _ ↦ -1) := by
  have eq : Fourier.phase 2 1 = -1 := by
    unfold Fourier.phase Fourier.cis
    norm_num
    rw [show (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) = (Real.pi : ℂ) by ring,
      Complex.exp_pi_mul_I]
  simpa only [eq] using Prepared.root P (Brief.Signed.fixed 1) (.natural 2) (fun _ ↦ by decide)

private theorem preparedFiniteSwitch {t : J → ℕ} (T : Figure s t) (n : ℕ)
    (zs : ℕ → J → ℂ) (d : J → ℂ) (D : Prepared s bits d)
    (Z : ∀ i < n, Prepared s bits (zs i)) :
    Prepared s bits (fun j ↦ if t j < n then zs (t j) j else d j) := by
  induction n generalizing t zs with
  | zero => simpa using D
  | succ n ih =>
    have rest := ih (T.subtracted (.natural 1)) (fun i ↦ zs (i+1))
      (fun i hi ↦ Z (i+1) (by omega))
    have ans := Prepared.conditional (T.compare_ (.natural 1)) (Z 0 (by omega)) rest
    convert ans using 2
    rename_i j
    by_cases ht : t j = 0
    · simp [ht]
    · have hn : ¬ t j < 1 := by omega
      have he : t j - 1 + 1 = t j := by omega
      have hl : t j - 1 < n ↔ t j < n+1 := by omega
      simp [hn, he, hl]

private def innerRank (q : SlotQuery) : Fin q.axis :=
  ⟨q.rank.val % q.axis, Nat.mod_lt _ q.axis_pos⟩

private theorem prepareFiber (H : SlotQuery.Available s q)
    (f : (j : J) → Fin (q j).axis → ℂ) (d : J → ℂ)
    (F : Prepared s bits (fun j ↦ f j (innerRank (q j)))) (D : Prepared s bits d) :
    Prepared s bits (fun j ↦ fiberEntries (f j) (d j) (q j).address) := by
  have active := Prepared.conditional (H.rank.compare_ (Figure.of_spoken H.axis)) F D
  have result := Prepared.branch H.half D active
  convert result using 2
  rename_i j
  cases hh : (q j).half <;> by_cases ha : (q j).rank.val < (q j).axis <;>
    simp [SlotQuery.address, fiberEntries,hh,ha, innerRank,Nat.mod_eq_of_lt]

private theorem prepareOuter (H : SlotQuery.Available s q) (kind : OuterChirp) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ fiberEntries (kind.entry (a := (q j).axis)) 1 (q j).address) := by
  apply prepareFiber H _ _ _ (Prepared.one H.bits)
  have inn := Prepared.outer kind H.axis H.bits (Regime.fixed false)
    (fun j ↦ innerRank (q j)) (H.rank.modded (Figure.of_spoken H.axis))
  simpa [OuterChirp.oriented] using inn

private theorem preparePair (H : SlotQuery.Available s q) (a b : Fin 6) :
    Prepared s (fun j ↦ (q j).bits) (fun j ↦ physicalDilationPhase
      (calibratedMultiplier (q j).axis (2^(q j).width)) a b (q j).address) := by
  have prep (c : Fin 6) := Prepared.dilation H.axis H.bits ((Figure.natural 2).repeated H.width)
    (fun j ↦ (q j).rank) H.rank (fun j ↦ (q j).axis_pos) (fun _ ↦ c) (.natural c.val)
  have res := Prepared.branch H.half (prep b) (prep a)
  convert res using 2
  rename_i j
  cases hh : (q j).half <;> simp only [SlotQuery.address, hh, Bool.cond_false,Bool.cond_true] <;> rfl

private def revPos (q : SlotQuery) := q.width - (q.arg + 1)

private theorem rankBitClass (H : SlotQuery.Available s q) :
    Classified s (fun j ↦ (q j).rank.val.testBit (revPos (q j)) = true) := by
  have R : Realizes s (fun j ↦ revPos (q j)) := H.width.minused (H.arg.plus (.fix 1))
  have B := (H.rank.quotients ((Figure.natural 2).repeated R)).modded (.natural 2)
  obtain ⟨f,h,e⟩ := (Figure.natural 0).compare_ B
  refine ⟨f,h,fun j ↦ ?_⟩
  rw [← e]
  dsimp only
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  omega

private theorem prepareControlled (H : SlotQuery.Available s q) (a b : Fin 6) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ bitPhase (q j).arg (fun i ↦ controlledPhase i a b) (q j).address) := by
  have tab (i : Fin 6) := Prepared.idleWalsh H.bits (fun _ ↦ i) (.natural i.val)
  have idle := Prepared.conditional (rankBitClass H) (tab b) (tab a)
  have half := Prepared.branch H.half idle (Prepared.one H.bits)
  have res := Prepared.conditional (H.arg.below H.width) half (Prepared.one H.bits)
  convert res using 2
  rename_i j
  cases hh : (q j).half <;> by_cases h : (q j).arg < (q j).width <;>
    cases hb : (q j).rank.val.testBit (revPos (q j)) <;>
    simp [bitPhase,h,SlotQuery.address,hh,controlledPhase, rankBits, Fin.rev,
      revPos] at hb ⊢ <;> simp [hb]

private theorem prepareTwiddle (H : SlotQuery.Available s q) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ slotPhase (q j).axis (q j).width 1 (q j).arg (q j).address) := by
  have R : Realizes s (fun j ↦ revPos (q j)) := H.width.minused (H.arg.plus (.fix 1))
  have N := (H.rank.modded ((Figure.natural 2).repeated R)).variant (.natural 0) (rankBitClass H)
  have D := (Figure.natural 2).repeated (H.width.minused H.arg)
  have active := Prepared.root H.bits (Brief.Signed.up N) D (fun _ ↦ Nat.two_pow_pos _)
  have half := Prepared.branch H.half (Prepared.one H.bits) active
  have res := Prepared.conditional (H.arg.below H.width) half (Prepared.one H.bits)
  convert res using 2
  rename_i j
  cases hh : (q j).half <;> by_cases h : (q j).arg < (q j).width <;>
    cases hb : (q j).rank.val.testBit (revPos (q j)) <;>
    simp [slotPhase,bitPhase,h,SlotQuery.address,hh,twiddleNumerator,Fin.rev,
      revPos] at hb ⊢ <;> simp [hb]

private theorem prepareTag (H : SlotQuery.Available s q) (t : ℕ) (ht : t < 18) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ slotPhase (q j).axis (q j).width t (q j).arg (q j).address) := by
  have one := Prepared.one H.bits
  have neg := preparedNegOne H.bits
  interval_cases t
  · exact one
  · exact prepareTwiddle H
  · exact one
  · exact one
  · exact prepareOuter H .bluestein
  · exact prepareFiber H (fun _ _ ↦ 1) _ one neg
  · exact prepareFiber H (fun _ _ ↦ -1) _ neg one
  · exact prepareOuter H .periodic
  · exact prepareFiber H (fun j ↦ chirpSpectrum (q j).axis) _ (Prepared.spectrum H.axis H.bits
      (fun j ↦ innerRank (q j)) (H.rank.modded (Figure.of_spoken H.axis))) one
  · exact prepareOuter H .reflected
  · exact one
  · exact preparePair H 0 1
  · exact preparePair H 2 3
  · exact preparePair H 4 5
  · exact one
  · exact prepareControlled H 0 1
  · exact prepareControlled H 2 3
  · exact prepareControlled H 4 5

/-- A single setup program dispatches the opcode and operand in the physical
stage descriptor, computes its scalar, and applies the stored orientation. -/
theorem prepareSlot (H : SlotQuery.Available s q) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ adjointValue (q j).adj
        (slotPhase (q j).axis (q j).width (q j).tag (q j).arg (q j).address)) := by
  have ans := preparedFiniteSwitch H.tag 18
    (fun t j ↦ slotPhase (q j).axis (q j).width t (q j).arg (q j).address)
    (fun _ ↦ 1) (Prepared.one H.bits) (prepareTag H)
  apply Prepared.adjoint H.adj
  convert ans using 2
  rename_i j
  by_cases ht : (q j).tag < 18
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    generalize hu : (q j).tag = t at *
    obtain ⟨m,rfl⟩ : ∃ m, t = m + 18 := ⟨t-18, by omega⟩
    rfl

/-- Every dispatch branch, including idle and out-of-range operands, denotes
a phase of norm one. -/
theorem slotPhase_unit (a k t arg : ℕ) [NeZero a] (x : Ambient k) :
    ‖slotPhase a k t arg x‖ = 1 := slotPhase_norm a k t arg x

/-- Encoding of a coefficient query. The doubled-fiber address is its half
bit followed by the rank inside that half. -/
def SlotQuery.words (q : SlotQuery) :=
  ((tally q.axis, tally q.width, tally q.bits), (tally q.tag, tally q.arg),
    (q.half,q.adj), tally q.rank.val)

def SlotQuery.inputSize (q : SlotQuery) := q.axis + q.width + q.bits + q.tag + q.arg + q.rank.val

private def slotRegime : Regime SlotQuery where
  scale := SlotQuery.inputSize
  header := fun q ↦ send q.words
  gauge := by
    refine ⟨1, 20, fun q ↦ ?_⟩
    change size q.words ≤ 20*(q.inputSize+1)^1
    simp only [SlotQuery.words,SlotQuery.inputSize,size_prod,size_tally,tally_length,size_bit,pow_one]
    omega

/-- One deterministic multitape machine answers every query for the actual
compiled phase instruction. Its transition count and distinct visited cells
are polynomial in the unary local descriptor. -/
theorem prepareSlotOnTapes :
    ∃ v : (q : SlotQuery) → Grain (q.bits+5),
      PolyTreeMachine SlotQuery.inputSize (fun q ↦ send q.words) (fun q ↦ send (mark (k := q.bits+5) (v q))) ∧
      ∀ (q : SlotQuery), ‖meaning (q.bits+2) (q.bits+5) (v q) -
        adjointValue q.adj (slotPhase q.axis q.width q.tag q.arg q.address)‖ ≤ 1/(2:ℝ)^q.bits := by
  have hdr : slotRegime.Has SlotQuery.words := Regime.self
  have left := hdr.ez Easy.fst
  have right := hdr.ez Easy.snd
  have inst := right.ez Easy.fst
  have addr := right.ez Easy.snd
  have flags := addr.ez Easy.fst
  have ra : Realizes slotRegime (fun q ↦ q.rank.val) := addr.ez Easy.snd
  have tg : Realizes slotRegime SlotQuery.tag := inst.ez Easy.fst
  have known : SlotQuery.Available slotRegime id :=
    ⟨left.ez Easy.fst, (left.ez Easy.snd).ez Easy.fst, (left.ez Easy.snd).ez Easy.snd,
     inst.ez Easy.snd, Figure.of_spoken tg, Figure.of_spoken ra, flags.ez Easy.fst, flags.ez Easy.snd⟩
  obtain ⟨v,built,err⟩ := prepareSlot known
  exact ⟨v,polyTreeMachine_of_BT built slotRegime.gauge,err⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
