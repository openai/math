import OAI.Computability.NearSquareRoot.PrecisionSlotRows
import OAI.Computability.NearSquareRoot.SynchronizedPlacementTape
import OAI.Computability.NearSquareRoot.SynchronizedShortAxis

/-! # Phase queries in a borrowing batch on a padded physical block -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Code.Task Strip Staff Carry Grid Dusk ShortFourier AxisWord SynchronizedBorrowing

/-- The physical lookup can yield no local address. This case instruction
inspects the root of the encoded option, then evaluates the payload branch. -/
theorem easyOption {X Y : Type} [Codec X] [Codec Y] (d : Y) (f : X → Y)
    (F : Easy f) : Easy (fun o : Option X ↦ o.elim d f) := by
  have q : Easy (fun p : Bool × X ↦ f p.2) := Easy.snd.compose F
  obtain ⟨c,C,hc⟩ := q
  refine ⟨splitRoot 0 (fun _ ↦ Task.prepare 0 (send d)) (.join (pack 0) c),
    C+5*(send d).count+7, fun x env r ↦ ?_⟩
  cases x with
  | none =>
    refine (fits_bit (b := false) (c := fun _ ↦ Task.prepare 0 (send d))
      (fits_prepare _ _ _ _)).mono ?_
    simp only [size_none,Nat.add_mul]
    omega
  | some y =>
    have hh := hc (true,y) env r
    refine (fits_pair ((fits_pack _ _ _ _ _).join hh)).mono ?_
    simp only [size_some,size_prod,size_bit,Nat.add_mul]
    rw [show 1 + Code.size y + 1 + 1 = Code.size y + 2 + 1 by omega]
    omega

/-- The low-order half-rank supplied by a successful inverse placement.
Unused or padded cells use a unit phase. -/
def SlotQuery.atFlat (q : SlotQuery) (flat : ℕ) : SlotQuery :=
  { q with
    half := decide (2^q.width < flat+1)
    rank := ⟨flat % 2^q.width,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ }

noncomputable def placedCoefficient (q : SlotQuery) (start count row col : ℕ) : ℂ :=
  if col < q.axis then
    (lookupRank start count q.axis (2^q.width) (row*q.axis+col)).elim 1
      (fun entry ↦ (q.atFlat entry.2).coefficient)
  else 1

theorem placedCoefficient_unit (q : SlotQuery) (start count row col : ℕ) :
    ‖placedCoefficient q start count row col‖ = 1 := by
  unfold placedCoefficient
  split
  · cases lookupRank start count q.axis (2^q.width) (row*q.axis+col) with
    | none => simp
    | some p => exact SlotQuery.coefficient_unit _
  · simp

/-- The borrowing inverse, both address halves and the padded/unused masks
are executed in the same polynomial-time setup as the scalar generator. -/
theorem preparePlacedSlot {J : Type} {s : Regime J} {q : J → SlotQuery}
    (H : SlotQuery.Available s q) {start count row col : J → ℕ}
    (S : Realizes s start) (V : Realizes s count) (Y : Realizes s row) (X : Realizes s col)
    (R : Realizes s (fun j ↦ 2^(q j).width)) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ placedCoefficient (q j) (start j) (count j) (row j) (col j)) := by
  let o j := lookupRank (start j) (count j) (q j).axis (2^(q j).width) (row j*(q j).axis+col j)
  have O : s.Has (fun j ↦ encodeLookup (o j)) :=
    lookupRank_has S V H.axis R ((Y.times H.axis).plus X)
  let f j := (o j).elim 0 Prod.snd
  have F : Realizes s f := by
    have found := O.ez (easyOption ([] : Tally) (fun p : Tally × Tally ↦ p.2) Easy.snd)
    change s.Has (fun j ↦ tally (f j))
    convert found using 2
    rename_i j
    cases h : o j <;> simp [f,encodeLookup,h,tally]
  have enabled : s.Has (fun j ↦ (o j).isSome) := by
    have found := O.ez (easyOption false (fun _ : Tally × Tally ↦ true) (Easy.const _))
    convert found using 2
    rename_i j
    cases o j <;> simp [encodeLookup]
  have known : SlotQuery.Available s (fun j ↦ (q j).atFlat (f j)) :=
    ⟨H.axis,H.width,H.bits,H.arg,H.tag,
      (Figure.of_spoken F).modded (Figure.of_spoken R),
      classifiedBool (R.below (F.plus (.fix 1))),H.adj⟩
  have loc : Prepared s (fun j ↦ (q j).bits) (fun j ↦ ((q j).atFlat (f j)).coefficient) :=
    prepareSlot known
  have both := Prepared.conditional (X.below H.axis)
    (Prepared.branch enabled loc (Prepared.one H.bits)) (Prepared.one H.bits)
  convert both using 2
  rename_i j
  change (if col j < (q j).axis then (o j).elim _ _ else _) = _
  by_cases hc : col j < (q j).axis
  · simp only [hc, ite_true]
    have selected (v : Option (ℕ × ℕ)) :
        v.elim 1 (fun t ↦ ((q j).atFlat t.2).coefficient) =
          (bif v.isSome then ((q j).atFlat (v.elim 0 Prod.snd)).coefficient else 1) := by
      cases v <;> rfl
    exact selected (o j)
  · simp [hc]

/-- For the short Fourier padding chosen from the occupied length, a unary
loop through the full half-array is polynomial in the original descriptor. -/
theorem paddedLengthAvailable {J : Type} {s : Regime J} {q : J → SlotQuery}
    (H : SlotQuery.Available s q) (width : ∀ j, (q j).width = paddedLog (q j).axis) :
    Realizes s (fun j ↦ 2^(q j).width) := by
  apply ((Figure.natural 2).repeated H.width).pay
  have b := diameter _ ((Realizes.fix 4).times H.axis)
  apply b.mono
  intro j
  rw [width]
  have h := doubled_pad_lt (q j).axis_pos
  omega

/-- The start and count for each of the fifteen borrowing batches are
computed from the spectator count and its batch number. -/
theorem prepareShortBatchSlot {J : Type} {s : Regime J} {q : J → SlotQuery}
    (H : SlotQuery.Available s q) (width : ∀ j, (q j).width = paddedLog (q j).axis)
    {b row col : J → ℕ} {batch : J → Fin 15}
    (B : Realizes s b) (T : Realizes s (fun j ↦ (batch j).val))
    (Y : Realizes s row) (X : Realizes s col) :
    Prepared s (fun j ↦ (q j).bits)
      (fun j ↦ placedCoefficient (q j) (first (b j) (batch j))
        (SynchronizedBorrowing.size (b j) (batch j)) (row j) (col j)) :=
  preparePlacedSlot H (first_realizes B T) (size_realizes B T) Y X (paddedLengthAvailable H width)

/-- Metadata read from one physical short transform instruction. The borrowing
address is filled by the inverse placement. -/
def SlotQuery.fromInst (a k bits : ℕ) [NeZero a] (op : Inst) : SlotQuery where
  axis := a
  width := k
  bits := bits
  tag := op.1.length
  arg := op.2.1.length
  half := false
  adj := op.2.2
  rank := 0
  axis_pos := NeZero.pos a

/-- The actual opcode, unary bit-position operand and orientation are the
three fields of the generated short-axis instruction. -/
def SlotQuery.ofInstruction (a bits : ℕ) (op : Inst) (ha : 0 < a) : SlotQuery :=
  letI : NeZero a := ⟨ha.ne'⟩
  SlotQuery.fromInst a (paddedLog a) bits op

/-- The instruction comes directly from the setup word. Its tag, operand and
orientation are read by tape projections; padding depth is computed from the
axis length. The placement supplies the address at which it will be run. -/
theorem prepareInstructionBatch {J : Type} {s : Regime J}
    {a bits b row col : J → ℕ} {op : J → Inst} {batch : J → Fin 15}
    (A : Realizes s a) (ha : ∀ j, 0 < a j) (P : Realizes s bits) (Op : s.Has op)
    (B : Realizes s b) (T : Realizes s (fun j ↦ (batch j).val))
    (Y : Realizes s row) (X : Realizes s col) :
    Prepared s bits (fun j ↦ placedCoefficient (SlotQuery.ofInstruction (a j) (bits j) (op j) (ha j))
      (first (b j) (batch j)) (SynchronizedBorrowing.size (b j) (batch j)) (row j) (col j)) := by
  let q j := SlotQuery.ofInstruction (a j) (bits j) (op j) (ha j)
  have W : Realizes s (fun j ↦ paddedLog (a j)) :=
    (Figure.of_spoken (((Realizes.fix 2).times A).minused (.fix 1))).short_log
  have tag : Realizes s (fun j ↦ (op j).1.length) := by
    simpa only [Realizes, Function.comp_def, box, recover_tally] using Op.ez Easy.fst
  have arg : Realizes s (fun j ↦ (op j).2.1.length) := by
    simpa only [Realizes, Function.comp_def, box, recover_tally] using (Op.ez Easy.snd).ez Easy.fst
  have known : SlotQuery.Available s q :=
    ⟨A,W,P,arg,Figure.of_spoken tag, Figure.natural 0, Regime.fixed false, (Op.ez Easy.snd).ez Easy.snd⟩
  exact prepareShortBatchSlot known (fun _ ↦ rfl) B T Y X

end PhaseTable

end NearSquareRoot
end Computability
end OAI
