import OAI.Computability.VPVNP.MotifConversion
import OAI.Computability.VPVNP.CompressionState
import OAI.Computability.VPVNP.PrimedCounterBits

/-!
# Reading the outer compressor term choices

In the second shrinking scan of Appendix E, and in the corresponding port-block
scan, the term index consists of one integer per supply edge. The reader checks
each binary word against the payload cap and tests the quadratic energy of the
result. Its successful streams are in bijection with the outer indices of
Theorem 6.1. The readers compose in motif order and along branch-dependent
compression passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

/-- A prefix parser with exactly one code per output. The untouched suffix can
contain the choices of all later motifs and compression levels. -/
structure ChoiceReader (α : Type*) where
  /-- Boolean word encoding an individual choice so that the reader can consume it as a prefix. -/
  encode : α → List Bool
  /-- Decode the next choice and return its unconsumed suffix, or fail when the stream has no
  valid choice prefix. -/
  read : List Bool → Option (α × List Bool)
  read_iff : ∀ bits i tail, read bits = some (i, tail) ↔ bits = encode i ++ tail

namespace ChoiceReader

universe u
variable {α : Type u} {β : Type*}

/-- Successful complete transcripts carry exactly one admitted choice each. -/
def completeEquiv (C : ChoiceReader α) :
    α ≃ {bits : List Bool // ∃ i, C.read bits = some (i, [])} where
  toFun i := ⟨C.encode i, i, (C.read_iff _ _ _).mpr (List.append_nil _).symm⟩
  invFun b := ((C.read b.val).get (b.property.elim fun i hi => hi ▸ rfl)).1
  left_inv i := by
    have h := (C.read_iff (C.encode i) i []).mpr (List.append_nil _).symm
    simp [h]
  right_inv b := by
    obtain ⟨i, hi⟩ := b.property
    apply Subtype.ext
    change C.encode ((C.read b.val).get _).1 = b.val
    simp only [hi, Option.get_some]
    simpa using ((C.read_iff _ _ _).mp hi).symm

/-- A deterministic choice takes no bits. -/
def single (a : α) (h : ∀ x, x = a) : ChoiceReader α where
  encode _ := []
  read bits := some (a, bits)
  read_iff bits x tail := by simp [h x]

/-- Keep the same concrete reader under a change of indices. -/
def reindex (C : ChoiceReader α) (e : α ≃ β) : ChoiceReader β where
  encode i := C.encode (e.symm i)
  read bits := (C.read bits).map (fun (a, tail) => (e a, tail))
  read_iff bits i tail := by
    constructor
    · intro h
      obtain ⟨⟨a, rest⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simpa using (C.read_iff _ _ _).mp hr
    · intro h
      rw [(C.read_iff _ _ _).mpr h]
      simp

/-- Read the first choice before looking up the next reader. This preserves
multiplicity when two first choices lead to identical continuation data. -/
def sigma {β : α → Type u} (C : ChoiceReader α) (D : ∀ i, ChoiceReader (β i)) :
    ChoiceReader ((i : α) × β i) where
  encode p := C.encode p.1 ++ (D p.1).encode p.2
  read bits := do
    let (i, mid) ← C.read bits
    let (j, tail) ← (D i).read mid
    return (⟨i, j⟩, tail)
  read_iff bits p tail := by
    obtain ⟨i, j⟩ := p
    constructor
    · intro h
      cases hc : C.read bits with
      | none => simp [hc] at h
      | some x =>
        obtain ⟨i', mid⟩ := x
        cases hd : (D i').read mid with
        | none => simp [hc, hd] at h
        | some y =>
          obtain ⟨j', rest⟩ := y
          have he : ((⟨i', j'⟩ : Sigma β), rest) = (⟨i, j⟩, tail) := by simpa [hc, hd] using h
          cases he
          rw [(C.read_iff _ _ _).mp hc, ((D i).read_iff _ _ _).mp hd, List.append_assoc]
    · intro h
      simp only [List.append_assoc] at h
      rw [(C.read_iff _ _ _).mpr h]
      simp [((D i).read_iff ((D i).encode j ++ tail) j tail).mpr rfl]

/-- Reject a candidate which fails the deterministic admission test. -/
def restrict (C : ChoiceReader α) (ok : α → Bool) : ChoiceReader {i // ok i = true} where
  encode i := C.encode i.val
  read bits := do
    let (a, tail) ← C.read bits
    if h : ok a = true then return (⟨a, h⟩, tail) else none
  read_iff bits i tail := by
    constructor
    · intro h
      cases hc : C.read bits with
      | none => simp [hc] at h
      | some x =>
        obtain ⟨a, rest⟩ := x
        by_cases ha : ok a = true
        · have he : ((⟨a, ha⟩ : {i // ok i = true}), rest) = (i, tail) := by simpa [hc, ha] using h
          cases he
          exact (C.read_iff _ _ _).mp hc
        · simp [hc, ha] at h
    · intro h
      rw [(C.read_iff _ _ _).mpr h]
      simp [i.property]

/-- Read a finite ordered list of motifs. Each motif can have its own set of
terms and its own number of supply coordinates. -/
def vector : (d : ℕ) → (A : Fin d → Type*) →
    (∀ i, ChoiceReader (A i)) → ChoiceReader (∀ i, A i)
  | 0, _, _ => single (fun i => nomatch i) (fun _ => funext fun i => nomatch i)
  | d + 1, A, C =>
    let rest := vector d (fun i => A i.succ) (fun i => C i.succ)
    let merge : ((_ : A 0) × ((i : Fin d) → A i.succ)) ≃ ((i : Fin (d + 1)) → A i) :=
      { toFun := fun x => Fin.cons x.1 x.2
        invFun := fun f => ⟨f 0, Fin.tail f⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := Fin.cons_self_tail }
    ((C 0).sigma fun _ => rest).reindex merge

theorem vector_length (d : ℕ) (A : Fin d → Type*) (C : ∀ i, ChoiceReader (A i)) (a : ∀ i, A i) :
    ((vector d A C).encode a).length = ∑ i, ((C i).encode (a i)).length := by
  induction d with
  | zero => simp [vector, single]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    change ((C 0).encode (a 0) ++ (vector d (fun i => A i.succ) (fun i => C i.succ)).encode (Fin.tail a)).length = _
    rw [List.length_append, ih]
    rfl

theorem vector_encode (d : ℕ) (A : Fin d → Type*) (C : ∀ i, ChoiceReader (A i)) (a : ∀ i, A i) :
    (vector d A C).encode a = (List.ofFn (fun i => (C i).encode (a i))).flatten := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.ofFn_succ]
    change (C 0).encode (a 0) ++ (vector d (fun i => A i.succ) (fun i => C i.succ)).encode (Fin.tail a) = _
    rw [ih]
    rfl

/-- One checked machine-word candidate. -/
def bounded (w bound : ℕ) (h : bound ≤ 2 ^ w) : ChoiceReader (Fin bound) where
  encode a := PrimedCounter.digits w a.val
  read := PrimedCounter.takeBounded w bound
  read_iff := PrimedCounter.takeBounded_eq bound h

end ChoiceReader

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- The bound on each coordinate checked before the quadratic admission test. -/
abbrev outerCap (demand : D → ℕ) :=
  MotifAdmission.payloadCap q (repetitions B demand) B.scale B.radius

/-- With zero repetitions every payload is forced to zero and no choice bit is used. -/
def coordinateBits (demand : D → ℕ) (w : ℕ) :=
  if repetitions B demand = 0 then 0 else w

theorem coordinate_fit (demand : D → ℕ) (w : ℕ) (hw : outerCap B demand < 2 ^ w) :
    outerCap B demand + 1 ≤ 2 ^ coordinateBits B demand w := by
  by_cases h : repetitions B demand = 0
  · simp [coordinateBits, outerCap, MotifAdmission.payloadCap, h]
  · simpa [coordinateBits, h] using hw

private def admittedBoxEquiv (demand : D → ℕ) (hq : ∀ e, 0 < q e) :
    {v : S → Fin (outerCap B demand + 1) //
      MotifAdmission.admit q (fun e => (v e).val) (repetitions B demand) B.scale B.radius = true}
      ≃ ↥(outerIndices B demand) where
  toFun v := ⟨fun e => (v.val e).val, (mem_outerIndices_iff B hq _ _).mpr v.property⟩
  invFun v :=
    let h := (mem_outerIndices_iff B hq _ _).mp v.property
    ⟨fun e => ⟨v.val e, Nat.lt_succ_of_le (MotifAdmission.payload_le_cap q hq _ _ _ _ h e)⟩, h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The concrete binary reader for exactly the terms of the fixed conversion.
The numbering of the supply edges is chosen once for the motif. -/
def outerReader {n : ℕ} (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) (demand : D → ℕ)
    (w : ℕ) (hw : outerCap B demand < 2 ^ w) : ChoiceReader ↥(outerIndices B demand) :=
  let cap := outerCap B demand + 1
  let one := ChoiceReader.bounded (coordinateBits B demand w) cap (coordinate_fit B demand w hw)
  let box := (ChoiceReader.vector n (fun _ => Fin cap) (fun _ => one)).reindex
    (Equiv.arrowCongr order (Equiv.refl (Fin cap)))
  (box.restrict (fun v => MotifAdmission.admit q (fun e => (v e).val)
    (repetitions B demand) B.scale B.radius)).reindex (admittedBoxEquiv B demand hq)

/-- A successful read consumes just the specified edge order, including the
leading zero bits of each word. Rejection can occur after the cap check or
after the total energy test. -/
theorem read_outer_iff {n : ℕ} (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) (demand : D → ℕ)
    (w : ℕ) (hw : outerCap B demand < 2 ^ w) (bits tail : List Bool) (v : ↥(outerIndices B demand)) :
    (outerReader B order hq demand w hw).read bits = some (v, tail) ↔
      bits = (List.ofFn (fun i => PrimedCounter.digits (coordinateBits B demand w)
        (v.val (order i)))).flatten ++ tail := by
  rw [ChoiceReader.read_iff]
  unfold outerReader ChoiceReader.restrict ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_encode]
  rfl

theorem outerReader_length {n : ℕ} (order : Fin n ≃ S) (hq : ∀ e, 0 < q e)
    (demand : D → ℕ) (w : ℕ) (hw : outerCap B demand < 2 ^ w) (v : ↥(outerIndices B demand)) :
    ((outerReader B order hq demand w hw).encode v).length = n * coordinateBits B demand w := by
  unfold outerReader ChoiceReader.restrict ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_length]
  simp [ChoiceReader.bounded, PrimedCounter.digits]

theorem zero_repetitions (demand : D → ℕ) (h : ∀ i, demand i = 0) :
    repetitions B demand = 0 := by
  simp [repetitions, MotifAdmission.copies, MotifAdmission.ceilRoot, MotifAdmission.energy, h]

/-- A motif with zero-width demands has the zero vector as its sole outer index. -/
theorem zero_outerIndices (demand : D → ℕ) (h : ∀ i, demand i = 0) (hq : ∀ e, 0 < q e) :
    outerIndices B demand = {fun _ => 0} := by
  classical
  ext v
  rw [mem_outerIndices_iff B hq, Finset.mem_singleton]
  constructor
  · intro hv
    funext e
    have hcap := MotifAdmission.payload_le_cap q hq v _ _ _ hv e
    simpa [MotifAdmission.payloadCap, zero_repetitions B demand h] using hcap
  · rintro rfl
    simp [MotifAdmission.admit, MotifAdmission.energy]

theorem zero_outer_code {n : ℕ} (order : Fin n ≃ S) (hq : ∀ e, 0 < q e)
    (demand : D → ℕ) (hd : ∀ i, demand i = 0) (w : ℕ) (hw : outerCap B demand < 2 ^ w)
    (v : ↥(outerIndices B demand)) : (outerReader B order hq demand w hw).encode v = [] := by
  apply List.length_eq_zero_iff.mp
  simp [outerReader_length, coordinateBits, zero_repetitions B demand hd]

/-- At zero demand the sole term's local map multiplies an empty list of
parameters. This proves its unit value independently of the parameter ring. -/
theorem zero_entry_value {A : Type*} [CommMonoidWithZero A] (κ : (parameterData B).Entry → A)
    (hp : ∀ i, 0 < p i) (demand : D → ℕ) (hd : ∀ i, demand i = 0) (j : J)
    (x : MotifDemandPadding.HalfBits a b demand j)
    (y : Half P (fun e => Word (supplyWidths B demand (fun _ => 0) e)) j) :
    evalEntry κ (entry B hp demand (fun _ => 0) j x y) = 1 := by
  classical
  let : IsEmpty (Fin (repetitions B demand)) := Fin.isEmpty_iff.mpr (zero_repetitions B demand hd)
  have agrees (fields : Half P (fun _ => (Fin (repetitions B demand) → Word B.selectorBits) × Word 0) j) :
      HalfAgrees P j fields :=
    ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  have tags (v : Fin (repetitions B demand) → Word B.selectorBits) :
      v ∈ Set.range (sequenceCode (selectorCode B) (repetitions B demand)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  have widths (v : Fin (repetitions B demand) → Selector B) :
      (fun _ => 0) = totalWidth (basePayload B) v := by funext e; simp [totalWidth]
  simp [entry, groupedIndices, agrees, tagIndices, tags, payloadIndices, evalEntry]
  rw [dite_eq_left (widths _)]
  rfl

/-- For a fixed motif the required word width is logarithmic in the maximum
demand width. The cap itself is computed by the same fixed integer formula
used in the reader. -/
theorem outerCap_bits_le (demand : D → ℕ) (M : ℕ) (hd : ∀ i, demand i ≤ M) :
    (outerCap B demand).size ≤
      (((∑ i, MotifAdmission.weight p i) + 1) * B.scale * B.radius.num.natAbs *
        MotifAdmission.denominator q).size + Nat.clog 2 (M + 1) := by
  let K := ((∑ i, MotifAdmission.weight p i) + 1) * B.scale * B.radius.num.natAbs *
    MotifAdmission.denominator q
  have hcap : outerCap B demand ≤ K * (M + 1) :=
    MotifAdmission.payloadCap_le p q demand B.scale M B.radius B.scale_pos hd
  apply Nat.size_le.mpr
  rw [pow_add]
  exact hcap.trans_lt (mul_lt_mul_of_lt_of_le_of_pos_of_nonneg (Nat.lt_size_self K)
    (Nat.le_pow_clog (by decide) _) (Nat.succ_pos _) (Nat.zero_le _))

/-- One complete ordered pass over the motifs, as in the shrinking and
degree-refresh scans. Demand widths may vary independently from motif to motif. -/
def motifPassReader {I : Type} {n t : ℕ} (motifs : Fin t ≃ I) (edges : Fin n ≃ S)
    (hq : ∀ e, 0 < q e) (demand : I → D → ℕ) (w : ℕ) (hw : ∀ i, outerCap B (demand i) < 2 ^ w) :
    ChoiceReader ((i : I) → ↥(outerIndices B (demand i))) :=
  (ChoiceReader.vector t _ (fun j => outerReader B edges hq (demand (motifs j)) w (hw (motifs j)))).reindex
    (Equiv.piCongrLeft (fun i => ↥(outerIndices B (demand i))) motifs)

theorem motifPass_bits_le {I : Type} {n t : ℕ} (motifs : Fin t ≃ I) (edges : Fin n ≃ S)
    (hq : ∀ e, 0 < q e) (demand : I → D → ℕ) (w : ℕ) (hw : ∀ i, outerCap B (demand i) < 2 ^ w)
    (v : ∀ i, ↥(outerIndices B (demand i))) :
    ((motifPassReader B motifs edges hq demand w hw).encode v).length ≤ t * (n * w) := by
  unfold motifPassReader ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_length]
  calc
    _ ≤ ∑ _ : Fin t, n * w := Finset.sum_le_sum fun i _ => by
      rw [outerReader_length]
      apply Nat.mul_le_mul_left
      unfold coordinateBits
      split <;> omega
    _ = _ := by simp

namespace ChoiceReader

open Compression

/-- At each compression pass, the complete next set of motifs can depend on
the earlier layout and widths. A pass reader consumes just its own prefix. -/
def passReaders {R : Type*} [CommSemiring R] {b n : ℕ} {a g : ℕ} {X : State a g} :
    StateExecution R b n X → Type
  | .done _ => Unit
  | .more p tail => ChoiceReader p.step.Choice × (∀ i, passReaders (tail i))

/-- The complete descriptor-phase reader on a branch-dependent sequence of
compression passes. Its output is the existing compressor's term sequence. -/
def execution {R : Type*} [CommSemiring R] {b n : ℕ} {a g : ℕ} {X : State a g}
    (P : StateExecution R b n X) : passReaders P → ChoiceReader P.Choices :=
  match P with
  | .done _ => fun _ => single () (fun _ => rfl)
  | .more _ tail => fun readers => readers.1.sigma fun i => execution (tail i) (readers.2 i)

end ChoiceReader
end CompressorRecords

end VPVNP
end Computability
end OAI
