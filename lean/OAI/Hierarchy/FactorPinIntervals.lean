import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace OAI
/-! # Original input intervals in a scheduled factor tape

A tick reads its header and then the input addresses of its occurrences,
in the given factor order. Within one occurrence the addresses stay in
their original tape order. -/

namespace Hierarchy.FactorPinIntervals

variable {S N : ℕ}

/-- All original bit addresses owned by this factor, in their tape order. -/
def intervalBits (origin : Fin S → Fin N) (i : Fin N) : List (Fin S) :=
  (List.finRange S).filter (fun j => decide (origin j = i))

@[simp] theorem mem_intervalBits {origin : Fin S → Fin N} {i : Fin N} {j : Fin S} :
    j ∈ intervalBits origin i ↔ origin j = i := by
  simp [intervalBits]

/-- The combined interval descriptor for this list of assigned occurrences. -/
def stream (origin : Fin S → Fin N) (xs : List (Fin N)) := xs.flatMap (intervalBits origin)

@[simp] theorem mem_stream {origin : Fin S → Fin N} {xs : List (Fin N)} {j : Fin S} :
    j ∈ stream origin xs ↔ origin j ∈ xs := by
  simp [stream]

theorem nodup_stream (origin : Fin S → Fin N) {xs : List (Fin N)} (hx : xs.Nodup) :
    (stream origin xs).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun _ _ => List.Nodup.filter _ (List.nodup_finRange S),?_⟩
  exact hx.imp fun {i j} ne e hi hj =>
    ne ((mem_intervalBits.mp hi).symm.trans (mem_intervalBits.mp hj))

theorem length_intervalBits (origin : Fin S → Fin N) (i : Fin N) :
    (intervalBits origin i).length = (Finset.univ.filter (fun j => origin j=i)).card := by
  classical
  have nd : (intervalBits origin i).Nodup := List.Nodup.filter _ (List.nodup_finRange S)
  have setEq : (intervalBits origin i).toFinset = Finset.univ.filter (fun j => origin j=i) := by
    ext j
    simp
  rw [←setEq, List.toFinset_card_of_nodup nd]

theorem length_stream (origin : Fin S → Fin N) (xs : List (Fin N)) :
    (stream origin xs).length =
      (xs.map (fun i => (Finset.univ.filter (fun j => origin j=i)).card)).sum := by
  simp only [stream, List.length_flatMap, length_intervalBits]

/-- Input data from the original tape and its factor dispatch. The capacity
is the sum of the counted input bits at each occurrence, plus this tick's
header. -/
structure Layout (T : Type) (S N d : ℕ) where
  origin : Fin S → Fin N
  owner : Fin N → T
  rows : T → List (Fin N)
  owns : ∀ i t, i ∈ rows t ↔ owner i = t
  distinct : ∀ t, (rows t).Nodup
  header : T → List Bool
  advice : Fin S → Bool
  fits : ∀ t, (header t).length +
    ((rows t).map (fun i => (Finset.univ.filter (fun j => origin j=i)).card)).sum ≤ d

namespace Layout
variable {T : Type} {d : ℕ} (P : Layout T S N d)

def tick (j : Fin S) := P.owner (P.origin j)

def inputBits (t : T) := stream P.origin (P.rows t)

theorem inputFits (t : T) : (P.header t).length + (P.inputBits t).length ≤ d := by
  simpa only [inputBits, length_stream] using P.fits t

theorem mem_inputBits {t : T} {j : Fin S} : j ∈ P.inputBits t ↔ P.tick j=t :=
  mem_stream.trans (P.owns _ _)

def slot (j : Fin S) : Fin d :=
  ⟨(P.header (P.tick j)).length + (P.inputBits (P.tick j)).idxOf j, by
    have pos := List.idxOf_lt_length_of_mem ((P.mem_inputBits).mpr (rfl : P.tick j = P.tick j))
    have fit := P.inputFits (P.tick j)
    omega⟩

theorem slot_val {t : T} {j : Fin S} (ht : P.tick j=t) :
    (P.slot j).val = (P.header t).length + (P.inputBits t).idxOf j := by
  simp only [slot,ht]

/-- The source of each bit can be recovered from its tick and slot. -/
def address : Fin S ↪ T × Fin d where
  toFun j := (P.tick j,P.slot j)
  inj' := by
    intro j j' eqn
    have ticks := congrArg Prod.fst eqn
    change P.tick j=P.tick j' at ticks
    have ij := congrArg (fun a : T × Fin d => a.2.val) eqn
    change (P.slot j).val = (P.slot j').val at ij
    rw [P.slot_val ticks,P.slot_val (rfl : P.tick j'=P.tick j')] at ij
    exact (List.idxOf_inj ((P.mem_inputBits).mpr ticks)).mp (Nat.add_left_cancel ij)

/-- The value in a pin that the grid controller fills with a constant. -/
def literal (t : T) (i : Fin d) : Bool :=
  if h : i.val < (P.header t).length then (P.header t)[i.val] else
    (((P.inputBits t)[i.val-(P.header t).length]?).map P.advice).getD false

theorem literal_header (t : T) (i : Fin d) (h : i.val < (P.header t).length) :
    P.literal t i=(P.header t)[i.val] := by simp [literal,h]

theorem literal_slot (j : Fin S) : P.literal (P.tick j) (P.slot j)=P.advice j := by
  have m : j ∈ P.inputBits (P.tick j) := P.mem_inputBits.mpr rfl
  have ge : ¬ (P.slot j).val < (P.header (P.tick j)).length := by
    rw [P.slot_val rfl]
    omega
  rw [literal, dite_eq_right ge, P.slot_val rfl, Nat.add_sub_cancel_left,
    List.getElem?_idxOf m]
  rfl

/-- Every ordinal in the packed descriptors represents its original input bit at
that exact slot (even if other occurrences carry identical factor data). -/
theorem slot_get (t : T) (i : Fin (P.inputBits t).length) :
    let j := (P.inputBits t).get i
    P.tick j=t ∧ (P.slot j).val=(P.header t).length+i.val := by
  have mem := List.get_mem (P.inputBits t) i
  have tickEq := P.mem_inputBits.mp mem
  refine ⟨tickEq,?_⟩
  rw [P.slot_val tickEq]
  congr 1
  exact (nodup_stream P.origin (P.distinct t)).idxOf_getElem i.val i.isLt

end Layout

/-- Turn arbitrary labels of original consecutive pairs into disjoint bit addresses. -/
def pairPorts {E : Type} (rail : E ↪ Fin (S/2)) : E × Bool ↪ Fin S where
  toFun u := ⟨2*(rail u.1).val+u.2.toNat,by
    have h := (rail u.1).isLt
    have b := Bool.toNat_le u.2
    omega⟩
  inj' := by
    rintro ⟨e,s⟩ ⟨f,t⟩ eqn
    have v : 2*(rail e).val+s.toNat=2*(rail f).val+t.toNat := congrArg Fin.val eqn
    have hs := Bool.toNat_le s
    have ht := Bool.toNat_le t
    obtain rfl : e=f := rail.injective (Fin.ext (by omega))
    cases s <;> cases t <;> simp_all

end Hierarchy.FactorPinIntervals

end OAI
