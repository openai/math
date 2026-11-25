import OAI.ThreeFlat.Diagonal.HistoryCode
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Complete shared histories, numbered final wire bits, and zero padding -/

namespace ThreeFlat.Diagonal.HistoryContraction.Plan

open scoped Classical
noncomputable section
variable {F : Type*} [CommSemiring F] {S : Shape}
variable (P : Plan F S) (E : P.Codes) (bits : P.History → ℕ) (capacity : ℕ)

abbrev Terminal := (h : P.History) × (Fin (bits h) → Bool)

def encodeShared (v : Terminal P bits) : List Bool :=
  P.write E v.1 ++ (List.ofFn v.2 ++ List.replicate (capacity - (P.write E v.1).length - bits v.1) false)

private def getBits (s : List Bool) {n : ℕ} (hs : s.length=n) (i : Fin n) := s.get (i.cast hs.symm)

private theorem list_getBits (s : List Bool) {n : ℕ} (hs : s.length=n) : List.ofFn (getBits s hs) = s := by
  subst n
  exact List.ofFn_get s

private theorem getBits_ofFn {n : ℕ} (f : Fin n → Bool) : getBits (List.ofFn f) List.length_ofFn = f := by
  funext i
  simp [getBits]

private def readWire (h : P.History) (tail : List Bool) : Option (Fin (bits h) → Bool) :=
  if hs : (tail.take (bits h)).length = bits h then
    if tail.drop (bits h) = List.replicate (capacity - (P.write E h).length - bits h) false then
      some (getBits _ hs) else none
  else none

def decodeShared (s : List Bool) : Option (Terminal P bits) := do
  let (h,tail) ← P.read E s
  let wire ← readWire P E bits capacity h tail
  return ⟨h,wire⟩

private theorem decode_after (s : List Bool) (h : P.History) (tail : List Bool)
    (read : P.read E s=some (h,tail)) :
    decodeShared P E bits capacity s=(readWire P E bits capacity h tail).map (fun wire=>⟨h,wire⟩) := by
  unfold decodeShared
  rw [read]
  change (readWire P E bits capacity h tail).bind (fun wire=>some (⟨h,wire⟩ : Terminal P bits))=_
  cases readWire P E bits capacity h tail <;> rfl

@[simp] theorem decode_encode (x : Terminal P bits) :
    decodeShared P E bits capacity (encodeShared P E bits capacity x) = some x := by
  obtain ⟨h,x⟩:=x
  let pad:=List.replicate (capacity-(P.write E h).length-bits h) false
  let t:=List.ofFn x++pad
  have take : t.take (bits h)=List.ofFn x:=List.take_left' List.length_ofFn
  have drop : t.drop (bits h)=pad:=List.drop_left' List.length_ofFn
  have length : (t.take (bits h)).length=bits h:=by rw [take,List.length_ofFn]
  have wire : readWire P E bits capacity h t=some x := by
    unfold readWire
    rw [dite_eq_left length,ite_eq_left drop]
    apply congrArg some
    apply List.ofFn_injective
    exact (list_getBits _ length).trans take
  change decodeShared P E bits capacity (P.write E h++t)=_
  rw [decode_after P E bits capacity _ h t (P.read_write E h t),wire]; rfl

/-- Successful parsing determines every original bit, including padding after the final wires. -/
theorem encode_decode (s : List Bool) (x : Terminal P bits)
    (ok : decodeShared P E bits capacity s = some x) : encodeShared P E bits capacity x = s := by
  cases result : P.read E s with
  | none=>simp [decodeShared,result] at ok
  | some v=>
    obtain ⟨h,t⟩:=v
    rw [decode_after P E bits capacity s h t result] at ok
    by_cases len : (t.take (bits h)).length=bits h
    · by_cases zero : t.drop (bits h)=List.replicate (capacity-(P.write E h).length-bits h) false
      · simp only [readWire,dite_eq_left len,ite_eq_left zero,Option.map_some,Option.some.injEq] at ok
        subst x
        change P.write E h ++ (List.ofFn (getBits _ len) ++ _) = s
        rw [list_getBits,←zero,List.take_append_drop]
        exact (P.write_read E s h t result).symm
      · simp [readWire,len,zero] at ok
    · rw [show readWire P E bits capacity h t=none by unfold readWire; rw [dite_eq_right len]] at ok
      cases ok

/-- After deterministic histogram admission, the only unchecked bits are the terminal
wire prefix and its zero padding. The suffix may have length zero. -/
theorem decodeShared_suffix (s : List Bool) (h : P.History) (tail : List Bool)
    (read : P.read E s=some (h,tail)) (size : s.length=capacity) :
    (decodeShared P E bits capacity s).isSome ↔
      bits h≤tail.length ∧ ∀ i : Fin tail.length,bits h ≤ i.val → tail.get i=false := by
  have eq := congrArg List.length (P.write_read E s h tail read)
  rw [List.length_append,size] at eq
  have pad : tail.drop (bits h)=List.replicate (capacity-(P.write E h).length-bits h) false ↔
      ∀ i : Fin tail.length,bits h ≤ i.val → tail.get i=false := by
    rw [List.eq_replicate_iff]
    constructor
    · rintro ⟨_,all⟩ i hi
      apply all
      apply List.mem_iff_get.mpr
      let j : Fin (tail.drop (bits h)).length := ⟨i.val-bits h,by
        have := i.isLt; rw [List.length_drop]; omega⟩
      exact ⟨j,by simp [j,List.get_eq_getElem,show bits h+(i.val-bits h)=i.val by omega]⟩
    · intro all
      refine ⟨by rw [List.length_drop]; omega,?_⟩
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
      let i : Fin tail.length := ⟨bits h+j.val,by have hj : j.val<tail.length-bits h := j.isLt.trans_eq List.length_drop; omega⟩
      simpa only [List.get_eq_getElem,List.getElem_drop] using all i (by dsimp [i]; omega)
  rw [decode_after P E bits capacity _ h tail read]
  by_cases room : bits h≤tail.length
  · have full : (tail.take (bits h)).length=bits h := by simp [List.length_take,room]
    by_cases zeros : tail.drop (bits h)=List.replicate (capacity-(P.write E h).length-bits h) false
    · refine ⟨fun _ => ⟨room,pad.mp zeros⟩,fun _ => ?_⟩
      simp only [readWire,dite_eq_left full,ite_eq_left zeros,Option.map_some,Option.isSome_some]
    · refine ⟨fun no => ?_, fun all => (zeros (pad.mpr all.2)).elim⟩
      simp only [readWire,dite_eq_left full,ite_eq_right zeros,Option.map_none,Option.isSome_none,Bool.false_eq_true] at no
  · have short : (tail.take (bits h)).length≠bits h := by
      simp only [List.length_take]; omega
    simp [readWire,room]

/-- A fixed-size persistent register contains exactly one encoding for each history and each
final wire assignment. -/
theorem encodeShared_length (x : Terminal P bits) (fits : (P.write E x.1).length + bits x.1 ≤ capacity) :
    (encodeShared P E bits capacity x).length = capacity := by
  simp only [encodeShared,List.length_append,List.length_replicate,List.length_ofFn]
  omega

theorem encodeShared_injective : Function.Injective (encodeShared P E bits capacity) := by
  intro x y h
  simpa only [decode_encode,Option.some.injEq] using congrArg (decodeShared P E bits capacity) h

end
end ThreeFlat.Diagonal.HistoryContraction.Plan

end OAI
