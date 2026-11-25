import OAI.ThreeFlat.Diagonal.HistoryCode
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # One accepted selector for the identity and each actual trace summand

After the branch bit, a simulator reads precisely the stage records for its
branch, then the prescribed number of terminal wire bits. Every remaining
bit is checked to be zero; the identity branch checks its entire suffix. -/

noncomputable section
namespace Hierarchy.GridSelector

open ThreeFlat.Diagonal.HistoryContraction
open scoped Classical

variable {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S)
  (C : P.Codes) (bits : P.History → ℕ) (cap : ℕ)

abbrev Trace := (h : P.History) × (Fin (bits h) → Bool)

def body (v : Trace P bits) : List Bool :=
  P.write C v.1 ++ List.ofFn v.2 ++ List.replicate (cap-((P.write C v.1).length+bits v.1)) false

def Room := ∀ h, (P.write C h).length+bits h ≤ cap

theorem body_length (room : Room P C bits cap) (v : Trace P bits) :
    (body P C bits cap v).length=cap := by
  rcases v with ⟨h,x⟩
  have := room h
  simp only [body,List.length_append,List.length_ofFn,List.length_replicate]
  omega

def readBits {b : ℕ} (s : List Bool) (hb : b≤s.length) (i : Fin b) : Bool :=
  s.get (i.castLE hb)

theorem readBits_list {b : ℕ} (s : List Bool) (hb : b≤s.length) :
    List.ofFn (readBits s hb) = s.take b := by
  apply List.ext_getElem
  · simp [List.length_take,Nat.min_eq_left hb]
  · intro i hi hj
    simp [readBits]

def read (s : List Bool) : Option (Trace P bits) := do
  let (h,rest) ← P.read C s
  if len : bits h ≤ rest.length then
    if rest.drop (bits h) = List.replicate (cap-((P.write C h).length+bits h)) false then
      return ⟨h,readBits rest len⟩
    else none
  else none

theorem read_body (v : Trace P bits) : read P C bits cap (body P C bits cap v) = some v := by
  rcases v with ⟨h,x⟩
  let pad := List.replicate (cap-((P.write C h).length+bits h)) false
  let rest := List.ofFn x ++ pad
  have len : bits h ≤ rest.length := by simp [rest]
  have data : readBits rest len = x := by
    funext i
    simp [readBits,rest,List.get_eq_getElem,List.getElem_append_left]
  unfold read body
  rw [List.append_assoc,P.read_write]
  change (if hlen : bits h ≤ rest.length then
    if rest.drop (bits h) = pad then some (⟨h,readBits rest hlen⟩ : Trace P bits) else none
    else none) = _
  have tail : rest.drop (bits h)=pad := List.drop_left' List.length_ofFn
  rw [dite_eq_left len,ite_eq_left tail,data]

theorem body_read (s : List Bool) (v : Trace P bits) (ok : read P C bits cap s = some v) :
    body P C bits cap v=s := by
  unfold read at ok
  cases parsed : P.read C s with
  | none => simp [parsed] at ok
  | some out =>
    obtain ⟨h,rest⟩ := out
    rw [parsed] at ok
    change (if len : bits h ≤ rest.length then
      if rest.drop (bits h)=List.replicate (cap-((P.write C h).length+bits h)) false then
        some (⟨h,readBits rest len⟩ : Trace P bits) else none else none)=some v at ok
    split at ok
    next len =>
      split at ok
      next pad =>
        change some _ = some v at ok
        cases Option.some.inj ok
        change P.write C h ++ List.ofFn (readBits rest len) ++ _=s
        rw [List.append_assoc,readBits_list,←pad,List.take_append_drop]
        exact (P.write_read C s h rest parsed).symm
      next => simp at ok
    next => simp at ok

def encode (room : Room P C bits cap) : Option (Trace P bits) → (Fin (cap+1) → Bool)
  | none => fun _ => false
  | some v => Fin.cons true (fun i => (body P C bits cap v).get (i.cast (body_length P C bits cap room v).symm))

def decode (s : Fin (cap+1) → Bool) : Option (Option (Trace P bits)) :=
  if s 0 then (read P C bits cap (List.ofFn (Fin.tail s))).map some
  else if ∀ i, Fin.tail s i=false then some none else none

theorem decode_encode (room : Room P C bits cap) (v : Option (Trace P bits)) :
    decode P C bits cap (encode P C bits cap room v) = some v := by
  cases v with
  | none => simp [decode,encode,Fin.tail]
  | some v =>
    have bodyEq : List.ofFn (fun i : Fin cap => (body P C bits cap v).get
        (i.cast (body_length P C bits cap room v).symm))=body P C bits cap v := by
      apply List.ext_getElem
      · simp [body_length P C bits cap room]
      · intro i hi hj
        simp [List.get_eq_getElem]
    simp only [decode,encode,Fin.cons_zero,Fin.tail_cons]
    exact congrArg (Option.map some) ((congrArg (read P C bits cap) bodyEq).trans (read_body P C bits cap v))

theorem encode_decode (room : Room P C bits cap) (s : Fin (cap+1) → Bool)
    (v : Option (Trace P bits)) (ok : decode P C bits cap s=some v) :
    encode P C bits cap room v=s := by
  unfold decode at ok
  split at ok
  next flag =>
    obtain ⟨r,parsed,rfl⟩ := Option.map_eq_some_iff.mp ok
    have same := body_read P C bits cap _ _ parsed
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [encode] using flag.symm
    · simp only [encode,Fin.cons_succ]
      simp [List.get_eq_getElem,same,Fin.tail]
  next flag =>
    split at ok
    next padding =>
      cases Option.some.inj ok
      funext i
      exact Fin.cases (by simpa [encode] using Bool.eq_false_of_not_eq_true flag |>.symm)
        (fun j => (padding j).symm) i
    next => simp at ok

/-- Rejecting the other padded strings leaves exactly one representative
of every typed, dependent trace and of the identity branch. -/
def validEquiv (room : Room P C bits cap) :
    {s // (decode P C bits cap s).isSome} ≃ Option (Trace P bits) where
  toFun s := (decode P C bits cap s.1).get s.2
  invFun v := ⟨encode P C bits cap room v,by simp [decode_encode]⟩
  left_inv s := Subtype.ext (encode_decode P C bits cap room s.1 _
    (Option.some_get s.2).symm)
  right_inv v := by
    simp [decode_encode]

end Hierarchy.GridSelector
end

end OAI
