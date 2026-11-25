import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeTape

/-! # The finite header and streaming word encoder -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code Bits CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open StagingProtection (Cell blank)
open ChunkControl (Driver)

variable (d : Driver) (k : ℕ)

theorem emit_header (s : List Ltr) :
    Trace (advance (rule d k)) (cursor d (headerAt k 0) [] s []) (header k).length
      (cursor d .scan [] s (header k)) := by
  let F (j : ℕ) := cursor d (headerAt k j) [] s ((header k).take j)
  have hist := Expand.steps (rule d k) F (header k).length fun j hj => by
    let i : Fin (header k).length := ⟨j,hj⟩
    have one := write_step d (.header i) (headerAt k (j+1)) s ((header k).take j) 0
      (header k)[j] .stay .right rfl
    have eq : headerAt k j = .header i := dite_eq_left hj
    dsimp only [F,cursor,List.length_nil,Nat.cast_zero,List.nil_append]
    rw [eq,List.take_succ_eq_append_getElem hj]
    simpa only [Move.shift,add_zero,Nat.cast_zero,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      using one
  have eq : headerAt k (header k).length = .scan := dite_eq_right (lt_irrefl _)
  simpa only [F,List.take_zero,List.take_length,eq] using hist

private theorem bit_step (a : Bool) (before rest out : List Ltr) :
    Trace (advance (rule d k)) (cursor d .scan before (.bit a :: rest) out) 2
      (cursor d .scan (before++[.bit a]) rest (out++[.node,.bit a])) := by
  let s := before ++ .bit a :: rest
  have first := write_step d (k:=k) .scan (.payload a) s out before.length .node .right .right
    (by simp [rule,pair,s,content_next])
  have second := write_step d (k:=k) (.payload a) .scan s (out++[.node]) (before.length+1 : ℕ)
    (.bit a) .stay .right rfl
  have run := (Trace.single first).trans
    (Trace.single (by simpa only [Move.shift,List.length_append,List.length_singleton,
      Nat.cast_add,Nat.cast_one] using second : advance _ _ = some _))
  simpa [s,cursor,List.append_assoc,Move.shift,add_assoc] using run

def pairs : Word → List Ltr
  | [] => []
  | b :: t => .node :: .bit b :: pairs t

@[simp] theorem pairs_term (x : Word) : pairs x ++ [.bit false] = body x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairs,body,ih]

theorem word_trace (x : Word) (before tail out : List Ltr) :
    Trace (advance (rule d k)) (cursor d .scan before (x.map Ltr.bit ++ tail) out)
      (2*x.length) (cursor d .scan (before++x.map Ltr.bit) tail (out++pairs x)) := by
  induction x generalizing before out with
  | nil => simp [pairs]; exact .nil _
  | cons a x ih =>
    have first := bit_step d k a before (x.map Ltr.bit ++ tail) out
    have rest := ih (before++[.bit a]) (out++[.node,.bit a])
    simpa [pairs,List.append_assoc,Nat.mul_succ,Nat.add_comm] using first.trans rest

theorem sep_step (before tail out : List Ltr) :
    advance (rule d k) (cursor d .scan before (.sep :: tail) out) =
      some (cursor d .scan (before++[.sep]) tail (out++[.bit false])) := by
  have h := write_step d (k:=k) .scan .scan (before ++ .sep :: tail) out before.length
    (.bit false) .right .right (by simp [rule,pair,content_next])
  simpa [cursor,List.append_assoc,Move.shift] using h

theorem end_step (before out : List Ltr) :
    advance (rule d k) (cursor d .scan before [] out) =
      some (cfg .returnIn ((before.length:ℤ)-1) out.length (content d before)
        (content d (out++[.bit false]))) := by
  have h := write_step d (k:=k) .scan .returnIn before out before.length (.bit false) .left .stay
    (by simp [rule,pair])
  simpa [cursor,Move.shift,sub_eq_add_neg] using h

end StagingSerialize

end NearSquareRoot
end Computability
end OAI
