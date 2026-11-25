import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeTape

/-! # Returning the two serialization heads to their literal starting cells -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open ChunkControl (Driver)

variable (d : Driver) (k : ℕ)

def backIn (k : ℕ) (checking : Bool) : Phase k := if checking then .back else .returnIn

def endedIn (k : ℕ) (checking : Bool) : Phase k :=
  if checking then headerAt k 0 else .returnOut

theorem rewind_in (checking : Bool) (s out : List Ltr) (o : ℤ) (j : ℕ) (hj : j ≤ s.length) :
    Trace (advance (rule d k))
      (cfg (backIn k checking) ((j:ℤ)-1) o (content d s) (content d out)) (j+1)
      (cfg (endedIn k checking) 0 o (content d s) (content d out)) := by
  induction j with
  | zero =>
    have h := Expand.move (rule d k) (backIn k checking) (endedIn k checking) (-1) o
      (content d s) (content d out) .right .stay
      (by cases checking <;> simp [backIn,endedIn,rule,pair])
    simpa [Move.shift] using Trace.single h
  | succ j ih =>
    have hl : j < s.length := by omega
    have h := Expand.move (rule d k) (backIn k checking) (backIn k checking) j o
      (content d s) (content d out) .left .stay
      (by cases checking <;> simp [backIn,rule,pair,content_get d s j hl])
    have one := Trace.single (by simpa [Move.shift,sub_eq_add_neg] using h :
      advance (rule d k) _ = some (cfg (backIn k checking) ((j:ℤ)-1) o (content d s) (content d out)))
    simpa [Nat.add_comm 1] using one.trans (ih (by omega))

theorem rewind_out (s out : List Ltr) (j : ℕ) (hj : j ≤ out.length) :
    Trace (advance (rule d k))
      (cfg .returnOut 0 ((j:ℤ)-1) (content d s) (content d out)) (j+1)
      (cfg .ready 0 0 (content d s) (content d out)) := by
  induction j with
  | zero =>
    have h := Expand.move (rule d k) .returnOut .ready 0 (-1) (content d s) (content d out)
      .stay .right (by simp [rule,pair])
    simpa [Move.shift] using Trace.single h
  | succ j ih =>
    have hl : j < out.length := by omega
    have h := Expand.move (rule d k) .returnOut .returnOut 0 j (content d s) (content d out)
      .stay .left (by simp [rule,pair,content_get d out j hl])
    have one := Trace.single (by simpa [Move.shift,sub_eq_add_neg] using h :
      advance (rule d k) _ = some (cfg .returnOut 0 ((j:ℤ)-1) (content d s) (content d out)))
    simpa [Nat.add_comm 1] using one.trans (ih (by omega))

end StagingSerialize

end NearSquareRoot
end Computability
end OAI
