import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase
import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import Init.Data.List.OfFn

/-! Install a geometric address request in the native even bank. The first four
requested even cells serve as temporary address registers while the tail is copied. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall
namespace NativeCopy

open RAM RAM.Block RAM.Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Source, destination, and odd-encoded cursor occupy native slots 0, 1 and 2. The
fourth native slot strips the one-bit odd encoding from each requested word. -/
def advance : Block := .seq (.op (.addrStore 2 6)) <| .seq (bumpIndex 0 2) <| .seq (bumpIndex 2 2) (bumpIndex 4 2)

def setupFrom (header : ℕ) : Block := .seq (copyIndexPlus 0 (Odd.slot header) 8) (.straight [.addrConst 2 8,.addrConst 4 9])

/-- All previous tail words have been written. Every scalar, every caller address,
and every native address from the cursor onward still has its original value. -/
structure TailState (original t : Memory K) (ab : ℕ) (words : List ℕ) (j : ℕ) : Prop where
  source : t.index 0=Odd.slot (ab+j)
  destination : t.index 2=2*j
  cursor : t.index 4=Odd.slot j
  scalars : t.data=original.data
  odd (i : ℕ) : t.index (Odd.slot i)=original.index (Odd.slot i)
  copied (i : ℕ) : 4 ≤ i → i < j → t.index (2*i)=2*(words[i]?.getD 0)
  future (i : ℕ) : j ≤ i → t.index (2*i)=original.index (2*i)

/-- After either an address read or a scalar decoding step deposits a doubled word in
register six, commit that word and advance the three cursors. -/
theorem advance_eval (orig s : Memory K) (P : K → Prop) (ab j : ℕ) (words : List ℕ)
    (hj : 4 ≤ j) (h : TailState orig s ab words j) (safe : s.AllData P) :
    ∃ t, Eval (Memory.AllData P) advance (s.putIndex 6 (2*(words[j]?.getD 0))) 7 t ∧ TailState orig t ab words (j+1) := by
  let v := words[j]?.getD 0
  let b := s.putIndex 6 (2*v)
  let c := b.putIndex (2*j) (2*v)
  let d := c.putIndex 0 (Odd.slot (ab+j)+2)
  let e := d.putIndex 2 (2*j+2)
  let t := e.putIndex 4 (Odd.slot j+2)
  have lo0 : 0≠2*j := by omega
  have lo2 : 2≠2*j := by omega
  have lo4 : 4≠2*j := by omega
  have e3 : Eval (Memory.AllData P) (.op (.addrStore 2 6)) b 1 c := by
    simpa [b,c,h.destination] using Eval.op_addrStore (safe := Memory.AllData P) b 2 6 safe safe
  have e4 : Eval (Memory.AllData P) (bumpIndex 0 2) c 2 d := by
    simpa [b,c,d,lo0,h.source] using bumpIndex_spec c 0 2 e3.safe_end
  have e5 : Eval (Memory.AllData P) (bumpIndex 2 2) d 2 e := by
    simpa [b,c,d,e,lo2,h.destination] using bumpIndex_spec d 2 2 e4.safe_end
  have e6 : Eval (Memory.AllData P) (bumpIndex 4 2) e 2 t := by
    simpa [b,c,d,e,t,lo4,h.cursor] using bumpIndex_spec e 4 2 e5.safe_end
  have outside (p : ℕ) (n0 : p≠0) (n2 : p≠2) (n4 : p≠4) (n6 : p≠6) (nj : p≠2*j) : t.index p=s.index p := by
    simp [b,c,d,e,t,n0,n2,n4,n6,nj]
  refine ⟨t,e3.seq (e4.seq (e5.seq e6)),?_,⟩
  constructor
  · simp [t,e,d,Odd.slot]; omega
  · simp [t,e]; omega
  · simp [t,Odd.slot]; omega
  · exact h.scalars
  · intro i
    exact (outside _ (by unfold Odd.slot; omega) (by unfold Odd.slot; omega) (by unfold Odd.slot; omega)
      (by unfold Odd.slot; omega) (by unfold Odd.slot; omega)).trans (h.odd i)
  · intro i low lt
    by_cases eq : i=j
    · subst i; simp [t,e,d,c,v,Ne.symm lo4,Ne.symm lo2,Ne.symm lo0]
    · exact (outside _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (h.copied i low (by omega))
  · intro i hi
    exact (outside _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (h.future i (by omega))

theorem setupFrom_eval (m : Memory K) (P : K → Prop) (header ab : ℕ) (words : List ℕ) (hm : m.AllData P)
    (base : m.index (Odd.slot header)=Odd.slot ab) : ∃ u, Eval (Memory.AllData P) (setupFrom header) m 11 u ∧ TailState m u ab words 4 := by
  let a := m.putIndex 0 (Odd.slot ab+8)
  let b := a.putIndex 2 8
  let u := b.putIndex 4 9
  have e1 : Eval (Memory.AllData P) (copyIndexPlus 0 (Odd.slot header) 8) m 9 a := by
    simpa only [a,base] using copyIndexPlus_spec m 0 (Odd.slot header) 8 hm
  have e2 : Eval (Memory.AllData P) (.op (.addrConst 2 8)) a 1 b := Eval.op_addrConst a 2 8 e1.safe_end e1.safe_end
  have e3 : Eval (Memory.AllData P) (.op (.addrConst 4 9)) b 1 u := Eval.op_addrConst b 4 9 e2.safe_end e2.safe_end
  refine ⟨u,e1.seq (e2.seq (e3.seq (.skip e3.safe_end))),?_,⟩
  constructor
  · simp [a,b,u,Odd.slot]; omega
  · simp [u,b]
  · rfl
  · rfl
  · intro i; simp [a,b,u,show Odd.slot i≠0 by unfold Odd.slot; omega,show Odd.slot i≠2 by unfold Odd.slot; omega,show Odd.slot i≠4 by unfold Odd.slot; omega]
  · intro i low high; omega
  · intro i hi; simp [a,b,u,show 2*i≠0 by omega,show 2*i≠2 by omega,show 2*i≠4 by omega]

end NativeCopy
end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall
open RAM RAM.Callable

variable {K : Type*}

private theorem memory_eq_of (m t : Memory K) (hd : m.data=t.data) (hi : ∀ a,m.index a=t.index a) : m=t := by
  cases m with
  | mk d a =>
    cases t with
    | mk e b =>
      change d=e at hd
      change ∀ j,a j=b j at hi
      cases hd
      cases funext hi
      rfl

/-- Reinstall only the requested address prefix in an arbitrary scalar field. -/
def requestedMemory (native : Memory K) (words : List ℕ) : Memory K :=
  ⟨native.data,fun i => words[i]?.getD (native.index i)⟩

theorem installed_state (native caller t : Memory K) (words : List ℕ)
    (data : t.data=(Odd.memory native caller).data)
    (odd : ∀ i, t.index (Odd.slot i)=(Odd.memory native caller).index (Odd.slot i))
    (write : ∀ i < words.length, t.index (2*i)=2*(words[i]?.getD 0))
    (after : ∀ i, words.length ≤ i → t.index (2*i)=(Odd.memory native caller).index (2*i)) :
    t=Odd.memory (requestedMemory native words) caller := by
  apply memory_eq_of t (Odd.memory (requestedMemory native words) caller) data
  intro p
  let j := p/2
  by_cases par : p%2=0
  · have even : p=2*j := by dsimp [j]; omega
    rw [even]
    by_cases valid : j < words.length
    · rw [write _ valid,Odd.index_even]
      change 2*(words[j]?.getD 0)=2*(words[j]?.getD (native.index j))
      simp only [List.getElem?_eq_getElem valid,Option.getD_some]
    · rw [after _ (by omega),Odd.index_even,Odd.index_even]
      change 2*native.index j=2*(words[j]?.getD (native.index j))
      simp only [List.getElem?_eq_none (by omega : words.length ≤ j),Option.getD_none]
  · have isOdd : p=Odd.slot j := by dsimp [j,Odd.slot]; omega
    rw [isOdd,odd]
    simp only [Odd.index_slot]

open OracleSpec

/-- Precisely the two packet shapes needed by the finite native-copy dispatcher. -/
theorem nativeCopy_word_shape {r s n : ℕ} (u : MinorLog.RawIndex r s n) :
    (MinorLog.words u).length=2 ∨ 4 ≤ (MinorLog.words u).length := by
  rcases u with a|a <;> simp only [MinorLog.words,MinorLog.squareWords,List.length_append,List.length_cons,List.length_nil,List.length_ofFn] <;> omega

/-- Each request contains its tag, its order and two index arrays. -/
theorem nativeRequest_length_le {r s n : ℕ} (u : MinorLog.RawIndex r s n) :
    (MinorLog.words u).length ≤ 2+2*n := by
  rcases u with a|a <;> simp only [MinorLog.words,MinorLog.squareWords,List.length_append,List.length_cons,List.length_nil,List.length_ofFn] <;> have := a.order.isLt <;> omega

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
