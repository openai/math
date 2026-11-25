import OAI.Optimization.LinearProgramming.Recovery.PairBuilderHeaders

/-! Fixed register installation for transposing the initial slack tableau and starting
the first independent-row/orthogonal-complement pair. The entire scalar bank is framed. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Tape RAM.Call

/-- The source has n rows of h entries. Place its transpose, the n-by-n pair output
and its scratch consecutively after that source. -/
def cBase (g h n : ℕ) := g+n*h
def outBase (g h n : ℕ) := cBase g h n+h*n
def scratchBase (g h n : ℕ) := outBase g h n+n*n

def headers : HeaderPlan 220 :=
  let h : AddressTerm 220 := .reg 200
  let n : AddressTerm 220 := .reg 201
  [(200,.reg 33),(201,.reg 31),(40,.reg 35),(41,.reg 33),(14,.val 0),(205,.val 0),
   (202,(.reg 40)+n*h),(203,(.reg 202)+h*n),(204,(.reg 203)+n*n),
   (31,h),(33,n),(35,.reg 202)]

def headerBlock := HeaderPlan.code 256 headers

/-- Both the table-traversal registers and the persistent PairBuilder input ABI. -/
structure Header {K : Type} (g h n : ℕ) (s : Memory K) : Prop where
  zero : s.index 14=0
  rows : s.index 31=h
  cols : s.index 33=n
  dest : s.index 35=cBase g h n
  source : s.index 40=g
  stride : s.index 41=h
  height : s.index 200=h
  dimension : s.index 201=n
  input : s.index 202=cBase g h n
  output : s.index 203=outBase g h n
  scratch : s.index 204=scratchBase g h n
  clean : s.index 205=0

/-- Original packet metadata and the caller's high address bank. -/
def Protected {K : Type} (s t : Memory K) : Prop :=
  t.index 24=s.index 24 ∧ t.index 28=s.index 28 ∧ t.index 29=s.index 29 ∧
  ∀ p, 512 ≤ p → t.index p=s.index p

private def relevant (e : Fin 220 → ℕ) (i : Fin 220) :=
  if i=31 then e 31 else if i=33 then e 33 else if i=35 then e 35 else 0

private theorem cost_relevant (e : Fin 220 → ℕ) : headers.cost e = headers.cost (relevant e) := by
  apply PairBuilder.plan_cost_congr
  intro i hi
  have sources : PairBuilder.needed headers = ({31,33,35} : Finset (Fin 220)) := by decide
  rw [sources] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with h|h|h <;> subst i <;> rfl

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

set_option maxRecDepth 30000 in
private theorem low_writes : headerBlock.indexWritesBelow 512 = true := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem header_spec (P : K → Prop) (s : Memory K) (g h n : ℕ) (hs : s.AllData P)
    (sr : s.index 31=n) (sc : s.index 33=h) (sg : s.index 35=g) :
    ∃ t k, k ≤ headers.budget.eval (g+h+n) ∧
      Block.Eval (Memory.AllData P) headerBlock s k t ∧ Header g h n t ∧ t.data=s.data ∧
      Protected s t := by
  let e : Fin 220 → ℕ := fun i => s.index i
  obtain ⟨t,k,run,time,data,ix⟩ := headers.correct 256 (by decide) s e (fun _ => rfl) hs
  have frame : Header (s.index 35) (s.index 33) (s.index 31) t :=
    ⟨ix 14,ix 31,ix 33,ix 35,ix 40,ix 41,ix 200,ix 201,ix 202,ix 203,ix 204,ix 205⟩
  have bounded (i : Fin 220) : relevant e i ≤ g+h+n := by
    unfold relevant
    split
    · exact sr.trans_le (by omega)
    split
    · exact sc.trans_le (by omega)
    split
    · exact sg.trans_le (by omega)
    · exact Nat.zero_le _
  have cap : headers.cost e ≤ headers.budget.eval (g+h+n) := by
    rw [cost_relevant]
    exact headers.cost_le (relevant e) _ bounded
  refine ⟨t,k,time.trans cap,
    run,?_,data,ix 24,ix 28,ix 29,?_⟩
  · simpa only [sg,sc,sr] using frame
  · intro p hp
    exact run.index_frame low_writes hp

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
