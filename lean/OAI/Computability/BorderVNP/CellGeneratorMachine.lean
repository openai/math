import OAI.Computability.BorderVNP.CellGeneratorWire
import OAI.Computability.BorderVNP.CellLeafBit

/-! # The private sparse command generator on finite named stacks

Its finite control depends on the permitted address and block nesting depths. Input fields,
copy counts, site metadata and profile descriptors stay on the tapes. Only a selected
conditional child runs. Repetition calls its stored body in ascending occurrence order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape CellSparse RationalHitting.StackLanguage

/-- Actual binary arithmetic clocks of the installed address and bit procedures. -/
noncomputable def clocks (d : ℕ) : Clocks where
  expr a env := (evalClock d).eval ((Coding.code (Address.pack d a,env)).length+1)
  bit v i env := (bitClock d).eval ((Coding.code ((Address.pack d v,Address.pack d i),env)).length+1)

private def reject : Fragment IO := .plain (.ofRoutine (.halt false))

private noncomputable def leaves (d : ℕ) : Fragment IO :=
  Fragment.select .row (Fragment.select .row fixedLeaf (readLeaf (eval d))) (bitLeaf d)

/-- Finite command dispatcher. The two nested constructs can call only the next smaller
nesting depth, while a sequence has no effect on that depth. -/
noncomputable def handler (d : ℕ) : ℕ → Fragment IO
  | 0 => Fragment.select .row (leaves d) reject
  | h+1 => let child := scan (handler d h)
           Fragment.select .row (leaves d) (Fragment.select .row
             (Loop.dispatch (eval d) child) (Branch.dispatch (eval d) child))

/-- Executable fixed private generator on compact framed input. -/
noncomputable def generate (d h : ℕ) : Fragment IO := scan (handler d h)

private theorem set_input (r e o z : List Bool) :
    Function.update (io r e o) .row z = io z e o := by funext i; cases i <;> simp [io]

private theorem zeroTag {lo hi : Fragment IO} {r env out emitted : List Bool} {t : ℕ}
    (h : lo.Runs t (io r env out) (io [] env emitted)) :
    (Fragment.select .row lo hi).Runs (t+1) (io (false::r) env out) (io [] env emitted) := by
  apply Fragment.runs_select_false (s := io (false::r) env out) rfl
  rwa [set_input]

private theorem oneTag {lo hi : Fragment IO} {r env out emitted : List Bool} {t : ℕ}
    (h : hi.Runs t (io r env out) (io [] env emitted)) :
    (Fragment.select .row lo hi).Runs (t+1) (io (true::r) env out) (io [] env emitted) := by
  apply Fragment.runs_select_true (s := io (true::r) env out) rfl
  rwa [set_input]

private theorem low {d h t : ℕ} {r env out emitted : List Bool}
    (hr : (leaves d).Runs t (io r env out) (io [] env emitted)) :
    (handler d h).Runs (t+1) (io (false::r) env out) (io [] env emitted) := by
  cases h <;> exact zeroTag hr

private def checked (d h : ℕ) (env : List ℕ) (j : Job) : Prop :=
  ∀ acc, ∃ t ≤ j.ticks, (handler d h).Runs t (io j.input (Coding.code env) acc)
    (io [] (Coding.code env) (j.output.reverse ++ acc))

private theorem scan_checked {d h : ℕ} {s : Stmt} {env : List ℕ} (acc : List Bool)
    (ok : ∀ j ∈ jobs (clocks d) d s env, checked d h env j) :
    ∃ t ≤ scanCost (jobs (clocks d) d s env),
      (generate d h).Runs t (io (serialized d s) (Coding.code env) acc)
        (io [] (Coding.code env) ((stream (s.expand env)).reverse ++ acc)) := by
  obtain ⟨t, ht, hr⟩ := scan_run (handler d h) Job.input Job.output Job.ticks (Coding.code env)
    (jobs (clocks d) d s env) acc ok
  rw [job_inputs, job_outputs] at hr
  exact ⟨t,ht,hr⟩

private theorem fixed_ok (d h : ℕ) (env : List ℕ) (o : Op) :
    checked d h env ⟨[false,false,false] ++ o.bits,o.bits,3+4*o.bits.length+2⟩ := by
  intro out
  obtain ⟨t,ht,hr⟩ := fixedLeaf_run o.bits (Coding.code env) out
  exact ⟨t+1+1+1, show t+1+1+1 ≤ 3+4*o.bits.length+2 by omega, low (zeroTag (zeroTag hr))⟩

private theorem read_ok (d h : ℕ) (a : NatExpr) (env : List ℕ) (ha : Address.depth a ≤ d) :
    ∀ j ∈ jobs (clocks d) d (.read a) env, checked d h env j := by
  intro j hj
  obtain rfl := List.mem_singleton.mp hj
  intro out
  obtain ⟨e,he,run⟩ := eval_run d a env out ha
  obtain ⟨t,ht,hr⟩ := readLeaf_run (eval d) (exprBits d a) (Coding.code env) out (a.eval env) run
  refine ⟨t+1+1+1, ?_, low (zeroTag (oneTag hr))⟩
  change t+1+1+1 ≤ 3+_+(7*(a.eval env)+8)*(a.eval env).bits.length+4*(a.eval env)+9
  change e ≤ (clocks d).expr a env at he
  omega

private theorem all_checked (d h : ℕ) (s : Stmt) (env : List ℕ) (hs : s.FitsDepth d h) :
    ∀ j ∈ jobs (clocks d) d s env, checked d h env j := by
  induction s generalizing h env with
  | nil => simp [jobs]
  | fixed o =>
    cases o with
    | read k => exact read_ok d h (.lit k) env (Nat.zero_le _)
    | literal b | guess | nand | guard | sign =>
      intro j hj; obtain rfl := List.mem_singleton.mp hj; exact fixed_ok d h env _
  | read a => exact read_ok d h a env hs
  | bit v i =>
    intro j hj; obtain rfl := List.mem_singleton.mp hj
    intro acc
    obtain ⟨t,ht,hr⟩ := bitLeaf_run d v i env acc hs.1 hs.2
    refine ⟨t+1+1, ?_, low (oneTag hr)⟩
    change t+1+1 ≤ 2+(clocks d).bit v i env
    change t ≤ (clocks d).bit v i env at ht
    omega
  | seq a b iha ihb =>
    intro j hj
    rcases List.mem_append.mp hj with h | h
    · exact iha _ env hs.1 j h
    · exact ihb _ env hs.2 j h
  | loop a b ih =>
    obtain ⟨hh, ha, hb⟩ := hs
    obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    intro j hj; obtain rfl := List.mem_singleton.mp hj
    intro acc
    obtain ⟨e,he,evalRun⟩ := eval_run d a env acc ha
    let emit (i : ℕ) := stream (b.expand (i::env))
    let cost (i : ℕ) := scanCost (jobs (clocks d) d b (i::env))
    have child (i : ℕ) (_hi : i < a.eval env) (out : List Bool) :
        ∃ t ≤ cost i, (generate d h).Runs t (io (serialized d b) (codeWord i.bits ++ Coding.code env) out)
          (io [] (codeWord i.bits ++ Coding.code env) ((emit i).reverse ++ out)) :=
      scan_checked out (ih h (i::env) hb)
    obtain ⟨t,ht,hr⟩ := Loop.dispatch_run (eval d) (generate d h) (exprBits d a) (serialized d b)
      (Coding.code env) acc (a.eval env) emit cost evalRun child
    have hemit : (List.range (a.eval env)).flatMap emit = stream ((Stmt.loop a b).expand env) := by
      simp [Stmt.expand,emit,stream,List.flatMap_assoc]
    rw [hemit] at hr
    refine ⟨t+1+1, ?_, oneTag (zeroTag hr)⟩
    change t+1+1 ≤ 2+Loop.overheadDispatch (exprBits d a) (serialized d b) (a.eval env)+
      (clocks d).expr a env+Loop.sweepCost (serialized d b) (Coding.code env) cost 0 (a.eval env)
    change e ≤ (clocks d).expr a env at he
    omega
  | ifEq a b y n ihy ihn =>
    obtain ⟨hh, hd, hy, hn⟩ := hs
    obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    intro j hj; obtain rfl := List.mem_singleton.mp hj
    intro acc
    let branch := Stmt.ifEq a b y n
    let answer := (stream (branch.expand env)).reverse ++ acc
    let c := if a.eval env = b.eval env then scanCost (jobs (clocks d) d y env)
      else scanCost (jobs (clocks d) d n env)
    have choice : ∃ t ≤ c, (generate d h).Runs t
        (io (if a.eval env = b.eval env then serialized d y else serialized d n) (Coding.code env) acc)
        (io [] (Coding.code env) answer) := by
      by_cases eq : a.eval env = b.eval env
      · simpa only [c,answer,branch,Stmt.expand,eq,ite_true] using
          scan_checked acc (ihy h env hy)
      · simpa only [c,answer,branch,Stmt.expand,eq,ite_false] using
          scan_checked acc (ihn h env hn)
    obtain ⟨tc,htc,hc⟩ := choice
    obtain ⟨t,ht,hr⟩ := Branch.eval_dispatch d (generate d h) a b env (serialized d y)
      (serialized d n) acc answer hd hc
    refine ⟨t+1+1, ?_, oneTag (oneTag hr)⟩
    change t+1+1 ≤ 2+(clocks d).expr (difference a b) env+c+Branch.overhead _ _ _ _
    change t ≤ (clocks d).expr (difference a b) env+tc+Branch.overhead _ _ _ _ at ht
    dsimp only [exprBits]
    omega

/-- The actual fixed finite private generator expands every compact input satisfying its
declared syntax depths into exactly the required chronological instruction stream, within
the sum of the individual field, iteration, and command scan bounds. -/
theorem generate_run (d h : ℕ) (s : Stmt) (env : List ℕ) (out : List Bool) (hs : s.FitsDepth d h) :
    ∃ t ≤ scanCost (jobs (clocks d) d s env), (generate d h).Runs t
      (io (serialized d s) (Coding.code env) out)
      (io [] (Coding.code env) ((stream (s.expand env)).reverse ++ out)) :=
  scan_checked out (all_checked d h s env hs)

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
