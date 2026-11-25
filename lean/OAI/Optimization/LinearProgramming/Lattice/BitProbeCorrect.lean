import OAI.Optimization.LinearProgramming.Lattice.BitProbeDyadic

/-! The packed finite continuation gives exactly the hidden-vector residual probe, including
its chronological signed rows, for every possible Boolean oracle. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

private def ratioTree {n p : ℕ} (R : Fin n→Fin p→ℤ) (b : Fin p→ℤ) (k : ℕ) : SignQueries p (Fin n→ℚ) :=
  SignQueries.sequence n fun i => (dyadicSearchQ (R i) b k).bind fun a => .done ((a : ℚ)/(2:ℚ)^k)

private theorem ratioTree_run {n p : ℕ} (o : (Fin p→ℤ)→Bool) (R : Fin n→Fin p→ℤ) (b : Fin p→ℤ) (k : ℕ) :
    SignQueries.run o (ratioTree R b k) = fun i => coordinate o (R i) b k := by
  simp only [ratioTree,SignQueries.run_sequence,SignQueries.run_bind,SignQueries.run,coordinate]

private theorem ratioTree_rows_succ {n p : ℕ} (o : (Fin p→ℤ)→Bool) (R : Fin (n+1)→Fin p→ℤ)
    (b : Fin p→ℤ) (k : ℕ) :
    queryRows o (ratioTree R b k) = queryRows o (dyadicSearchQ (R 0) b k) ++
      queryRows o (ratioTree (fun j => R j.succ) b k) := by
  simp only [ratioTree,SignQueries.sequence,queryRows_bind,queryRows_done,List.append_nil]

private theorem rows_prefix_finish {n p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool)
    (h : ∀ a, O (List.ofFn a)=o a) (R : Fin n→Fin p→ℤ) (b : Fin p→ℤ) (z : Params)
    (vs : List ℚ) (hk : 0<z.1.2) :
    Runs O (nextRow (z,List.ofFn b) (List.ofFn (fun i => List.ofFn (R i))) vs)
      (queryRows o (ratioTree R b z.1.2)) (true,vs.reverse ++ List.ofFn fun i => coordinate o (R i) b z.1.2) := by
  induction n generalizing vs with
  | zero => simpa [nextRow,done,ratioTree,SignQueries.sequence] using (Runs.done (oracle := O) (true,vs.reverse))
  | succ n ih =>
    let rest := List.ofFn fun i : Fin n => List.ofFn (R i.succ)
    let y := coordinate o (R 0) b z.1.2
    have first := ratio_prefix O o h (R 0) b z rest vs hk
    have remaining := ih (fun i => R i.succ) (y::vs)
    simpa only [ratioTree_rows_succ,List.ofFn_succ,List.reverse_cons,List.append_assoc,List.singleton_append,rest,y]
      using first.finish remaining

private theorem zero_queryRows {n p : ℕ} (o : (Fin p→ℤ)→Bool) (R : Fin n→Fin p→ℤ) (b : Fin p→ℤ) :
    queryRows o (ratioTree R b 0) = [] := by
  apply List.length_eq_zero_iff.mp
  simp [queryRows,SignQueries.history_length,ratioTree,dyadicSearchQ,SignQueries.cost]

private theorem tail_run {n p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool) (h : ∀ a, O (List.ofFn a)=o a)
    (R : Fin n→Fin p→ℤ) (b : Fin p→ℤ) (k : ℕ) :
    let z : Params := ((p,k),List.ofFn (fun i => List.ofFn (R i)))
    Runs O (nextMax z [] (List.ofFn b))
      (List.ofFn (-b) :: (if o (-b) then [] else queryRows o (ratioTree R b k)))
      (if o (-b) then (false,[]) else (true,List.ofFn (fun i => coordinate o (R i) b k))) := by
  dsimp only
  unfold nextMax
  rw [negateRow_pack]
  apply Runs.ask
  rw [h]
  cases hg : o (-b) with
  | true => exact .done _
  | false =>
    by_cases hk : k=0
    · subst k
      rw [zero_queryRows]
      have hv : List.ofFn (fun i => coordinate o (R i) b 0) = List.replicate n 0 := by
        simp [coordinate,dyadicSearchQ,SignQueries.run,List.ofFn_const]
      rw [hv]
      simpa [advance,zeroReply,done] using (Runs.done (oracle := O) (true,List.replicate n (0:ℚ)))
    · let z : Params := ((p,k),List.ofFn (fun i => List.ofFn (R i)))
      have hr := rows_prefix_finish O o h R b z [] (by change 0<k; omega)
      simpa [advance,zeroReply,z,hk] using hr

/-- Encode a returned option into the wire format, preserving the order of all coordinates. -/
def packedResult {n : ℕ} : Option (Fin n→ℚ) → Result
  | none => (false,[])
  | some y => (true,List.ofFn y)

/-- The packed step machine runs the full typed decision tree, issuing the very same
coefficient rows in the same order and emitting its exact optional rational vector. -/
theorem start_correct {n p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool)
    (h : ∀ a, O (List.ofFn a)=o a) (P : Fin n→Fin p→ℚ) (k : ℕ) :
    Runs O (start ((p,k),List.ofFn (fun i => List.ofFn (integralRows P i))))
      ((SignQueries.history o (probeRowsQ P k)).reverse.map List.ofFn)
      (packedResult (SignQueries.run o (probeRowsQ P k))) := by
  let R := integralRows P
  let z : Params := ((p,k),List.ofFn (fun i => List.ofFn (R i)))
  let t := maxRowQ (List.ofFn R)
  let b := SignQueries.run o t
  have prelim := max_prefix O o h z (List.ofFn R) []
  have hz : List.ofFn (0 : Fin p→ℤ) = List.replicate p 0 := by
    change List.ofFn (fun _ : Fin p => (0:ℤ)) = _
    rw [List.ofFn_const]
  have first : Steps O (start z) (queryRows o t) (nextMax z [] (List.ofFn b)) := by
    simpa only [start,z,t,b,List.append_nil,List.map_ofFn,Function.comp_def,hz] using prelim
  have run := first.finish (tail_run O o h R b k)
  change Runs O (start z) (queryRows o (probeRowsQ P k)) (packedResult (SignQueries.run o (probeRowsQ P k)))
  change Runs O (start z) (queryRows o (t.bind fun d => .ask (-d) fun zero => if zero then .done none else
      (ratioTree R d k).bind (fun ys => .done (some ys))))
    (packedResult (SignQueries.run o (t.bind fun d => .ask (-d) fun zero => if zero then .done none else
      (ratioTree R d k).bind (fun ys => .done (some ys)))))
  simp only [queryRows_bind,queryRows_ask,SignQueries.run_bind,SignQueries.run]
  change Runs O (start z) (queryRows o t ++ (List.ofFn (-b) :: queryRows o (if o (-b) then .done none else
      (ratioTree R b k).bind (fun ys => .done (some ys)))))
    (packedResult (SignQueries.run o (if o (-b) then .done none else (ratioTree R b k).bind (fun ys => .done (some ys)))))
  cases hb : o (-b) <;>
    simpa only [hb,Bool.false_eq_true,ite_false,ite_true,queryRows_done,queryRows_bind,SignQueries.run,
      SignQueries.run_bind,ratioTree_run,List.append_nil,packedResult] using run

/-- With the oracle fixed, every terminating physical trace has the same transcript and output. -/
theorem Runs.deterministic {O : Row → Bool} {a : Action} {xs ys : List Row} {u v : Result}
    (left : Runs O a xs u) (right : Runs O a ys v) : xs=ys ∧ u=v := by
  induction left generalizing ys v with
  | done r => cases right; exact ⟨rfl,rfl⟩
  | ask _ ih =>
    cases right with
    | ask tail => obtain ⟨rfl,rfl⟩ := ih tail; exact ⟨rfl,rfl⟩

/-- The concrete adaptive loop uses at most `2n+1+nk` queries, regardless of answers. -/
theorem start_length_le {n p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool) (h : ∀ a,O (List.ofFn a)=o a)
    (P : Fin n→Fin p→ℚ) (k : ℕ) {rows : List Row} {result : Result}
    (run : Runs O (start ((p,k),List.ofFn (fun i => List.ofFn (integralRows P i)))) rows result) :
    rows.length ≤ 2*n+1+n*k := by
  rw [(run.deterministic (start_correct O o h P k)).1, List.length_map,List.length_reverse,SignQueries.history_length]
  exact probeRowsQ_cost o P k

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
