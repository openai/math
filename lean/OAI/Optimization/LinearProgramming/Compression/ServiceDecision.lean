import OAI.Optimization.LinearProgramming.Compression.ServiceProgram
import OAI.Optimization.LinearProgramming.Compression.ServicePost

/-! A normal-entry numerical solver is invoked inside the protected public service.
The callee's complete RAM trace is replayed in the even bank; the data-dependent return
tag is observed by the actual caller instruction stream. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceDecision
open RAM RAM.Callable OracleSpec.MinorLog GeneratorTable ServiceBudget ServicePrepare

theorem emittedTag {v : State ℚ} {r : Option ℚ} (h : emits v r) : v.output=some (replyTag r) := by
  cases r with
  | none => exact h
  | some q => exact h.1

theorem run {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    {p : Program} {time height : Polynomial ℕ} (solver : NumericSolverSpec p time height)
    (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E) (H : ℕ) (s : Memory ℚ)
    (ins : Inspected D E J u H s) (tape : MagnitudeTape D E J u s) (hg : J.card ≤ paperWidth n) (hH : 3 ≤ H)
    (space : height.eval (n+totalBits (List.ofFn (matrixMinorCache D E J u))) ≤ H) :
    let rom := (ServiceInvoke.numerical p).localBudget
    let cap := capacity time rom n
    let r := matrixMinorRequest D E (manuscriptProxyFuel n) J u
    ∃ (prepared : Memory ℚ) (last : State ℚ) (out : Memory ℚ),
      (decision p time).Run (fun q => ratBits q ≤ H) s
        (ServicePrepare.work time rom n J.card+1+(2*time.eval n+2)) out ∧
      Ready D E J u cap s prepared ∧ ServiceInvoke.Returned prepared last.memory out cap (replyTag r) ∧
      emits last r ∧ out.index 15=1 := by
  let rom := (ServiceInvoke.numerical p).localBudget
  let cap := capacity time rom n
  let g := J.card
  let pos := matrixMinorPosition J u
  let mag := matrixMinorCache D E J u
  let rnk := rank u J.sort
  let r := matrixMinorRequest D E (manuscriptProxyFuel n) J u
  let P := fun q => ratBits q ≤ H
  let dims := [n,g,pos.isSome.toNat,rnk]
  let xs := List.ofFn mag
  have rle : rnk ≤ g := by
    have card : J.sort.length = J.card := @Finset.length_sort _ J _ _ _ _ _
    exact (rank_le_length u J.sort).trans_eq card
  have relation : ∀ i,pos=some i → i.val=rnk := position_rank J u ins.persistent.generators.sorted
  obtain ⟨last,hcall,emission⟩ := solver hg pos rnk rle relation mag (fun i => minorMagnitude_pos D E _)
  have answer : numericalValue n pos mag = r := numericalValue_of_minor D E J u
  have em : emits last r := (congrArg (emits last) answer).mp emission
  obtain ⟨k,hk,tr,htr,flast,bits⟩ := hcall
  have bits' (i j) : P ((tr i).data j) := (bits i j).trans space
  have dataSafe (i : ℕ) : P ((start dims xs).data i) := by simpa only [htr.1] using bits' 0 i
  obtain ⟨x,kpre,hpre,pre,ready⟩ := ServicePrepare.run D E time rom H J u s ins tape hg hH
  let a := x.putIndex 15 1
  have arm : Block.Eval (Memory.AllData P) (.op (.addrConst 15 1)) x 1 a :=
    Block.Eval.op_addrConst _ _ _ pre.safe_end pre.safe_end
  have checked : Ready D E J u cap s a := ServicePost.arm ready
  let b := ServiceFill.oddAddressBudget (live n g) n
  have dime (i : ℕ) : 2*(start dims xs).index i ≤ b := by
    have nL := (dimensions_le_live n g).1
    have gL := (dimensions_le_live n g).2.1
    have one := (dimensions_le_live n g).2.2
    have pm : pos.isSome.toNat ≤ 1 := Bool.toNat_le pos.isSome
    change 2*(dims[i]?.getD 0) ≤ b
    cases hx : dims[i]? with
    | none => simp
    | some v =>
      have hv := List.mem_of_getElem? hx
      simp only [dims,List.mem_cons,List.not_mem_nil,or_false] at hv
      dsimp [b,ServiceFill.oddAddressBudget]
      rcases hv with rfl | rfl | rfl | rfl <;> omega
  have room := (capacity_bounds time rom n g hg).2.1
  have fit : max (ServiceInvoke.numerical p).localBudget b + (2*k+2) ≤ cap := by
    change max rom b + (2*k+2) ≤ cap
    have widen : 2*k+2 ≤ 2*time.eval n+2 := by omega
    exact (Nat.add_le_add_left widen _).trans room
  obtain ⟨z,exp,ret⟩ := ServiceInvoke.run p P a dims xs cap b k (replyTag r) tr arm.safe_end dataSafe
    checked.evenScalar checked.evenAddress dime checked.oddBound fit
    (by have h := (capacity_bounds time rom n g hg).1; omega) htr
    (flast ▸ emittedTag em) (replyTag_lt r) bits'
  have actual := (Fragment.Run.ofBlock pre).seq ((Fragment.Run.ofBlock arm).seq exp)
  have ret' : ServiceInvoke.Returned a last.memory z cap (replyTag r) := flast ▸ ret
  have elapsed : kpre+(1+(2*k+2)) ≤ ServicePrepare.work time rom n J.card+1+(2*time.eval n+2) := by
    omega
  refine ⟨a,last,z,actual.mono elapsed,checked,ret',em,?_⟩
  exact (ret'.oddAddress 7 (by decide)).trans (by simp [a])

end ServiceDecision
end Compression
end LinearProgramming
end Optimization
end OAI
