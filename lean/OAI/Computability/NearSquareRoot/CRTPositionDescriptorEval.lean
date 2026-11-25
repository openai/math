import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import OAI.Computability.NearSquareRoot.CRTPositionMirror
import OAI.Computability.NearSquareRoot.CRTControlledPositions

/-! # Correctness of the executable bit-position reflection tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Reflections

open IntegerMultiplication.Code

variable {k : ℕ} (p : Equiv.Perm (Fin k)) (x : Fin k)

private def seen (n : ℕ) : Pair := (tally ((p^n) x).val,tally ((p^(2*n)) x).val)

private theorem next_cursors (n : ℕ) (saved : Pair) :
    cursors (table p,seen p x n,saved) = seen p x (n+1) := by
  simp only [cursors,seen,next_table]
  rw [show 2*(n+1) = (2*n+1)+1 by omega]
  simp only [pow_succ',Equiv.Perm.mul_apply]

private theorem scan_invariant (n : ℕ) :
    ∃ j ≤ n, (∀ t ≤ n, (p^j) x ≤ (p^t) x) ∧
      (fun s => step (table p,s))^[n]
        ((tally x.val,tally x.val),tally x.val,tally x.val) = (seen p x n,seen p x j) := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun _ h => (Nat.eq_zero_of_le_zero h) ▸ le_rfl,rfl⟩
  | succ n ih =>
    obtain ⟨j,hj,least,state⟩ := ih
    rw [Function.iterate_succ_apply',state]
    simp only [step,next_cursors]
    by_cases h : (p^(n+1)) x < (p^j) x
    · refine ⟨n+1,le_rfl,?_,?_⟩
      · intro t ht
        rcases Nat.lt_or_ge n t with ht' | ht'
        · rw [show t = n+1 by omega]
        · exact h.le.trans (least _ ht')
      · simp [record,seen,Iter.small,h]
    · refine ⟨j,by omega,?_,?_⟩
      · intro t ht
        rcases Nat.lt_or_ge n t with ht' | ht'
        · rw [show t = n+1 by omega]
          exact le_of_not_gt h
        · exact least _ ht'
      · simp [record,seen,Iter.small,h]

/-- The executable program returns both images of a given position. -/
theorem reflectPair_spec :
    reflectPair (table p,tally x.val) = (tally (forwardMirror p x).val, tally (p (forwardMirror p x)).val) := by
  obtain ⟨j,hj,least,state⟩ := scan_invariant p x k
  obtain ⟨t,ht,hit⟩ := orbitMin_hit p x
  have eq : (p^j) x = orbitMin p x :=
    le_antisymm (hit ▸ least t ht) (orbitMin_le_power p x ⟨j, by omega⟩)
  have m : (p^(2*j)) x = forwardMirror p x := by
    rw [forwardMirror_of_power p x j eq,← eq,two_mul,pow_add,Equiv.Perm.mul_apply]
  have run : scan (table p,tally x.val) = (seen p x k,seen p x j) := by
    simpa only [scan,table,List.length_ofFn] using state
  simp only [reflectPair,run,seen,m,next_table]

/-- P192's compiled table agrees with both reflection permutations at every position. -/
theorem make_spec : make (table p) =
    List.ofFn (fun x : Fin k => (tally (forwardMirror p x).val, tally (p (forwardMirror p x)).val)) := by
  have r : ruler (table p) = tally k := by
    rw [← recover_tally (ruler (table p)),ruler_length,table,List.length_ofFn]
  simp only [make,polyPush,r,Iter.lined,List.map_ofFn,Function.comp_def,reflectPair_spec]

/-- The two permutations whose actual lookup tables the program returns. -/
def first : Equiv.Perm (Fin k) :=
  ⟨forwardMirror p,forwardMirror p,forwardMirror_involutive p,forwardMirror_involutive p⟩

def second : Equiv.Perm (Fin k) :=
  ⟨p ∘ forwardMirror p,p ∘ forwardMirror p,shiftedMirror_involutive p,shiftedMirror_involutive p⟩

theorem factor : (first p).trans (second p) = p := forwardMirror_factor p

theorem prepare_spec : prepare (table p) = (table (first p),table (second p)) := by
  simp only [prepare,make_spec,List.map_ofFn]
  rfl

/-- One P192 command produces the two reflection tables in time polynomial in
the number of positions, uniformly over all permutation sizes and inputs. -/
theorem prepare_uniform {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x))) :
    Task.BT k (fun x => send (table (p x))) (fun x => send (table (first (p x)),table (second (p x)))) := by
  have h := poly_prepare.on (q := fun x => table (p x)) (p := k)
    (show Dom k (fun x => size (table (p x))) from ⟨2,2,fun x => table_size (p x)⟩)
  simpa only [prepare_spec] using h

/-- Each reflected table is precisely one of the two matchings routed on the
three consecutive chunks and up to two remaining positions. -/
theorem preparedMatchingRounds :
    let e := threeChunksWithTail k
    ∀ q ∈ [first p,second p], ∃ round : PositionRound (Fin 3) (Fin (k/3)) (k%3),
      round.layers.length ≤ 81 ∧ round.singles.length ≤ 2 ∧
      ∀ w : Fin k → Bool, (round.act (w ∘ e.symm)) ∘ e = w ∘ q := by
  dsimp only
  let e := threeChunksWithTail k
  intro q hq
  have inv : Function.Involutive q := by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact forwardMirror_involutive p
    · rw [List.mem_singleton.mp hq]
      exact shiftedMirror_involutive p
  let v := (e.symm.trans q).trans e
  have hv : Function.Involutive v := by
    intro y
    simp [v,inv (e.symm y)]
  obtain ⟨round,single,gates,spec⟩ := involutionRound v hv
  refine ⟨round,by simpa using gates,by omega,fun w => ?_⟩
  rw [spec]
  funext j
  simp [v,Function.comp_def,e]

end Controlled.Reflections

end NearSquareRoot
end Computability
end OAI
