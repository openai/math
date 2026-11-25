import OAI.Computability.NearSquareRoot.InterchangeCompiledAtlas
import OAI.Computability.NearSquareRoot.InterchangeSpectralRequest

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RectangleAtlas.Frame

open IntegerMultiplication.Port IntegerMultiplication.Loom IntegerMultiplication.Adic
  IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  NearSquareRoot.InterchangeSlots InterchangeSpectralRequest Support

private theorem swapAt_twice {J T : Type} [DecidableEq J] {P G B : Tape}
    (j : J) (x : Keys P G B J T) : swapAt j (swapAt j x) = x := by
  rcases x with ⟨p,h,g,d,t⟩
  simp [swapAt]

private theorem chase_swapAt {b f : ℕ} [NeZero b] {P G B : Tape} {J : Type} [DecidableEq J]
    (j : J) (x : Keys P G B J (Block b f)) :
    Lag.fire f (chase x) (.pivot j j) = chase (swapAt j x) := by
  apply hear_all
  rintro ⟨_ | _, k⟩ <;> by_cases h : k = j <;> simp [Lag.fire,hear,place,chase,swapAt,h]

variable {L B : Type} {r : B → Rectangle L} {a b m : ℕ} [NeZero b]
  {A : RectangleAtlas r a} (g : Frame A m b)

/-- Native pullback on every fibre is the literal exchange used by the
recursive query request, including the unchanged header spectators. -/
theorem native_pull (j : Fin m) (v : L) (P G B : Tape) (f : ℕ)
    (x : Keys P G B (Fin (a+m+a)) (Block b f)) :
    let D := extendLayout P G B (g.layout f)
    (D.S j v).symm (D.T j v x) = swapAt (mainRank a j) x := by
  let D := extendLayout P G B (g.layout f)
  let σ := (D.S j v).trans (D.T j v).symm
  have out (y : Keys P G B (Fin (a+m+a)) (Block b f)) : σ y = swapAt (mainRank a j) y := by
    have h := congrArg (fun e : Equiv.Perm _ => e y) (g.native_diagonal j v P G B f)
    apply h.trans
    apply square.injective
    exact (fore (Equiv.refl _) [.pivot (mainRank a j) (mainRank a j)] (by simp [Lag.legal]) y).trans
      (congrArg (fun u => (u,watcher y)) (chase_swapAt (mainRank a j) y))
  change σ.symm x = _
  apply σ.injective
  rw [Equiv.apply_symm_apply,out,swapAt_twice]

end Interchange.RectangleAtlas.Frame

end NearSquareRoot
end Computability
end OAI
