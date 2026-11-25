import OAI.Computability.BorderVNP.RoutingISASignedArenaRate
import OAI.Computability.BorderVNP.RoutingISACubeSelectedRoom

/-! # A single physical word for all selected signed-stage memory addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Tally Filter

/-- Common scalar bounds for the true report dimensions, sparse encodings
and final residue circuit, independent of the observed operand counts. -/
structure Layout.ScalarRoom (l : Layout) (W u v gates S : ℕ) : Prop where
  /-- All report maxima, including full source slots and checked owned vertices. -/
  reports : l.p.report.Le S
  /-- Curve parameter count. -/
  parameters : l.p.parameters ≤ S
  /-- Private argument scratch stride, also bounding the sparse exterior encoding. -/
  scratch : l.p.scratchStride ≤ S
  /-- Maximum private burst window. -/
  burst : l.p.burstStride ≤ S
  /-- Machine word width. -/
  word : W ≤ S
  /-- Number of input pins in the selected residue circuit. -/
  query : u ≤ S
  /-- Number of free residue choices. -/
  choices : v ≤ S
  /-- Number of actual supplied Boolean gates. -/
  gates : gates ≤ S

/-- Every native stage through the final actual residue reader has its entire
address space below the physical word bound. The same cutoff works for all
batch sizes and length-only public layouts at the selected geometric and
curve-size ceilings. -/
theorem eventually_signed_word (n b h K s C D E : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let S := C*(r*t+1)^D
      ∀ (p : CubeArena.Sizes) (l : Layout) (W u v gates : ℕ), p.Le S →
        l.cube = p.selected n b h K s → l.ScalarRoom W u v gates S →
        l.endAddress W u v gates < 2^((TeamScales.logWidth r t)^(E+2)) := by
  obtain ⟨e,he⟩ := CubeArena.uniform_exponent n b h K s
  let table := 2+(CubeConstants.recipes n b h K s).length+2^(argumentWidth n b h K s)
  let A := (C+2)^e+table+192*(C+1)^3
  let F := max (D*e) (D*3)
  filter_upwards [Diagonal.eventually_polynomial_words A F E] with t room
  intro r hr S p l W u v gates sizes geometry fit
  let z := r*t+1
  let P := z^D
  have zp : 0 < z := by dsimp [z]; omega
  have hp : 1 ≤ P := Nat.one_le_pow _ _ zp
  have xs : S+2 ≤ (C+2)*P := by change C*P+2 ≤ _; rw [Nat.add_mul]; omega
  have ys : S+1 ≤ (C+1)*P := by change C*P+1 ≤ _; rw [Nat.add_mul]; omega
  have cubed : l.cube.stop ≤ (C+2)^e*z^F := by
    rw [geometry]
    have q := (he S p sizes).trans (Nat.pow_le_pow_left xs e)
    rw [mul_pow] at q
    exact q.trans (Nat.mul_le_mul_left _ (show P^e≤z^F by
      dsimp only [P,F]; rw [← pow_mul]; exact Nat.pow_le_pow_right zp (le_max_left _ _)))
  have cost : 192*(S+1)^3 ≤ (192*(C+1)^3)*z^F := by
    have q := Nat.pow_le_pow_left ys 3
    rw [mul_pow] at q
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (q.trans (Nat.mul_le_mul_left _ (show P^3≤z^F by
      dsimp only [P,F]; rw [← pow_mul]; exact Nat.pow_le_pow_right zp (le_max_right _ _))))
  have shapes : l.cube.n=n ∧ l.cube.b=b ∧ l.cube.h=h ∧ l.cube.K=K ∧ l.cube.s=s := by
    rw [geometry]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have size : CubeConstants.arenaEnd l.cube.stop l.id = l.cube.stop+table := by
    simp only [CubeConstants.arenaEnd,CubeConstants.idBase,CubeConstants.ids,List.length_ofFn,
      shapes.1,shapes.2.1,shapes.2.2.1,shapes.2.2.2.1,shapes.2.2.2.2,table,Nat.add_assoc]
  have counts : l.cube.cells ≤ S ∧ l.cube.teams ≤ S ∧ l.cube.cables ≤ S ∧ l.cube.maxRows ≤ S := by
    rw [geometry]; exact ⟨sizes.2.2.2.1,sizes.2.2.2.2.2.2.1,sizes.2.2.2.2.1,sizes.2.2.2.2.2.1⟩
  have actual := l.end_le W u v gates S fit.reports counts.1 counts.2.1 counts.2.2.1 counts.2.2.2
    fit.parameters fit.scratch fit.burst fit.word fit.query fit.choices fit.gates
  rw [size] at actual
  have constant : table ≤ table*z^F := Nat.le_mul_of_pos_right _ (Nat.pow_pos zp)
  apply (actual.trans _).trans_lt (room r hr)
  change _ ≤ A*z^F
  dsimp only [A]
  rw [Nat.add_mul,Nat.add_mul]
  omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
