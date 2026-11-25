import OAI.Computability.NearSquareRoot.CRTPositionProgramBounded
import OAI.Computability.NearSquareRoot.CRTPositionChunkView

/-! # The emitted residue schedule for an aligned slot XOR

A native window contains the source, destination, and auxiliary chunks in
most-significant-first order. Each of the source bits controls its aligned bit
of the destination. Every opcode reindexes complete rows of spectator data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorSweep

open IntegerMultiplication Code Staff Strip Space Controlled Controlled.PositionProgram Controlled.PositionPreparation

/-- Native position programs number their three chunks from least to most significant. -/
def gate (n : ℕ) : Gate := (2,1,List.ofFn (fun j : Fin n => unaryPort (some j)))

def program (n G : ℕ) := expand ((tally n,tally G),gate n)

theorem program_length (n G : ℕ) : (program n G).length ≤ 4+3*G := expand_length ..

theorem program_valid {k G : ℕ} (q : Op) (h : q ∈ program (k/3) G) : WellFormed k G q :=
  expand_valid _ _ h

/-- Pulling back a row by the complete schedule applies the single directed
XOR, an involution. The result is valid at every address in the window. -/
theorem program_rows {k G : ℕ} {Y : Type*} (hg : 0 < G) (f : (Fin k → Bool) → Y) :
    (program (k/3) G).foldl (fun b q => b ∘ fun w => act G w q) f = f ∘ directed (gate (k/3)) := by
  have hsd : (gate (k/3)).1 ≠ (gate (k/3)).2.1 := by change (2:Fin 3) ≠ 1; decide
  have twice (w : Fin k → Bool) : directed (gate (k/3)) (directed (gate (k/3)) w) = w := by
    funext j
    obtain ⟨v,rfl⟩ := (threeChunksWithTail k).symm.surjective j
    cases v with
    | inr j => simp [directed]
    | inl v =>
      rcases v with ⟨c,j⟩
      fin_cases c <;> simp [gate,directed,decodePort_encoded,chunkWord,xorFrom]
  funext w
  have h := rows_forward G (program (k/3) G) f (directed (gate (k/3)) w)
  simpa only [program,expand_action G hg (gate (k/3)) hsd,twice,Function.comp_apply] using h

/-- The complete unary read table is manufactured by a polynomial header
program from the group width. No input row is consulted. -/
theorem program_has {X : Type} {r : Regime X} {n G : X → ℕ} (hn : Realizes r n) (hG : Realizes r G) :
    r.Has (fun x => program (n x) (G x)) := by
  have ports := (hn.thenDo Iter.poly_line).ez ((Easy.some (X:=Tally)).mapping)
  have indices : r.Has (fun x => (gate (n x)).2.2) := by
    convert ports using 2 with x
    simp [gate,Iter.lineup,unaryPort,List.map_ofFn,Function.comp_def]
  exact ((hn.pair hG).pair ((Regime.fixed (2 : Fin 3)).pair ((Regime.fixed (1 : Fin 3)).pair indices))).thenDo expand_poly

/-- Execute the actual header forest in logarithmically many charged passes.
The descriptor and intermediate arrays occupy the same bounded workspace. -/
theorem boundedProgram {X : Type} {Y : X → Type} (k G : X → ℕ) (positive : ∀ x, 0 < G x)
    (key : X → Op → Tree) (box : (x : X) → ((Fin (k x) → Bool) → Y x) → Tree)
    (budget volume : X → ℕ) (charge : X → Op → ℕ)
    (stage : BoundedTask (fun j : (x : X) × {q // q ∈ program (k x/3) (G x)} × ((Fin (k x) → Bool) → Y x) => charge j.1 j.2.1)
      (fun j => volume j.1) (fun j => .fork (key j.1 j.2.1) (box j.1 j.2.2))
      (fun j => box j.1 (j.2.2 ∘ fun w => act (G j.1) w j.2.1)))
    (forest : ∀ x, (Task.forest (key x) (program (k x/3) (G x))).count ≤ volume x)
    (live : ∀ x f, (box x f).count ≤ volume x)
    (cost : ∀ x, ∀ q ∈ program (k x/3) (G x), charge x q + (key x q).count + 1 ≤ budget x) :
    BoundedTask (fun j : (x : X) × ((Fin (k x) → Bool) → Y x) => (4+3*G j.1)*budget j.1+1)
      (fun j => volume j.1)
      (fun j => .fork (Task.forest (key j.1) (program (k j.1/3) (G j.1))) (box j.1 j.2))
      (fun j => box j.1 (j.2 ∘ directed (gate (k j.1/3)))) := by
  have run := boundedSchedule (fun x => program (k x/3) (G x)) key box (fun x f q => f ∘ fun w => act (G x) w q)
    charge budget volume stage forest live cost
  exact (run.mono (fun j => Nat.succ_le_succ (Nat.mul_le_mul_right _ (program_length _ _))) (fun _ => le_rfl)).conform
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun j => congrArg (box j.1) (program_rows (positive j.1) j.2))

end PhysicalWalsh.XorSweep

end NearSquareRoot
end Computability
end OAI
