import OAI.Computability.BorderVNP.CubeScatterDigits

/-! # Write confinement for arbitrary routed machine words

The byte ISA copies the raw source word, whatever its value. Every position
advances the destination by exactly one word, and no store can modify an
address outside the consecutive destination rectangle. This fact applies to
returning malformed declarations before decoding their crossing payload.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

variable {w : ℕ}

private theorem raw_step (d : Digit) (r : Bank w) (m : Memory w) (base : ℕ)
    (one : r 59 = 1) (address : r 38 = word w base) (room : base < 2^w) :
    let e := d.step r m
    e.bank 38 = word w (base+1) ∧ (∀ j : Reg, j ∉ ([36,37,38,60] : List Reg) → e.bank j = r j) ∧
      (∀ x, x ≠ base → e.mem x = m x) ∧ (d.mode ≠ .selector → e.bank 36 = r 36) := by
  have inc : word w base+1 = word w (base+1) := (word_add w base 1).symm
  cases d with
  | privateBit bit =>
    cases bit <;> simp (config := {decide := true}) [Digit.step,Digit.mode,Mode.code,writeLocal,
      Code.block,effect,BinaryOp.eval,Function.update,one,address,inc,-word_add,word_val _ _ room] <;>
      constructor <;> first | (intro j h36 h37 h38 h60; simp_all) | (intro x hx eqn; exact (hx eqn).elim)
  | selector | crossing | unused =>
    simp (config := {decide := true}) [Digit.step,Digit.mode,Mode.code,copyDigit,
      Code.block,effect,BinaryOp.eval,Function.update,one,address,inc,-word_add,word_val _ _ room]
    first | (constructor <;> first | (intro j h36 h37 h38 h60; simp_all) | (intro x hx eqn; exact (hx eqn).elim))
            | (intro j h36 h37 h38 h60; simp_all)

/-- Exact destination and memory confinement of any realized native digit sequence.
Only selector digits can move the selector cursor. No premise constrains the
crossing cursor, the copied words, or the values of private choices. -/
theorem result_frame (ds : List Digit) (r : Bank w) (m : Memory w) (base : ℕ)
    (one : r 59 = 1) (address : r 38 = word w base) (room : base+ds.length ≤ 2^w) :
    let e := result ds r m
    e.bank 38 = word w (base+ds.length) ∧
      (∀ j : Reg, j ∉ ([36,37,38,60] : List Reg) → e.bank j = r j) ∧
      (∀ x, x < base ∨ base+ds.length ≤ x → e.mem x = m x) ∧
      (Mode.selector ∉ ds.map Digit.mode → e.bank 36 = r 36) := by
  induction ds generalizing base r m with
  | nil => exact ⟨address,fun _ _ => rfl,fun _ _ => rfl,fun _ => rfl⟩
  | cons d ds ih =>
    simp only [List.length_cons] at room ⊢
    obtain ⟨ptr,keep,away,sel⟩ := raw_step d r m base one address (by omega)
    obtain ⟨ptr',keep',away',sel'⟩ := ih (d.step r m).bank (d.step r m).mem (base+1)
      ((keep 59 (by decide)).trans one) ptr (by omega)
    refine ⟨by simpa only [result,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm 1] using ptr',
      fun j hj => (keep' j hj).trans (keep j hj),fun j hj => (away' j (by omega)).trans (away j (by omega)),?_⟩
    intro no
    simp only [List.map_cons,List.mem_cons,not_or] at no
    exact (sel' no.2).trans (sel (Ne.symm no.1))

end Cube.Scatter

end BorderVNP
end Computability
end OAI
