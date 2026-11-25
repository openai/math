import OAI.Computability.NearSquareRoot.ScheduleSchoolPrograms
import OAI.Computability.NearSquareRoot.ScheduleSchoolSegments
import OAI.Computability.NearSquareRoot.ScheduleSchoolDispatch

/-! # Bounded stack-machine run of the schoolbook fallback -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- One deterministic stack machine performs every digit pass. The stack
height bound holds at every intermediate step, including inside the compiled
adder and the input/output conversions. -/
theorem schoolbook_stack :
    ∃ (p : Dispatch.Programs) (D : ℕ), ∀ (n : ℕ) (x y : Word),
      x.length = n → y.length = n → ∃ t z,
        Segment p.rule (SM.origin p.start p.output ((operandStream x y).map Sum.inl)) t
          (p.done (raw (z.map Ltr.bit))) (D * (n+1)) ∧
        t ≤ D*(n+2)^2 ∧ z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  obtain ⟨a,b,c,B,programs⟩ := schoolbook_programs
  let p : Dispatch.Programs := ⟨a,b,c⟩
  refine ⟨p, 8+(B+2), fun n x y hx hy => ?_⟩
  obtain ⟨⟨u,hu,load⟩,step,⟨v,hv,emit⟩⟩ := programs x y n hx hy
  let H := 8 * (n+1)
  let L := (B+2) * (n+1)
  let cfg (i : ℕ) := p.ready (raw (encoded (boundary x y i)))
  have cb {t : ℕ} (ht : t ≤ B*(n+1)) : 2+t ≤ L := by
    dsimp [L]
    rw [Nat.add_mul]
    omega
  have state_bound {i : ℕ} (hi : i ≤ y.length) :
      ∀ j, ((cfg i).stack j).length ≤ H := by
    intro j
    apply (p.ready_height _ _).trans
    have h := encoded_bound hx.le hy.le hi
    dsimp [H]
    omega
  have initial_bound : ∀ j, ((p.initial (raw (operandStream x y))).stack j).length ≤ H := by
    intro j
    apply (p.initial_height _ _).trans
    simp [operandStream, hx, hy, H]
    omega
  have first : Segment p.rule (p.initial (raw (operandStream x y))) u (cfg 0) (H+L) :=
    Segment.of_cost (p.run_load load) initial_bound ((Nat.le_add_left u 2).trans (cb hu))
  have s (i : ℕ) (hi : i < y.length) : ∃ t ≤ L, Segment p.rule (cfg i) t (cfg (i+1)) (H+L) := by
    obtain ⟨t,ht,run⟩ := step i hi
    exact ⟨2+t, cb ht, Segment.of_cost (p.run_step (encoded_head _) (active_tag x y hi) run)
      (state_bound hi.le) (cb ht)⟩
  obtain ⟨w,hw,middle⟩ := segments_iterate (m := p.rule) y.length
    (fun j => (state_bound (Nat.zero_le _) j).trans (Nat.le_add_right H L)) s
  let z := finish (boundary x y y.length)
  have last : Segment p.rule (cfg y.length) (2+v) (p.done (raw (z.map Ltr.bit))) (H+L) :=
    Segment.of_cost (p.run_emit (encoded_head _) (finish_tag x y) emit)
      (state_bound le_rfl) (cb hv)
  have all := (first.trans middle).trans last
  rw [p.initial_origin, show H+L = (8+(B+2))*(n+1) by simp [H,L,Nat.add_mul]] at all
  have ez := output_exact x y
  refine ⟨_,z,all,?_,by simpa [z,boundary,hx,hy,two_mul] using ez.1,ez.2⟩
  have hu' : u ≤ L := (Nat.le_add_left u 2).trans (cb hu)
  have hv' := cb hv
  rw [hy] at hw
  calc
    u + w + (2+v) ≤ (n+2)*L := by rw [Nat.add_mul]; omega
    _ = (B+2) * ((n+2)*(n+1)) := by dsimp [L]; ring
    _ ≤ (8+(B+2)) * (n+2)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))

end Schoolbook

end NearSquareRoot
end Computability
end OAI
