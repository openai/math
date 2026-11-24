import OAI.Computability.VPVNP.LiveHeaderPhases

/-!
# Field intervals for the live incident cuts

In the unit mode all nonmode bits form a single zero-padding interval.
In the simulation mode the cut carries the exterior and exponents up
to and including the midpoint, then the evaluator configuration. Missing
cuts and empty payloads have no sites to visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderDescriptors

/-- The incoming left or outgoing right side of the group whose incident cut is being parsed. -/
inductive Side where | left | right deriving DecidableEq
/-- The payload or padding interval requested from a live incident cut. -/
inductive Field where | exterior | exponents | config | padding deriving DecidableEq
/-- The cut formats governing field lengths, covering absent endpoints, unit mode, paired
computation, and evaluator tail. -/
inductive Shape where | missing | unit | pair | tail deriving DecidableEq

/-- The first tail group's left cut is the midpoint, so it still has the
pair layout even though the group's own mode dispatch chose the tail. -/
def shape (side : Side) (width tag : ℕ) (firstHalf firstTail : Bool) : Shape :=
  if width = 0 then .missing else if tag = 0 then .unit else
    if firstHalf || (decide (side = .left) && firstTail) then .pair else .tail

/-- The index of the left or right incident cut of a one-based group. -/
def cutIndex (side : Side) (group : ℕ) := match side with | .left => group - 1 | .right => group

/-- The index-based flag dispatch produces the layout of the incident cut
itself. In particular the group just after the midpoint has different
layouts on its two sides. -/
theorem shape_at_group (h group tag : ℕ) (side : Side) (W : ℕ) :
    shape side W tag (decide (group ≤ 2^h)) (decide (group = 2^h+1)) =
      if W = 0 then .missing else if tag = 0 then .unit else
        if cutIndex side group ≤ 2^h then .pair else .tail := by
  cases side
  · have he : group ≤ 2^h ∨ group = 2^h+1 ↔ group-1 ≤ 2^h := by
      constructor
      · rintro (he | he)
        · exact (Nat.sub_le group 1).trans he
        · simp [he]
      · intro he
        by_cases hl : group ≤ 2^h
        · exact Or.inl hl
        · exact Or.inr (by omega)
    simp [shape, cutIndex, he]
  · simp [shape, cutIndex]; rfl

/-- Natural-number lengths for the three payloads, in their physical order. -/
def exterior (form : Shape) (W Δ : ℕ) : ℕ := if form = .pair then W-Δ else 0
/-- The occupied exponent length for a cut shape, equal to the supplied exponent size on a pair
cut. -/
def exponents (form : Shape) (e : ℕ) : ℕ := if form = .pair then e else 0
/-- The occupied configuration length for a cut shape, equal to the supplied configuration size
on a tail cut. -/
def config (form : Shape) (c : ℕ) : ℕ := if form = .tail then c else 0
/-- The length occupied by the leading mode bit, zero at a missing cut and one on a nonempty
cut. -/
def mode (W : ℕ) := if W = 0 then 0 else 1

/-- The offset of the requested field after the mode bit and preceding enabled payloads. -/
def start (form : Shape) (W Δ e c : ℕ) : Field → ℕ
  | .exterior => mode W
  | .exponents => mode W + exterior form W Δ
  | .config => mode W + exterior form W Δ + exponents form e
  | .padding => mode W + exterior form W Δ + exponents form e + config form c

/-- The occupied length of the specified field, assigning the remainder of the cut to padding. -/
def count (form : Shape) (W Δ e c : ℕ) : Field → ℕ
  | .exterior => exterior form W Δ
  | .exponents => exponents form e
  | .config => config form c
  | .padding => W - start form W Δ e c .padding

/-- No source address is used for an empty field; its offset word is zero. -/
def span (form : Shape) (W Δ e c : ℕ) (f : Field) : ℕ × ℕ :=
  let length := count form W Δ e c f
  (if length = 0 then 0 else start form W Δ e c f, length)

/-- The largest nonpadding prefix ends at or before the cut boundary. -/
theorem payload_le {form : Shape} {W Δ e c : ℕ} (he : 1+e ≤ Δ) (hc : 1+c ≤ Δ)
    (hp : form = .pair ∨ form = .tail → Δ ≤ W) :
    start form W Δ e c .padding ≤ W := by
  cases form <;> simp [start, exterior, exponents, config, mode] at * <;> split_ifs <;> omega

/-- After the mode bit these four consecutive fields cover every site. -/
theorem partition {form : Shape} {W Δ e c : ℕ} (he : 1+e ≤ Δ) (hc : 1+c ≤ Δ)
    (hp : form = .pair ∨ form = .tail → Δ ≤ W) :
    mode W + count form W Δ e c .exterior + count form W Δ e c .exponents +
      count form W Δ e c .config + count form W Δ e c .padding = W :=
  Nat.add_sub_of_le (payload_le he hc hp)

/-- Every emitted interval lies inside the supplied cut. -/
theorem span_fit {form : Shape} {W Δ e c : ℕ} (he : 1+e ≤ Δ) (hc : 1+c ≤ Δ)
    (hp : form = .pair ∨ form = .tail → Δ ≤ W) (f : Field) :
    (span form W Δ e c f).1 + (span form W Δ e c f).2 ≤ W := by
  have h := payload_le he hc hp
  change (if count form W Δ e c f = 0 then 0 else start form W Δ e c f) + count form W Δ e c f ≤ W
  split_ifs with hz
  · simp [hz]
  · cases f <;> simp only [count, start] at * <;> omega

/-- Every nonempty cut has at least one full block under equation (9.1). -/
theorem width_ge_block (H Δ j : ℕ) :
    CutSchedule.width H Δ j = 0 ∨ Δ ≤ CutSchedule.width H Δ j := by
  unfold CutSchedule.width
  split_ifs with hi
  · right
    have := Nat.log_lt_of_lt_pow hi.1.ne' hi.2
    simpa using Nat.mul_le_mul_right Δ (show 1 ≤ H - Nat.log 2 j by omega)
  · exact Or.inl rfl

theorem shape_fit {side : Side} {W Δ tag : ℕ} {half firstTail : Bool}
    (hW : W = 0 ∨ Δ ≤ W) :
    shape side W tag half firstTail = .pair ∨ shape side W tag half firstTail = .tail → Δ ≤ W := by
  rcases hW with rfl | h
  · simp [shape]
  · exact fun _ => h

/-- A pair-layout outgoing live cut carries exactly the primed exterior
at twice its index, including the midpoint where that exterior is empty. -/
theorem pair_exterior (h Δ i : ℕ) (hi : 0 < i) (hle : i ≤ 2^h) :
    exterior .pair (CutSchedule.width (h+1) Δ i) Δ = CutSchedule.width (h+1) Δ (2*i) := by
  simp [exterior, CutSchedule.width_double h Δ i hi hle]

/-- At the middle cut the exponents start immediately after the mode. -/
theorem midpoint_exterior (h Δ : ℕ) : exterior .pair (CutSchedule.width (h+1) Δ (2^h)) Δ = 0 := by
  rw [pair_exterior h Δ (2^h) (Nat.two_pow_pos h) le_rfl, ← pow_succ', CutSchedule.width_end]

end LiveHeaderDescriptors

end VPVNP
end Computability
end OAI
