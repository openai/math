import OAI.Computability.IntegerMultiplication.Strip.Rails
import OAI.Computability.IntegerMultiplication.Code.Recurse

/-!
# Closing fixed-stage interchange programs on the P192 stack machine

The intermediate arrays can contain different record layouts at different stages.
A stage certificate is a P192 `Tunnel`, which charges a concrete command for
local stack instructions and charges each recursive call at the child's fare.
The only recursive command is P192's fixed `again 0`; the solver ties it once.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication.Code

/-- Sequence a statically known list of stage certificates, retaining their
actual child calls with multiplicity. The command and its local multiplicative
constant are independent of both the input and the recursion depth. -/
theorem interchange_stage_sequence {X I : Type*} (o : Oracle X)
    (localWork : I → ℝ) (hW : ∀ i, 1 ≤ localWork i)
    (layout : ℕ → I → Tree) (children : ℕ → I → List X)
    (stages : ℕ)
    (hstage : ∀ t < stages,
      Tunnel o localWork (children t) (layout t) (layout (t + 1))) :
    Tunnel o localWork (fun i => (List.range stages).flatMap (fun t => children t i))
      (layout 0) (layout stages) := by
  induction stages with
  | zero =>
    refine ⟨hW, .pass, 1, fun i _ _ _ _ r => ?_⟩
    apply (Meter.cast (Fits.pass _)).mono
    simpa [Oracle.reserve] using hW i
  | succ t ih =>
    have h := (ih (fun j hj => hstage j (by omega))).join (hstage t (by omega))
    simpa [List.range_succ] using h

/-- Focus a recursive call on one row of a fixed batch. The child starts
with its encoded query above the parked row packet. On return the old row is
replaced by the reply and every other row is restored. Both surrounding
rearrangements are charged to the local work, and the oracle is called once. -/
theorem interchange_call_on_row {X I K : Type} [DecidableEq K] (o : Oracle X)
    (rows : IntegerMultiplication.Strip.Series K) (k : K) (row : I → K → Tree)
    (child : I → X) (w : I → ℝ) (input : I → Tree)
    (hrows : Carries w input (fun i => IntegerMultiplication.Strip.stripe rows (row i)))
    (hquery : Carries w input (o.query ∘ child)) (hout : Volume w (o.reply ∘ child)) :
    Tunnel o w (fun i => [child i]) input
      (fun i => IntegerMultiplication.Strip.stripe rows
        (Function.update (row i) k (o.reply (child i)))) := by
  let packet i := IntegerMultiplication.Strip.stripe rows (row i)
  have hw := hquery.budget
  have enter := Tunnel.walkway (o := o) (hquery.twice hrows).runs
  have visit := (Tunnel.summon (o := o) child hw).surround packet
  let parked i := Tree.fork (o.reply (child i)) (packet i)
  have parkedVolume : Volume w parked := hout.fork hrows.out hw
  have recover : Carries w parked (fun i => IntegerMultiplication.Strip.stripe rows
      (Function.update (row i) k (o.reply (child i)))) := by
    apply IntegerMultiplication.Strip.finite_series rows _ parkedVolume hw
    intro l
    by_cases hl : l = k
    · subst l
      simpa [parked, packet, Function.comp_def] using Carries.dropRight hw hout hrows.out
    · simpa [parked, packet, IntegerMultiplication.Strip.stackRun, Function.comp_def, Function.update_of_ne hl] using IntegerMultiplication.Strip.finite_cell rows row
        (Carries.dropLeft hw hout hrows.out) l
  simpa using (enter.join visit).join (Tunnel.walkway recover.runs)

/-- The total volume bound and the common width contraction leave a fixed
positive fraction of the parent fare for local work. -/
theorem interchange_fare_slack {X : Type*} (width volume : X → ℕ) (calls : X → List X)
    (m : ℕ) (α θ : ℝ) (hm : 1 < m) (hα : 0 ≤ α) (hcontract : θ < (m : ℝ) ^ α)
    (hchild : ∀ x y, y ∈ calls x → width y * m ≤ width x)
    (htotal : ∀ x, ((calls x).map (fun y => (volume y : ℝ))).sum ≤ θ * volume x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x,
      ((calls x).map (fun y => (volume y : ℝ) * (width y : ℝ) ^ α)).sum +
        ε * ((volume x : ℝ) * (width x : ℝ) ^ α) ≤ (volume x : ℝ) * (width x : ℝ) ^ α := by
  let M := (m : ℝ) ^ α
  have hM : 0 < M := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
  have hsmall (x y : X) (h : y ∈ calls x) :
      (width y : ℝ) ^ α ≤ (width x : ℝ) ^ α / M := by
    apply (le_div_iff₀ hM).mpr
    dsimp [M]
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hchild x y h) hα
  refine ⟨1 - θ / M, sub_pos.mpr ((div_lt_one hM).mpr hcontract), fun x => ?_⟩
  have hsum (l : List X) (h : ∀ y ∈ l, y ∈ calls x) :
      (l.map (fun y => (volume y : ℝ) * (width y : ℝ) ^ α)).sum ≤
      (l.map (fun y => (volume y : ℝ))).sum * ((width x : ℝ) ^ α / M) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hsmall _ _ (h _ (by simp))) (by positivity))
        (ih (by simp_all))
  have hreserved := (hsum (calls x) (fun _ => id)).trans
    (mul_le_mul_of_nonneg_right (htotal x) (div_nonneg (by positivity) hM.le))
  calc
    _ ≤ θ * volume x * ((width x : ℝ) ^ α / M) +
        (1 - θ / M) * (volume x * (width x : ℝ) ^ α) := add_le_add hreserved le_rfl
    _ = _ := by ring

/-- Given a single certified stage body with the manuscript's local and
recursive-volume charges, compile a single recursive stack program whose
concrete running time is at most a constant times `volume * width^α`. The
coefficient `θ` accommodates both the small padded main calls and the
full-volume reserve calls. -/
theorem interchange_recursive_program {X : Type*}
    (width volume : X → ℕ) (calls : X → List X) (input output : X → Tree)
    (m : ℕ) (α θ : ℝ) (hm : 1 < m) (hα : 0 ≤ α)
    (hwidth : ∀ x, 0 < width x) (hvol : ∀ x, 0 < volume x)
    (hcontract : θ < (m : ℝ) ^ α)
    (hchild : ∀ x y, y ∈ calls x → width y * m ≤ width x)
    (htotal : ∀ x, ((calls x).map (fun y => (volume y : ℝ))).sum ≤ θ * volume x)
    (hbody : Tunnel
      ⟨fun x => (volume x : ℝ) * (width x : ℝ) ^ α, input, output⟩
      (fun x => (volume x : ℝ)) calls input output) :
    Sized (fun x => (volume x : ℝ) * (width x : ℝ) ^ α) input output := by
  have hOne (x : X) : 1 ≤ (width x : ℝ) ^ α :=
    Real.one_le_rpow (by exact_mod_cast hwidth x) hα
  have hdom (x : X) : (volume x : ℝ) ≤ (volume x : ℝ) * (width x : ℝ) ^ α :=
    le_mul_of_one_le_right (by positivity) (hOne x)
  obtain ⟨ε, pos, slack⟩ := interchange_fare_slack width volume calls m α θ hm hα hcontract
    hchild htotal
  refine Tunnel.solve _ hbody (fun x => (show (1 : ℝ) ≤ volume x by
    exact_mod_cast hvol x).trans (hdom x)) hdom ε pos slack width ?_
  intro x y hy
  exact lt_of_lt_of_le (by
    have := Nat.mul_lt_mul_of_pos_left hm (hwidth y)
    simpa using this) (hchild x y hy)

end NearSquareRoot
end Computability
end OAI
