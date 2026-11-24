import OAI.Computability.VPVNP.MacaulayReadFinish

/-! # Whole execution of a coefficient or powered-row arm

Every call starts with empty exponent and flag buffers, and returns with both
empty. An equation lookup is invoked only when all monomial coordinates can
be subtracted. A powered row selects a constant encoding directly. The space
budget accounts for a single live exponent buffer and a single scalar call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open BurstRAM RAMTape UniversalCountStack MacaulayRowDispatch RadicalCertificate.MonomialIndex

variable {K : Type} [DecidableEq K]

/-- Run the appropriate monomial scan for an equation or powered row, then use its flag to
complete the scalar lookup. -/
def phase (power : Bool) (leaf : FiniteRoutine (Ports K)) : FiniteRoutine (Ports K) :=
  let scan := if power then PairCall.powered else PairCall.equation
  (scan.onPorts (pairPorts power)).followedBy (finish power leaf)

/-- Both of the Boolean-indexed temporary buffers contain empty bit stacks. -/
abbrev blank : Bool → List Bool := fun _ => []

/-- Place the given bits in the chosen buffer and leave the other buffer empty. -/
def selected (b : Bool) (xs : List Bool) : Bool → List Bool := Function.update blank b xs

private theorem erase_selected (b : Bool) (x : List Bool) : Function.update (selected b x) b [] = blank := by
  rw [selected, Function.update_idem, show [] = blank b from rfl, Function.update_eq_self]

/-- Common space for registers, immutable data, a dense residual vector and
flag, and either a scalar copy or final buffer cleanup. -/
def transient (A t w : ℕ) := (A + t*w+w) + (5*A + t*w+w+4)

/-- Tick allowance after the monomial scan, including scalar selection or evaluation and
cleanup of the exponent and flag buffers. -/
def postTicks (A t w scalarTicks : ℕ) := 2 + max (5*A+2) scalarTicks + (t*w+1+(w+1))

/-- A common stack bound for the register words, unary arity markers, scalar constants and
auxiliary reader advice. -/
structure Preload {w : ℕ} (A : ℕ) (data : Bool → PairCall.Inputs) (constants : Bool → List Bool)
    (aux : Stacks K) : Prop where
  words : w ≤ A
  arity : ∀ b, (data b).arity ≤ A
  scalars : ∀ b, (constants b).length ≤ A
  payload : ∀ k, (aux k).length ≤ A

omit [DecidableEq K] in
private theorem phase_room {w A t : ℕ} {data : Bool → PairCall.Inputs} {constants : Bool → List Bool} {aux : Stacks K}
    (pre : Preload (w := w) A data constants aux) (rs : Reg → Word w) (res : List Bool)
    (hr : res.length ≤ A) (b : Bool) (buf flag : List Bool) (hp : buf.length ≤ t*w) (hf : flag.length ≤ w) :
    ∀ z, (frame rs res (storage w data (selected b buf) (selected b flag) constants aux) z).length ≤ A+t*w+w := by
  apply frame_bound
  · omega
  · omega
  · intro j; exact (pre.arity j).trans (by omega)
  · intro j; by_cases hj : j=b <;> simp [selected, blank, hj]; omega
  · intro j; by_cases hj : j=b <;> simp [selected, blank, hj]; omega
  · intro j; exact (pre.scalars j).trans (by omega)
  · intro j; exact (pre.payload j).trans (by omega)

/-- Append a flag-selected coefficient or constant call to a native scan,
then reset both buffers. A coefficient routine may consume its exponent
buffer or leave it for the common cleanup stage. -/
theorem complete_phase {w A S t scanTicks leafTicks : ℕ} (hw : 1 ≤ w) (b matched : Bool)
    (rs : Reg → Word w) (data : Bool → PairCall.Inputs) (constants : Bool → List Bool) (aux : Stacks K)
    (pre : Preload (w := w) A data constants aux) (hs : transient A t w ≤ S)
    (leaf : FiniteRoutine (Ports K)) (buf result : List Bool) (hp : buf.length ≤ t*w) (hv : result.length ≤ A)
    (scan : ∃ cost ≤ scanTicks, ((if b then PairCall.powered else PairCall.equation).onPorts (pairPorts b)).BoundedRun S cost
      (frame rs [] (storage w data blank blank constants aux))
      (frame rs [] (storage w data (selected b buf) (selected b (digits w matched.toNat)) constants aux)))
    (yes : matched = true → ∃ n ≤ leafTicks, ∃ rest : List Bool, rest.length ≤ t*w ∧
      leaf.BoundedRun S n (frame rs [] (storage w data (selected b buf) (selected b (digits w matched.toNat)) constants aux))
        (frame rs result (storage w data (selected b rest) (selected b (digits w matched.toNat)) constants aux))) :
    ∃ n ≤ scanTicks + postTicks A t w leafTicks, (phase b leaf).BoundedRun S n
      (frame rs [] (storage w data blank blank constants aux))
      (frame rs (if matched then result else constants false) (storage w data blank blank constants aux)) := by
  obtain ⟨u,hu,scanrun⟩ := scan
  let flag := selected b (digits w matched.toNat)
  have hflag : flag b = digits w matched.toNat := Function.update_self ..
  have hf : (flag b).length = w := hflag ▸ length_digits ..
  have work : ∃ n ≤ max (5*A+2) leafTicks, ∃ rest : List Bool, rest.length ≤ t*w ∧
      (if matched then leaf else emit false).BoundedRun S n (frame rs [] (storage w data (selected b buf) flag constants aux))
        (frame rs (if matched then result else constants false) (storage w data (selected b rest) flag constants aux)) := by
    cases matched with
    | true =>
      obtain ⟨n,hn,rest,hr,h⟩ := yes rfl
      exact ⟨n,hn.trans (le_max_right ..),rest,hr,h⟩
    | false =>
      have hl : 5*(constants false).length+2 ≤ 5*A+2 := by have := pre.scalars false; omega
      refine ⟨_,hl.trans (le_max_left ..),buf,hp,spaceRun_of_steps (emit_runs rs false data (selected b buf) flag constants aux) ?_⟩
      intro z
      have hm := phase_room pre rs [] (by simp) b buf (digits w 0) hp (by simp) z
      change _ + _ ≤ S
      dsimp only [transient] at hs
      exact (Nat.add_le_add hm hl).trans (by omega)
  obtain ⟨n,hn,rest,hr,call⟩ := work
  have hor : (if matched then result else constants false).length ≤ A := by cases matched; exact pre.scalars false; exact hv
  have done := finish_bounded rs b matched data (selected b buf) flag constants aux leaf _ (selected b rest) hw hflag call (fun z => by
    have cap := phase_room pre rs _ hor b rest (digits w matched.toNat) hr (by simp) z
    have hlen : (selected b rest b).length = rest.length := by simp [selected]
    dsimp only [transient] at hs
    change _ + (_ + 1 + (_ + 1)) ≤ S
    exact (Nat.add_le_add cap (show (selected b rest b).length + 1 + ((flag b).length+1) ≤ t*w+1+(w+1) by omega)).trans (by omega))
  rw [erase_selected, show Function.update flag b [] = blank from erase_selected ..] at done
  refine ⟨_, ?_, scanrun.followedBy done⟩
  have hlen : (selected b rest b).length = rest.length := by simp [selected]
  dsimp only [postTicks]; omega

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
