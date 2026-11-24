import OAI.Computability.VPVNP.PairSimulationTerminalFive

/-!
# Uniqueness of the five terminal phases

The accepting exit of each worker uniquely determines its block of physical
calls. Concatenating the five blocks therefore gives a bijection with the
native accepted paths, for any predicate on the full sequence of reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}

/-- Two complete runs of the same worker on prefixes of a common call stream
consume the same prefix and leave the same reports, memory and suffix. -/
theorem Phase.unique_prefix {e m xs ls final}
    (left : Phase workers pub cap e m xs ls final)
    {ys rs nextMemory} (right : Phase workers pub cap e m ys rs nextMemory)
    {a b : List (List Bool)} (same : xs ++ a = ys ++ b) :
    xs = ys ∧ ls = rs ∧ final = nextMemory ∧ a = b := by
  induction left generalizing ys rs nextMemory with
  | @last e m x raw called room accepted =>
    cases right with
    | @last _ _ y out called' room' accepted' =>
      obtain ⟨rfl, hab⟩ := List.cons.inj same
      obtain rfl := Option.some.inj (called.symm.trans called')
      exact ⟨rfl, rfl, rfl, hab⟩
    | @more _ _ y ys out j rs nextMemory called' room' returned' later =>
      obtain ⟨rfl, _⟩ := List.cons.inj same
      obtain rfl := Option.some.inj (called.symm.trans called')
      rw [accepted] at returned'
      contradiction
  | @more e m x xs raw i ls final called room returned tail ih =>
    cases right with
    | @last _ _ y out called' room' accepted' =>
      obtain ⟨rfl, _⟩ := List.cons.inj same
      obtain rfl := Option.some.inj (called.symm.trans called')
      rw [accepted'] at returned
      contradiction
    | @more _ _ y ys out j rs nextMemory called' room' returned' later =>
      obtain ⟨rfl, rest⟩ := List.cons.inj same
      obtain rfl := Option.some.inj (called.symm.trans called')
      obtain rfl := Option.some.inj (returned.symm.trans returned')
      obtain ⟨rfl, rfl, rfl, hab⟩ := ih later rest
      exact ⟨rfl, rfl, rfl, hab⟩

/-- The terminal cut determines the full block and its remaining choice stream. -/
theorem Phase.block_eq_suffix {e m} {x y : Block w}
    (hx : Phase workers pub cap e m x.choices x.logs x.memory)
    (hy : Phase workers pub cap e m y.choices y.logs y.memory)
    {a b : List (List Bool)} (same : x.choices ++ a = y.choices ++ b) :
    x = y ∧ a = b := by
  obtain ⟨choices, logs, mem, suffix⟩ := hx.unique_prefix hy same
  cases x
  cases y
  exact ⟨by congr, suffix⟩

/-- The entire five-phase trace, including the reports and each intermediate
memory, is uniquely determined by the sequence of native branch strings. -/
theorem FiveTrace.choices_injective {m : Memory w} :
    Function.Injective (FiveTrace.choices (workers := workers) (pub := pub) (cap := cap) (m := m)) := by
  rintro ⟨x₀, x₁, x₂, x₃, x₄, p₀, p₁, p₂, p₃, p₄⟩ ⟨y₀, y₁, y₂, y₃, y₄, q₀, q₁, q₂, q₃, q₄⟩ h
  change x₀.choices ++ (x₁.choices ++ (x₂.choices ++ (x₃.choices ++ x₄.choices))) =
    y₀.choices ++ (y₁.choices ++ (y₂.choices ++ (y₃.choices ++ y₄.choices))) at h
  obtain ⟨rfl, h₁⟩ := Phase.block_eq_suffix p₀ q₀ h
  obtain ⟨rfl, h₂⟩ := Phase.block_eq_suffix p₁ q₁ h₁
  obtain ⟨rfl, h₃⟩ := Phase.block_eq_suffix p₂ q₂ h₂
  obtain ⟨rfl, h₄⟩ := Phase.block_eq_suffix p₃ q₃ h₃
  obtain ⟨rfl, _⟩ := Phase.block_eq_suffix p₄ q₄ (a := []) (b := []) (by simpa using h₄)
  rfl

/-- Concatenate the choices of the five admissible phases to obtain the
corresponding accepting path of the linked native program. -/
noncomputable def fiveTraceEquiv (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)
    (m : Memory w) (ok : List (Report w) → Prop) (fit : 32 ≤ 2 ^ w) (hcap : 26 ≤ cap) :
    {t : FiveTrace workers pub cap m // ok (reports (header pub) t.logs)} ≃
      ActualPaths (program workers pub) cap 0 m ok := by
  let join : {t : FiveTrace workers pub cap m // ok (reports (header pub) t.logs)} →
      ActualPaths (program workers pub) cap 0 m ok := fun t =>
    ⟨t.val.choices, (accepts_five workers pub cap m _ ok fit hcap).mpr ⟨t.val, rfl, t.property⟩⟩
  refine Equiv.ofBijective join ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (FiveTrace.choices_injective (congrArg Subtype.val h))
  · intro b
    obtain ⟨t, ht, accepted⟩ := (accepts_five workers pub cap m b.val ok fit hcap).mp b.property
    exact ⟨⟨t, accepted⟩, Subtype.ext ht.symm⟩

@[simp] theorem fiveTraceEquiv_apply_val {m : Memory w} {ok : List (Report w) → Prop}
    (fit : 32 ≤ 2 ^ w) (hcap : 26 ≤ cap)
    (t : {t : FiveTrace workers pub cap m // ok (reports (header pub) t.logs)}) :
    (fiveTraceEquiv workers pub cap m ok fit hcap t).val = t.val.choices := rfl

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
