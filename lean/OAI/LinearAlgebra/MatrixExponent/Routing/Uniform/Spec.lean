import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Blueprint
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Colours

/-!
# A sorting protocol from one fixed description

The generator returns the instructions, the group assignments and
the construction cost together. The integer d bounds the bit width
of intermediate indices and the work of a single arithmetic query.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Algorithm Coloring Transport
variable {M t p q l n : ℕ}

noncomputable section
open scoped Classical
variable (F : Type) [Field F]

/-- All assertions at one height use the given blueprint and
generator recipes. No program or grouping is chosen at this height. -/
def Blueprint.ProtocolAt (a : Blueprint M t p q l n) (hM : 1 < M)
    (gen : B p → Recipe M) (m b c d D h : ℕ) (hh : Blueprint.limit t p q l ≤ h) : Prop :=
  let made := a.generate hM h (h / m + b) hh
  let code := (a.compile hM h hh).code
  let group := a.partition h (h / m + b)
  let budget := 2 ^ h * (100 + h) ^ c
  let word := (2 * c + 4 * d + 10) * h
  let storage := 2 ^ (h + 1) * (64 + 32 * 2 ^ p)
  h / m + b ≤ h + 2 ∧ made.value = (code, group) ∧
  (∀ i, group i < 2 ^ (h + 2)) ∧
  (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (h / m + b + p)) ∧
  max (d * (h + 3)) (max (3 * (h + 1) + 10) (max l (max q p))) ≤ word ∧
  made.steps + code.time + storage ≤ budget ∧
  code.advice + code.scratch + storage ≤ budget ∧ budget ≤ 2 ^ word ∧
  evaluate code = code.eval ∧
  (∀ (σ : Equiv.Perm (B h)) (j : B p), Function.Bijective ((gen j).eval hM h (inflate h σ))) ∧
  (∀ (σ : Equiv.Perm (B h)) (z : Site h → B q) (i : Port h p),
    let v := commands (evaluate code (σ, z))
    let j := (v i).2.2
    let g := (gen i.2).eval hM h (inflate h σ)
    i ∈ Enabled v → gen i.2 = gen j.2 ∧ (g i.1 = j.1 ∨ g j.1 = i.1)) ∧
  ∀ w ≥ h, ∃ (u : ℕ) (f : Kernel F p l w u), 0 < u ∧ u ≤ 2 * w ∧
    let S := network code group f
    S.selector.width = 2 ^ (h + 1) * q ∧ S.Correct 9624 ∧
      Install.Weight F S.localWeight (w * (100 + Nat.clog 2 w) ^ D)

/-- Only the finite recipe and menu data precede the height quantifier. -/
def Protocol (τ : ℝ) : Prop :=
  ∃ (m M t p q l n b c d D : ℕ) (hM : 1 < M)
    (a : Blueprint M t p q l n) (gen : B p → Recipe M),
    2 ≤ m ∧ (∀ h : ℕ, (↑(h / m) : ℝ) ≤ τ * h) ∧ Countable (Recipe M) ∧
    (∀ u : Index.Query M, u.code.width ≤ d ∧ ∀ h, u.code.cost h ≤ (100 + h) ^ d) ∧
    ∀ᶠ h in Filter.atTop, ∃ hh, a.ProtocolAt F hM gen m b c d D h hh

end
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
