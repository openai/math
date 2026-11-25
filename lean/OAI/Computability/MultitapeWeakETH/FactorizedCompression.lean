import OAI.Computability.MultitapeWeakETH.PortTemplates

/-! # Factorized evaluation of a branch of the iterated wire compressor

Commit to the motif indices and the final shared bit strings first. At that
point each surviving position evaluates only the factors in its own placement
fiber. This order of summation is used by the characteristic-zero counter.
-/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open VPVNP VPVNP.Compression VPVNP.NetworkKernel Finset
open scoped BigOperators Classical
noncomputable section

variable {R : Type*} [CommSemiring R]

/-- Follow the complete original factors along a selected chain of placements. -/
def destination {N Y : Network} : TermChain R N Y → N.Site → Y.Site
  | .done _ => id
  | .more t _ tail => destination tail ∘ t.place

/-- Perform each local sum before multiplying across surviving positions. -/
def evaluate {N Y : Network} : TermChain R N Y → Factors R N → Factors R Y
  | .done _ => id
  | .more t _ tail => fun F => evaluate tail (t.push F)

/-- An evaluated site depends on its own block of original factors. -/
theorem evaluate_congr {N Y : Network} (chain : TermChain R N Y) (F G : Factors R N)
    (v : Y.Site) (same : ∀ u, destination chain u = v → F u = G u) :
    evaluate chain F v = evaluate chain G v := by
  induction chain with
  | done => exact same v rfl
  | more t rec tail ih =>
    apply ih
    intro u hu
    funext z
    apply sum_congr rfl
    intro a _
    apply congrArg (· * t.kernel u a z)
    apply prod_congr rfl
    intro i _
    by_cases eq : u = t.place i
    · simp only [eq,dite_eq_left, same i (by simpa [destination,← eq] using hu)]
    · simp [eq]

omit [CommSemiring R] in
/-- Bound the total original load in a terminal block by its recursive record
count. Zero-width arcs and changes of placement need no special case. -/
theorem block_load {N Y : Network} (chain : TermChain R N Y) (load : N.Site → ℕ)
    (v : Y.Site) :
    (∑ u, if destination chain u = v then load u else 0) ≤ chain.occurrences load v := by
  induction chain with
  | done =>
    change (∑ u, if u = v then load u else 0) ≤ load v
    rw [sum_eq_single v] <;> simp_all
  | more t rec tail ih =>
    let next := t.pushHistorySize rec load
    apply le_trans _ (ih next v)
    calc
      _ = ∑ w, if destination tail w = v then
          ∑ u, (if w = t.place u then load u else 0) else 0 := by
        simp only [ite_sum_zero]
        rw [sum_comm]
        apply sum_congr rfl
        intro u _
        rw [sum_eq_single (t.place u)]
        · by_cases h : destination tail (t.place u) = v <;> simp [destination,h]
        · intro w _ ne
          simp [ne]
        · simp
      _ ≤ _ := by
        apply sum_le_sum
        intro w _
        split_ifs
        · dsimp [next,Term.pushHistorySize]
          rw [← sum_filter, sum_subtype (p := fun x => w = t.place x) _ (by simp) load]
          exact Nat.le_add_left ..
        · exact le_rfl

omit [CommSemiring R] in
theorem block_card {N Y : Network} (chain : TermChain R N Y) (v : Y.Site) :
    Fintype.card {u // destination chain u = v} ≤ chain.occurrences (fun _ => 1) v := by
  rw [Fintype.card_subtype]
  simpa using block_load chain (fun _ => 1) v

/-- The finite outer sum ranges over the admitted motif choices alone. -/
@[instance_reducible] def choiceFintype {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X) : Fintype E.Choices :=
  match E with
  | .done _ => inferInstanceAs (Fintype Unit)
  | .more p tail =>
    letI (i : p.step.Choice) := choiceFintype (tail i)
    inferInstanceAs (Fintype ((i : p.step.Choice) × (tail i).Choices))

local instance {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X) :
    Fintype E.Choices := choiceFintype E

private theorem cast_evaluate {N N' Y : Network} (h : N = N') (chain : TermChain R N' Y)
    (F : Factors R N) :
    evaluate (h.symm ▸ chain : TermChain R N Y) F =
      evaluate chain (h ▸ F : Factors R N') := by cases h; rfl

/-- The terminal factor evaluations have independent hidden sums after fixing
the outer choices. Only the final edge assignment is shared by all positions. -/
theorem contract_factorized {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (rec : E.Records) (F : Factors R X.network) :
    contract X.network F = ∑ h : E.Choices,
      ∑ z : (e : (E.finalState h).network.Edge) → (E.finalState h).network.Payload e,
        ∏ v, evaluate (E.termChain rec h) F v
          (WireTensor.edgeAssignment (E.finalState h).network.src (E.finalState h).network.dst z v) := by
  induction E with
  | done X =>
    change _ = ∑ _ : Unit, _
    rw [Fintype.sum_unique]
    exact contract_edgeSum X.network F
  | more p tail ih =>
    rw [p.step.contract_eq_sum]
    change _ = ∑ h : (i : p.step.Choice) × (tail i).Choices, _
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    let Fi : Factors R (p.next i).network := p.output_eq i ▸ (p.step.term i).push F
    have transfer {N M : Network} (h : N = M) (A : Factors R N) :
        contract N A = contract M (h ▸ A : Factors R M) := by cases h; rfl
    rw [transfer (p.output_eq i), ih i (rec.2 i) Fi]
    apply sum_congr rfl
    intro h _
    apply sum_congr rfl
    intro z _
    apply prod_congr rfl
    intro v _
    exact congrFun (congrFun (cast_evaluate (p.output_eq i) ((tail i).termChain (rec.2 i) h)
      ((p.step.term i).push F)).symm v) _

/-- There are exactly two to the total width possible final wire assignments. -/
theorem card_assignments {a g : ℕ} (X : State a g) :
    Fintype.card ((e : X.network.Edge) → X.network.Payload e) = 2^X.totalWidth := by
  let Payload (e : (X.Base × BitWord g) × Fin (2^a)) := Fin (X.width ((e.1.1,e.2),e.1.2)) → Bool
  trans Fintype.card ((e : (X.Base × BitWord g) × Fin (2^a)) → Payload e)
  · exact Fintype.card_congr (Equiv.refl _)
  dsimp only [Payload]
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,prod_pow_eq_pow_sum]
  congr 1
  unfold State.totalWidth
  simp only [Fintype.sum_prod_type]
  exact sum_congr rfl fun u _ => sum_comm

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
