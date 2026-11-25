import OAI.Hierarchy.ABPFirstCutStep

namespace OAI
/-! # Multilinear suffix coefficients of an affine branching program

`transfer a g target cut S` sums the contributions of paths from `cut` to
`target` that use exactly the variables selected by `a` in slots `S`. A path
of length zero contributes the coefficient of its constant weight one.
-/

namespace Hierarchy.ABPFirstCut

noncomputable section

variable {F : Type*} {V : Type} {τ : V → Type} [Field F] [DecidableEq V]
variable {n : ℕ}

/-- Coefficient propagation from a chosen cut vertex. -/
def transfer (a : ∀ i, τ i) : {n : ℕ} → Rows F (Σ i, τ i) n →
    Fin n → Fin n → Finset V → F
  | _, .source => fun _ _ S => if S = ∅ then 1 else 0
  | _, .snoc prev edges =>
      Fin.lastCases
        (Fin.lastCases (fun S => if S = ∅ then 1 else 0)
          (fun cut S => step a edges (fun t => transfer a prev t cut) S))
        (fun target => Fin.lastCases (fun _ => 0) (fun cut => transfer a prev target cut))

@[simp] theorem transfer_source (a : ∀ i, τ i) (target cut : Fin 1) (S : Finset V) :
    transfer (F := F) a .source target cut S = if S = ∅ then 1 else 0 := rfl

variable (a : ∀ i, τ i) (g : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i)))

@[simp] theorem transfer_old_old (target cut : Fin n) (S : Finset V) :
    transfer a (.snoc g edges) target.castSucc cut.castSucc S = transfer a g target cut S := by
  simp [transfer]

@[simp] theorem transfer_old_last (target : Fin n) (S : Finset V) :
    transfer a (.snoc g edges) target.castSucc (Fin.last n) S = 0 := by
  simp [transfer]

@[simp] theorem transfer_last_old (cut : Fin n) (S : Finset V) :
    transfer a (.snoc g edges) (Fin.last n) cut.castSucc S =
      step a edges (fun t => transfer a g t cut) S := by
  simp [transfer]

@[simp] theorem transfer_last_last (S : Finset V) :
    transfer a (.snoc g edges) (Fin.last n) (Fin.last n) S = if S = ∅ then 1 else 0 := by
  simp [transfer]

/-- The assignment outside the slot set of the suffix does not affect the coefficient. -/
theorem transfer_congr (g : Rows F (Σ i, τ i) n) (target cut : Fin n) (S : Finset V)
    {a b : ∀ i, τ i} (ha : ∀ i ∈ S, a i = b i) :
    transfer a g target cut S = transfer b g target cut S := by
  induction g generalizing S with
  | source => rfl
  | @snoc n prev edges ih =>
    refine Fin.lastCases ?_ (fun t => ?_) target
    · refine Fin.lastCases ?_ (fun c => ?_) cut
      · simp
      · simp only [transfer_last_old]
        apply step_congr edges S ha
        exact fun t T hT => ih t c T (fun i hi => ha i (hT hi))
    · refine Fin.lastCases ?_ (fun c => ?_) cut
      · simp
      · simpa only [transfer_old_old] using ih t c S ha

end

end Hierarchy.ABPFirstCut

end OAI
