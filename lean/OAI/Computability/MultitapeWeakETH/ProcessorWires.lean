import OAI.Computability.MultitapeWeakETH.FoldedNetwork
import OAI.Computability.MultitapeWeakETH.TablePipeline

/-! # Determinism of the folded network's auxiliary processor wires -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open VPVNP.WireTensor
open scoped Classical
noncomputable section

variable {n b N : ℕ} [NeZero N] (G : Network n b)
abbrev Block (n b : ℕ) := Fin (n ⌈/⌉ b)
abbrev Aux (n b : ℕ) := (Fin 4 × Block n b) ⊕ Block n b ⊕ Block n b

def auxSrc (e : Aux n b) : Site G N := src G (.inr e)
def auxDst (e : Aux n b) : Site G N := dst G (.inr e)
def Message : Aux n b → Type
  | .inl _ => Word b
  | .inr (.inl _) => Bool → Bool
  | .inr (.inr _) => Bool → Word b

instance (e : Aux n b) : Fintype (Message e) := by
  rcases e with _ | _ | _ <;> unfold Message <;> infer_instance

abbrev auxSupply (K : Type) [Field K] := wireNetwork (k:=K) (auxSrc G (N:=N)) (auxDst G) Message

/-- The original site encodes its four raw output blocks. Each processor
receives the four blocks and one borrow per subtraction. -/
def ProcessorRule := Block n b → (Fin 4 → Word b) → (Bool → Bool) → (Bool → Word b) × (Bool → Bool)

variable {K : Type} [Field K]
def checks (emit : Fin 4 → Block n b → Word b) (step : ProcessorRule (n:=n) (b:=b))
    (v : Site G N) (wire : (auxSupply G K (N:=N)).Basis v) : Prop :=
  match v with
  | .inl v => ∀ r j (h : v = G.output j), wire.1 (.inl (r,j)) (congrArg Sum.inl h) = emit r j
  | .inr (.inl j) =>
    let raw := fun r => wire.2 (.inl (r,j)) rfl
    let old := if j.val = 0 then fun _ => false else
      wire.2 (.inr (.inl ((finRotate _).symm j))) (congrArg (processor G) ((finRotate _).apply_symm_apply j).symm)
    let result := step j raw old
    wire.1 (.inr (.inr j)) rfl = result.1 ∧ wire.1 (.inr (.inl j)) rfl = result.2
  | .inr (.inr _) => True

/-- Place the explicit raw, borrow and difference values on the auxiliary wires. -/
def assignment (emit : Fin 4 → Block n b → Word b) (carry : Block n b → Bool → Bool)
    (diff : Block n b → Bool → Word b) : (e : Aux n b) → Message e
  | .inl (r,j) => emit r j
  | .inr (.inl j) => carry j
  | .inr (.inr j) => diff j

theorem unique_assignment (emit : Fin 4 → Block n b → Word b) (step : ProcessorRule (n:=n) (b:=b))
    (carry : Block n b → Bool → Bool) (diff : Block n b → Bool → Word b)
    (spec : ∀ j, step j (fun r => emit r j)
        (if j.val = 0 then fun _ => false else carry ((finRotate _).symm j)) = (diff j,carry j))
    (labels : (e : Aux n b) → Message e) :
    (∀ v : Site G N, checks (K:=K) G emit step v (edgeAssignment (auxSrc G) (auxDst G) labels v)) ↔
      labels = assignment emit carry diff := by
  constructor
  · intro legal
    have raw (r j) : labels (.inl (r,j)) = emit r j := legal (original G (G.output j)) r j rfl
    have actual (j : Block n b) := legal (processor G j)
    change ∀ j : Block n b,
      let expected := step j (fun r => labels (.inl (r,j)))
        (if j.val = 0 then fun _ => false else labels (.inr (.inl ((finRotate _).symm j))))
      labels (.inr (.inr j)) = expected.1 ∧ labels (.inr (.inl j)) = expected.2 at actual
    have blockValues (j : Block n b) :
        labels (.inr (.inr j)) = diff j ∧ labels (.inr (.inl j)) = carry j := by
      induction j using (wellFounded_lt (α:=Block n b)).induction with
      | h j ih =>
        have h := actual j
        simp only [raw] at h
        have prev : (if j.val=0 then (fun _ : Bool => false) else labels (.inr (.inl ((finRotate _).symm j)))) =
            (if j.val=0 then (fun _ : Bool => false) else carry ((finRotate _).symm j)) := by
          by_cases nz : j.val = 0
          · simp [nz]
          · simp only [nz,ite_false]
            let _ : NeZero (n ⌈/⌉ b) := ⟨by have := j.isLt; omega⟩
            exact (ih _ ((finRotate_symm_lt_iff_ne_zero j).mpr (fun eq => nz (congrArg Fin.val eq)))).2
        simpa only [prev,spec] using h
    funext e
    rcases e with ⟨r,j⟩ | j | j
    · exact raw r j
    · exact (blockValues j).2
    · exact (blockValues j).1
  · rintro rfl v
    rcases v with v | j | t
    · exact fun _ _ _ => rfl
    · change diff j = _ ∧ carry j = _
      simpa only [edgeAssignment,assignment,spec] using (show diff j = diff j ∧ carry j = carry j from ⟨rfl,rfl⟩)
    · trivial

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
