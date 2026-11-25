import OAI.ThreeFlat.Routing.SpillBankBoard
import OAI.ThreeFlat.Routing.SpillControl

namespace OAI
/-! # Verifying reports on the public board of a two-pass bank -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {C q D R : ℕ} (B : TwoPassBank C q D R) {F : Type*}

abbrev BoardPin := Fin (C*R) ⊕ Candidate (fullBoard B)
private abbrev Gate := Option (Candidate (fullBoard B))
private def port : Gate B → Type
  | none => ControlPin (primaryBoard B) B.slots
  | some _ => Bool
private instance (g : Gate B) : Fintype (port B g) := by
  cases g <;> dsimp [port] <;> infer_instance

private def modules [Zero F] [One F] (cap : ℕ) :
    ∀ g : Gate B, BitNetwork F (Fintype.card (port B g))
  | none => controlNetwork (primaryBoard B) B.G B.slots cap
  | some _ => TypedWiring.localTable fun x => if x false = x true then 1 else 0

private def wire : ∀ g : Gate B, port B g → BoardPin B ⊕ BankSignal B
  | none, .inl (.inl i) => .inl (.inl i)
  | none, .inl (.inr p) => .inr (.inl p)
  | none, .inr r => .inr (.inr r)
  | some c, false => .inl (.inr c)
  | some c, true => .inr (boardSignal B c)

def boardCheck [Zero F] [One F] (cap : ℕ) : BitNetwork F (Fintype.card (BoardPin B)) :=
  TypedWiring.glue (modules B cap) (wire B)

def primaryPlan (A : Finset (Fin (C*R))) : Candidate (primaryBoard B) → Bool :=
  (existsUnique_primaryValid (primaryBoard B) (fun e => decide (e ∈ A))).choose

theorem primaryPlan_valid (A : Finset (Fin (C*R))) :
    PrimaryValid (primaryBoard B) (fun e => decide (e ∈ A)) (primaryPlan B A) :=
  (existsUnique_primaryValid (primaryBoard B) (fun e => decide (e ∈ A))).choose_spec.1

def remainderMask (A : Finset (Fin (C*R))) :=
  missedPrimary A (primaryBoard B) (primaryPlan B A)

def reservePlan (A : Finset (Fin (C*R))) (cap : ℕ) : ReserveChoice (Fin (C*R)) B.slots → Bool :=
  reservePick B.G (reserveReports B.G B.slots cap (remainderMask B A))

def fullPlan (A : Finset (Fin (C*R))) (cap : ℕ) :=
  boardPick B (primaryPlan B A) (reservePlan B A cap)

def Fits (A : Finset (Fin (C*R))) (cap : ℕ) : Prop := B.G.live B.slots (remainderMask B A) cap = ∅

private theorem checkProduct [CommSemiring F] (cap : ℕ) (A : Finset (Fin (C*R)))
    (c : Candidate (fullBoard B) → Bool) (h : BankSignal B → Bool) :
    let x := Sum.elim (fun e => decide (e ∈ A)) c
    let P := fun p => h (.inl p)
    let s := fun r => h (.inr r)
    let M := missedPrimary A (primaryBoard B) P
    (∏ g : Gate B, TypedWiring.value (modules (F := F) B cap g) (fun k => Sum.elim x h (wire B g k))) =
      if PrimaryValid (primaryBoard B) (fun e => decide (e ∈ A)) P ∧
        s = reservePick B.G (reserveReports B.G B.slots cap M) ∧ B.G.live B.slots M cap = ∅ ∧
        c = boardPick B P s then 1 else 0 := by
  dsimp only
  let x := Sum.elim (fun e => decide (e ∈ A)) c
  let P : Candidate (primaryBoard B) → Bool := fun p => h (.inl p)
  let s : ReserveChoice (Fin (C*R)) B.slots → Bool := fun r => h (.inr r)
  have ctrl : (fun k => Sum.elim x h (wire B none k)) = controlPins (primaryBoard B) A P s := by
    funext k
    rcases k with (i | b) | j <;> rfl
  have check (e : Candidate (fullBoard B)) : TypedWiring.value (modules (F := F) B cap (some e))
      (fun k => Sum.elim x h (wire B (some e) k)) = if c e = h (boardSignal B e) then 1 else 0 := by
    rw [modules,TypedWiring.localTable_value]
    rfl
  have matchAll : (∀ e, c e = h (boardSignal B e)) ↔ c = boardPick B P s := by
    have eqn : h ∘ boardSignal B = boardPick B P s := by
      funext e
      change h _ = Sum.elim P s _
      cases boardSignal B e <;> rfl
    rw [← eqn]
    exact funext_iff.symm
  have root : TypedWiring.value (modules (F := F) B cap none)
      (fun k => Sum.elim x h (wire B none k)) =
      if PrimaryValid (primaryBoard B) (fun e => decide (e ∈ A)) P ∧
        s = reservePick B.G (reserveReports B.G B.slots cap (missedPrimary A (primaryBoard B) P)) ∧
        B.G.live B.slots (missedPrimary A (primaryBoard B) P) cap = ∅ then 1 else 0 :=
    (congrArg (TypedWiring.value (controlNetwork (F := F) (primaryBoard B) B.G B.slots cap)) ctrl).trans
      (controlNetwork_eval (F := F) (primaryBoard B) B.G B.slots cap A P s)
  change (∏ g : Gate B, TypedWiring.value (modules (F := F) B cap g)
    (fun k => Sum.elim x h (wire B g k))) = _
  rw [Fintype.prod_option,root]
  simp_rw [check]
  simp only [Fintype.prod_ite_zero,Finset.prod_const_one,matchAll]
  have combine (a b : Prop) [Decidable a] [Decidable b] :
      (if a then (1:F) else 0) * (if b then 1 else 0) = if a ∧ b then 1 else 0 := by
    by_cases ha : a <;> by_cases hb : b <;> simp [ha,hb]
  rw [combine]
  exact if_congr (by simp only [and_assoc,P,s]) rfl rfl

private theorem sameDecision {K : Type*} (p : Prop) (d₁ d₂ : Decidable p) (a b : K) :
    @ite K p d₁ a b = @ite K p d₂ a b := by rw [Subsingleton.elim d₁ d₂]

/-- The public selectors have exactly one possible value on a completed input.
The unresolved-mask test kills every report when the reserve runs out of rounds. -/
theorem boardCheck_eval [CommSemiring F] (cap : ℕ) (A : Finset (Fin (C*R)))
    (c : Candidate (fullBoard B) → Bool) :
    TypedWiring.value (boardCheck (F := F) B cap) (Sum.elim (fun e => decide (e ∈ A)) c) =
      if Fits B A cap ∧ c = fullPlan B A cap then 1 else 0 := by
  let P := primaryPlan B A
  let s := reservePlan B A cap
  let h0 := Sum.elim P s
  rw [boardCheck,TypedWiring.glue_value]
  simp_rw [checkProduct]
  rw [Finset.sum_eq_single h0]
  · simp [h0,P,s,primaryPlan_valid,fullPlan,Fits,reservePlan,remainderMask]
    exact sameDecision _ _ _ _ _
  · intro h _ ne
    apply ite_eq_right
    rintro ⟨hv,hs,_,_⟩
    have hP : (fun p => h (.inl p)) = P :=
      (existsUnique_primaryValid (primaryBoard B) (fun e => decide (e ∈ A))).choose_spec.2 _ hv
    have hS : (fun r => h (.inr r)) = s := by simpa [s,reservePlan,remainderMask,← hP,P] using hs
    apply ne
    funext z
    cases z with
    | inl p => exact congrFun hP p
    | inr r => exact congrFun hS r
  · simp

theorem boardCheck_cells [Zero F] [One F] (cap : ℕ) :
    (boardCheck (F := F) B cap).cells = (controlNetwork (F := F) (primaryBoard B) B.G B.slots cap).cells +
      Fintype.card (Candidate (fullBoard B)) * 16 := by
  simp [boardCheck,modules,port,Fintype.sum_option,TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells,Finset.sum_mul]

end ThreeFlat.Routing.Spill

end
end OAI
