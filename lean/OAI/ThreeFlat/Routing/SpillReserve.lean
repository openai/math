import OAI.ThreeFlat.Routing.LocalChecks
import OAI.ThreeFlat.Concentrator.Peeling
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Unrolling the sparse reserve matching in logarithmically many rounds -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill
open Concentrator

universe u
variable {E : Type u} {V F : Type*} [Fintype E] [Fintype V] [DecidableEq V] (G : ReserveGraph E V)

abbrev Adjacent (v : V) := {e : E // G.src e = v ∨ G.dst e = v}
abbrev Round (E V : Type*) (cap : ℕ) := (V × Fin cap) ⊕ (E × Fin cap)

private def reservePort {cap : ℕ} : Round E V cap → Type _
  | .inl (v,_) => Option (Adjacent G v)
  | .inr _ => ULift.{u} (Fin 4)

private instance {cap : ℕ} (g : Round E V cap) : Fintype (reservePort G g) := by
  rcases g with ⟨v,t⟩ | ⟨e,t⟩ <;> dsimp [reservePort] <;> infer_instance

private def before {cap : ℕ} (e : E) (t : Fin cap) : E ⊕ Round E V cap :=
  if h : t.val = 0 then .inl e else .inr (.inr (e,⟨t.val-1,by omega⟩))

private def roundWire {cap : ℕ} : ∀ g : Round E V cap, reservePort G g → E ⊕ Round E V cap
  | .inl (v,t), none => .inr (.inl (v,t))
  | .inl (_,t), some e => before e.val t
  | .inr (e,t), k => ![.inr (.inr (e,t)), before e t,
      .inr (.inl (G.src e,t)), .inr (.inl (G.dst e,t))] k.down

private def roundTest (slots : ℕ) {cap : ℕ} : ∀ g : Round E V cap, (reservePort G g → Bool) → Prop
  | .inl (_,_), w => w none = decide ((Finset.univ.filter (fun e => w (some e) = true)).card ≤ slots)
  | .inr _, w => w ⟨0⟩ = (w ⟨1⟩ && !w ⟨2⟩ && !w ⟨3⟩)

/-- One local counting gate per reserve vertex per round and one continuation
gate per edge per round; each counting gate has bounded arity on the public graph. -/
def reserveNetwork [Zero F] [One F] (slots cap : ℕ) : BitNetwork F (Fintype.card E) :=
  LocalChecks.network (reservePort G) (roundWire G (cap := cap)) (roundTest G slots)

def reserveCheck [Zero F] [One F] (slots cap : ℕ) :
    BitNetwork F (Fintype.card (E ⊕ Round E V cap)) :=
  LocalChecks.exposed (reservePort G) (roundWire G (cap := cap)) (roundTest G slots)

def reserveTrace (slots cap : ℕ) (A : Finset E) : Round E V cap → Bool
  | .inl (v,t) => decide (G.departure slots A cap v ≤ t.val)
  | .inr (e,t) => decide (e ∈ G.live slots A (t.val+1))

omit [Fintype E] [Fintype V] in
private theorem before_trace (slots cap : ℕ) (A : Finset E) (e : E) (t : Fin cap) :
    Sum.elim (fun i => decide (i ∈ A)) (reserveTrace G slots cap A) (before e t) =
      decide (e ∈ G.live slots A t.val) := by
  by_cases ht : t.val = 0
  · simp [before,ht,ReserveGraph.live]
  · simp [before,ht,reserveTrace, Nat.sub_add_cancel (by omega : 1 ≤ t.val)]

omit [Fintype V] in
private theorem count_incident (A : Finset E) (v : V) :
    ((Finset.univ : Finset (Adjacent G v)).filter (fun e => e.val ∈ A)).card =
      (G.incident A v).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).2,e.property⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro e he
    obtain ⟨hin,hadj⟩ := Finset.mem_filter.mp he
    exact ⟨⟨e,hadj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hin⟩,rfl⟩

omit [Fintype V] in
theorem reserveTrace_valid (slots cap : ℕ) (A : Finset E) :
    LocalChecks.Accepts (reservePort G) (roundWire G) (roundTest G slots)
      (fun e => decide (e ∈ A)) (reserveTrace G slots cap A) := by
  rintro (⟨v,t⟩ | ⟨e,t⟩)
  · simp [roundTest,roundWire,Function.comp_def,before_trace,reserveTrace,count_incident,
      G.departure_le_iff slots A cap t.isLt]
  · simp [roundTest,roundWire,Function.comp_def,before_trace,reserveTrace,
      G.departure_le_iff slots A cap t.isLt,ReserveGraph.live,ReserveGraph.step]
    apply Bool.eq_iff_iff.mpr
    simp [and_assoc]

omit [Fintype V] in
theorem reserveTrace_unique (slots cap : ℕ) (A : Finset E) (h : Round E V cap → Bool)
    (ok : LocalChecks.Accepts (reservePort G) (roundWire G) (roundTest G slots)
       (fun e => decide (e ∈ A)) h) : h = reserveTrace G slots cap A := by
  let z := reserveTrace G slots cap A
  let X := fun e => decide (e ∈ A)
  have hz := reserveTrace_valid G slots cap A
  have step (t : Fin cap) :
      (∀ v, h (.inl (v,t)) = z (.inl (v,t))) ∧ (∀ e, h (.inr (e,t)) = z (.inr (e,t))) := by
    induction ht : t.val using Nat.strong_induction_on generalizing t with
    | h n ih =>
      have hp (e : E) : Sum.elim X h (before e t) = Sum.elim X z (before e t) := by
        by_cases ht0 : t.val = 0
        · simp [before,ht0]
        · let k : Fin cap := ⟨t.val-1,by omega⟩
          simpa [before,ht0,k] using (ih k.val (by dsimp [k]; omega) k rfl).2 e
      have hv (v : V) : h (.inl (v,t)) = z (.inl (v,t)) := by
        have a := ok (.inl (v,t))
        have b := hz (.inl (v,t))
        change h (.inl (v,t)) = decide ((Finset.univ.filter
          (fun e : Adjacent G v => Sum.elim X h (before e.val t) = true)).card ≤ slots) at a
        change z (.inl (v,t)) = decide ((Finset.univ.filter
          (fun e : Adjacent G v => Sum.elim X z (before e.val t) = true)).card ≤ slots) at b
        simpa only [hp] using a.trans (by rw [b]; simp only [hp])
      refine ⟨hv,?_⟩
      intro e
      have a := ok (.inr (e,t))
      have b := hz (.inr (e,t))
      change h (.inr (e,t)) = (Sum.elim X h (before e t) && !h (.inl (G.src e,t)) &&
        !h (.inl (G.dst e,t))) at a
      change z (.inr (e,t)) = (Sum.elim X z (before e t) && !z (.inl (G.src e,t)) &&
        !z (.inl (G.dst e,t))) at b
      rw [a,b,hp,hv,hv]
  funext g
  cases g with
  | inl vt => exact (step vt.2).1 vt.1
  | inr et => exact (step et.2).2 et.1

theorem reserveNetwork_cells [Zero F] [One F] (slots cap D : ℕ)
    (bounded : ∀ v, Fintype.card (Adjacent G v) ≤ D) :
    (reserveNetwork (F := F) G slots cap).cells ≤
      (Fintype.card V*cap + Fintype.card E*cap) *
        (2^(max (D+1) 4) * (max (D+1) 4 + 2)) := by
  have bound (g : Round E V cap) : Fintype.card (reservePort G g) ≤ max (D+1) 4 := by
    obtain ⟨v,t⟩ | ⟨e,t⟩ := g
    · simpa [reservePort] using (Nat.add_le_add_right (bounded v) 1).trans (le_max_left _ 4)
    · simp [reservePort]
  simpa [reserveNetwork,Round,Fintype.card_prod] using
    LocalChecks.cells_le (F := F) (reservePort G) (roundWire G) (roundTest G slots) bound

theorem reserveCheck_eval [CommSemiring F] (slots cap : ℕ) (A : Finset E) (h : Round E V cap → Bool) :
    TypedWiring.value (reserveCheck (F := F) G slots cap) (Sum.elim (fun e => decide (e ∈ A)) h) =
      if h = reserveTrace G slots cap A then 1 else 0 := by
  rw [reserveCheck,LocalChecks.exposed_value]
  congr 1
  exact propext ⟨reserveTrace_unique G slots cap A h,
    fun he => he.symm ▸ reserveTrace_valid G slots cap A⟩

end ThreeFlat.Routing.Spill

end
end OAI
