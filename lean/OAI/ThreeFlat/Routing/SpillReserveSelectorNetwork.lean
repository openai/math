import OAI.ThreeFlat.Routing.SpillReserve

namespace OAI
/-! # Output selectors for the peeled reserve graph

For each edge, endpoint, and slot, a chain accumulates proposals from all rounds.
The last state of each chain is its exposed selector bit.
-/

noncomputable section
open scoped BigOperators Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {E V F : Type*} [Fintype E] [Fintype V] [LinearOrder E] [DecidableEq V]
variable (G : ReserveGraph E V)

abbrev ReserveChoice (E : Type*) (slots : ℕ) := E × Bool × Fin slots
abbrev ReserveSelectPin (E V : Type*) (slots cap : ℕ) :=
  (E ⊕ Round E V cap) ⊕ ReserveChoice E slots

def reserveEnd {slots : ℕ} (c : ReserveChoice E slots) : V :=
  if c.2.1 then G.dst c.1 else G.src c.1

def reserveBefore {cap : ℕ} (e : E) (t : Fin cap) : E ⊕ Round E V cap :=
  if h : t.val = 0 then .inl e else .inr (.inr (e,⟨t.val-1,by omega⟩))

private def proposalRule {slots : ℕ} (c : ReserveChoice E slots)
    (live src dst : Bool) (adj : Adjacent G (reserveEnd G c) → Bool) : Bool :=
  live && (if c.2.1 then !src && dst else src) &&
    decide ((Finset.univ.filter (fun i : Adjacent G (reserveEnd G c) =>
      i.val < c.1 ∧ adj i = true)).card = c.2.2.val)

/-- A live request selects its source if eligible, otherwise its eligible destination.
Its slot counts the smaller live edges incident to the selected endpoint. -/
def reserveProposal {slots cap : ℕ} (a : E ⊕ Round E V cap → Bool)
    (c : ReserveChoice E slots) (t : Fin cap) : Bool :=
  proposalRule G c (a (reserveBefore c.1 t))
    (a (.inr (.inl (G.src c.1,t)))) (a (.inr (.inl (G.dst c.1,t))))
    (fun i => a (reserveBefore i.val t))

omit [Fintype V] in
theorem reserveProposal_eq {slots cap : ℕ} (a : E ⊕ Round E V cap → Bool)
    (c : ReserveChoice E slots) (t : Fin cap) :
    reserveProposal G a c t =
      (a (reserveBefore c.1 t) &&
        (if c.2.1 then !a (.inr (.inl (G.src c.1,t))) && a (.inr (.inl (G.dst c.1,t)))
         else a (.inr (.inl (G.src c.1,t)))) &&
        decide ((Finset.univ.filter (fun i : Adjacent G (reserveEnd G c) =>
          i.val < c.1 ∧ a (reserveBefore i.val t) = true)).card = c.2.2.val)) := rfl

def reservePick {slots cap : ℕ} (a : E ⊕ Round E V cap → Bool) (c : ReserveChoice E slots) :
    Bool := decide (∃ t : Fin cap, reserveProposal G a c t = true)

private abbrev Run (E : Type*) (slots cap : ℕ) := ReserveChoice E slots × Fin cap
private abbrev SelectGate (E : Type*) (slots cap : ℕ) := ReserveChoice E slots ⊕ Run E slots cap

private def selectPort {slots cap : ℕ} : SelectGate E slots cap → Type _
  | .inl _ => PUnit
  | .inr (c,_) => Fin 5 ⊕ Adjacent G (reserveEnd G c)

private def stateWire {slots cap : ℕ} (c : ReserveChoice E slots) (n : ℕ) :
    ReserveSelectPin E V slots cap ⊕ Run E slots cap :=
  if h : n < cap then .inr (c,⟨n,h⟩) else .inl (.inr c)

private def selectWire {slots cap : ℕ} : ∀ g : SelectGate E slots cap,
    selectPort G g → ReserveSelectPin E V slots cap ⊕ Run E slots cap
  | .inl c, _ => stateWire c 0
  | .inr (c,t), .inl i => ![stateWire c (t.val+1), stateWire c t.val,
      .inl (.inl (reserveBefore c.1 t)),
      .inl (.inl (.inr (.inl (G.src c.1,t)))),
      .inl (.inl (.inr (.inl (G.dst c.1,t))))] i
  | .inr (_,t), .inr i => .inl (.inl (reserveBefore i.val t))

private def selectTest {slots cap : ℕ} : ∀ g : SelectGate E slots cap,
    (selectPort G g → Bool) → Prop
  | .inl _, w => w PUnit.unit = false
  | .inr (c,_), w =>
    w (.inl 0) = (w (.inl 1) ||
      proposalRule G c (w (.inl 2)) (w (.inl 3)) (w (.inl 4)) (fun i => w (.inr i)))

private instance selectPortFintype {slots cap : ℕ} (g : SelectGate E slots cap) :
    Fintype (selectPort G g) := by
  rcases g with c | ⟨c,t⟩ <;> dsimp [selectPort] <;> infer_instance

def reserveSelectNetwork [Zero F] [One F] (slots cap : ℕ) :
    BitNetwork F (Fintype.card (ReserveSelectPin E V slots cap)) :=
  LocalChecks.network (selectPort G (slots := slots) (cap := cap)) (selectWire G) (selectTest G)

private def stateBit {slots cap : ℕ} (out : ReserveChoice E slots → Bool)
    (h : Run E slots cap → Bool) (c : ReserveChoice E slots) (n : ℕ) : Bool :=
  if hn : n < cap then h (c,⟨n,hn⟩) else out c

omit [Fintype E] [Fintype V] [LinearOrder E] [DecidableEq V] in
private theorem readState {slots cap : ℕ} (a : E ⊕ Round E V cap → Bool)
    (out : ReserveChoice E slots → Bool) (h : Run E slots cap → Bool)
    (c : ReserveChoice E slots) (n : ℕ) :
    Sum.elim (Sum.elim a out) h (stateWire c n) = stateBit out h c n := by
  by_cases hn : n < cap <;> simp [stateWire,stateBit,hn]

omit [Fintype V] in
private theorem accepts_iff {slots cap : ℕ} (a : E ⊕ Round E V cap → Bool)
    (out : ReserveChoice E slots → Bool) (h : Run E slots cap → Bool) :
    LocalChecks.Accepts (selectPort G) (selectWire G) (selectTest G) (Sum.elim a out) h ↔
    (∀ c, stateBit out h c 0 = false) ∧ (∀ c (t : Fin cap), stateBit out h c (t.val+1) =
      (stateBit out h c t.val || reserveProposal G a c t)) := by
  constructor
  · intro ok
    refine ⟨fun c => ?_,fun c t => ?_⟩
    · exact (readState a out h c 0).symm.trans (ok (.inl c))
    · simpa [selectTest,Function.comp_def,selectWire,readState,reserveProposal] using ok (.inr (c,t))
  · rintro ⟨start,step⟩ (c | ⟨c,t⟩)
    · exact (readState a out h c 0).trans (start c)
    · simpa [selectTest,Function.comp_def,selectWire,readState,reserveProposal] using step c t

private def seen {cap : ℕ} (b : Fin cap → Bool) (n : ℕ) : Bool :=
  decide (∃ t : Fin cap, t.val < n ∧ b t = true)

private theorem seen_zero {cap : ℕ} (b : Fin cap → Bool) : seen b 0 = false := by simp [seen]

private theorem seen_succ {cap : ℕ} (b : Fin cap → Bool) (t : Fin cap) :
    seen b (t.val+1) = (seen b t.val || b t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [seen,decide_eq_true_eq,Bool.or_eq_true]
  constructor
  · rintro ⟨s,hs,hb⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
    · exact Or.inl ⟨s,hlt,hb⟩
    · exact Or.inr (Fin.ext heq ▸ hb)
  · rintro (⟨s,hs,hb⟩ | hb)
    · exact ⟨s,by omega,hb⟩
    · exact ⟨t,by omega,hb⟩

private theorem seen_cap {cap : ℕ} (b : Fin cap → Bool) :
    seen b cap = decide (∃ t : Fin cap, b t = true) := by simp [seen]

/-- For any proposed report, the selector chain has exactly one extension if the
exposed bits agree with the union of its round proposals. This includes zero rounds. -/
theorem reserveSelectNetwork_eval [CommSemiring F] (slots cap : ℕ)
    (a : E ⊕ Round E V cap → Bool) (out : ReserveChoice E slots → Bool) :
    TypedWiring.value (reserveSelectNetwork (F := F) G slots cap) (Sum.elim a out) =
      if out = reservePick G a then 1 else 0 := by
  let hidden (g : Run E slots cap) := seen (reserveProposal G a g.1) g.2.val
  have canonical (c : ReserveChoice E slots) (n : ℕ) (hn : n ≤ cap) :
      stateBit (reservePick G a) hidden c n = seen (reserveProposal G a c) n := by
    by_cases hlt : n < cap
    · simp [stateBit,hlt,hidden]
    · have e : n = cap := by omega
      subst n
      simp [stateBit,seen_cap,reservePick]
  have reconstruct (h : Run E slots cap → Bool)
      (ok : LocalChecks.Accepts (selectPort G) (selectWire G) (selectTest G) (Sum.elim a out) h)
      (c : ReserveChoice E slots) (n : ℕ) (hn : n ≤ cap) :
      stateBit out h c n = seen (reserveProposal G a c) n := by
    obtain ⟨start,step⟩ := (accepts_iff G a out h).mp ok
    induction n with
    | zero => exact (start c).trans (seen_zero _).symm
    | succ n ih =>
      let t : Fin cap := ⟨n,by omega⟩
      exact (step c t).trans ((congrArg (· || reserveProposal G a c t) (ih (by omega))).trans
        (seen_succ _ t).symm)
  refine (LocalChecks.eval_of_unique (F := F) (selectPort G) (selectWire G) (selectTest G)
    (Sum.elim a out) (out = reservePick G a) ?_ ?_).trans ?_
  · rintro rfl
    refine ⟨hidden,(accepts_iff G a _ hidden).mpr ⟨fun c => ?_,fun c t => ?_⟩,?_⟩
    · rw [canonical c 0 (by omega),seen_zero]
    · rw [canonical c _ (by omega),canonical c _ t.isLt.le,seen_succ]
    · intro h ok
      funext g
      simpa [stateBit,g.2.isLt,hidden] using reconstruct h ok g.1 g.2.val g.2.isLt.le
  · intro h ok
    funext c
    simpa [stateBit,seen_cap,reservePick] using reconstruct h ok c cap le_rfl
  · by_cases eqn : out = reservePick G a <;> simp [eqn]

theorem reserveSelectNetwork_cells [Zero F] [One F] (slots cap D : ℕ)
    (bounded : ∀ v, Fintype.card (Adjacent G v) ≤ D) :
    (reserveSelectNetwork (F := F) G slots cap).cells ≤
      Fintype.card (ReserveChoice E slots) * (cap+1) * (2^(5+D)*(5+D+2)) := by
  have arity (g : SelectGate E slots cap) : Fintype.card (selectPort G g) ≤ 5+D := by
    rcases g with c | ⟨c,t⟩
    · simp [selectPort]; omega
    · simpa only [selectPort,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_left (bounded _) 5
  simpa [reserveSelectNetwork,SelectGate,Run,Fintype.card_prod,Nat.mul_add,Nat.add_comm] using
    LocalChecks.cells_le (F := F) (selectPort G (slots := slots) (cap := cap)) (selectWire G) (selectTest G) arity

end ThreeFlat.Routing.Spill

end
end OAI
