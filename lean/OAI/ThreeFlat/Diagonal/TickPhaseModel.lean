import OAI.ThreeFlat.Diagonal.TickGroupStates
import OAI.ThreeFlat.Diagonal.PackedChunkTransfer

namespace OAI
/-! # One chronological physical row after multiplying the processor team -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer RotatedChunkGuards
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock}
abbrev Aux (a : ℕ) := Fin a → Bool
abbrev Ext (c : Clock) (a : ℕ) := Fin c.chunks → Aux a

/-- These are the packed S6 count, S5-derived codes and the local forest
value. They all depend on the history selected by the uniform decoder. -/
structure Data (R : GroupRegister P E bits a) (c : Clock) where
  length : Plan.Terminal P bits → ℕ → ℕ
  fit : ∀ v g, 1+R.capacity+2*length v g ≤ a
  code : Plan.Terminal P bits → ℕ → Fin c.chunks → Fin a → ℕ
  weight : ∀ v g, (Fin (length v g) → Bool) → (Fin (length v g) → Bool) → ℕ → F

variable {R : GroupRegister P E bits a} (B : Data R c)

abbrev layout (v : Plan.Terminal P bits) (g : ℕ) := R.layout (B.length v g) (B.fit v g)

def before (v : Plan.Terminal P bits) (g : ℕ) (old : Aux a) (i : Fin (B.length v g)) : Bool :=
  old ⟨1+R.capacity+i.val,by have := i.isLt; have := B.fit v g; omega⟩

def after (v : Plan.Terminal P bits) (g : ℕ) (old : Aux a) (i : Fin (B.length v g)) : Bool :=
  old ⟨1+R.capacity+(B.length v g+i.val),by have := i.isLt; have := B.fit v g; omega⟩

theorem before_work (v : Plan.Terminal P bits) (g : ℕ) (p r : Fin (B.length v g) → Bool) :
    before B v g (R.work (B.fit v g) v p r) = p := funext (R.work_before _ v p r)

theorem after_work (v : Plan.Terminal P bits) (g : ℕ) (p r : Fin (B.length v g) → Bool) :
    after B v g (R.work (B.fit v g) v p r) = r := funext (R.work_after _ v p r)

theorem ready_dec (v : Plan.Terminal P bits) : decode P E bits R.base (R.ready v) = some v := by
  have h := R.decode_ready (n:=0) (by simpa using R.fits) v
  exact h

def chunk (c : Clock) (t : ℕ) : Fin c.chunks := ⟨t%c.chunks,Nat.mod_lt _ c.chunks_pos⟩

theorem chunk_scan (g : ℕ) (j : Fin c.chunks) : chunk c (c.base g+(1+j.val)) = c.scanOrder g j :=
  Fin.ext (c.scanOrder_val g j).symm

def scanKernel (v : Plan.Terminal P bits) (g : ℕ) (p r : Fin (B.length v g) → Bool) (i : Fin c.chunks) :
    Matrix (Ext c a) (Ext c a) F :=
  chunkKernel (fun j => entry (B.code v g j) (atIndex p) (atIndex r)) {i}

/-- The input memory chooses a history using the opening's new word or any
later phase's old word. The disjoint identity branch contributes its own entry. -/
def step (t : ℕ) : Matrix (Ext c a × Aux a) (Ext c a × Aux a) F := fun s d =>
  let ph := c.phase t
  let v := decode P E bits R.base (if ph=.opening then d.2 else s.2)
  let g := c.group t
  (if s.2=(fun _ => false) ∧ d.2=(fun _ => false) ∧ s.1=d.1 then 1 else 0) +
    v.elim 0 (fun h => if (layout B h g).accepts ph true s.2 d.2 then
      if ph=.scan then scanKernel B h g (before B h g s.2) (after B h g s.2) (chunk c t) s.1 d.1
      else if s.1=d.1 then
        if ph=.evaluate then B.weight h g (before B h g s.2) (after B h g s.2) t else 1
      else 0
    else 0)

def readyAux : Option (Plan.Terminal P bits) ↪ Aux a :=
  ⟨fun o => o.elim (fun _ => false) R.ready,by
    rintro (_|v) (_|w) h
    · rfl
    · exact (R.ready_no_false w h.symm).elim
    · exact (R.ready_no_false v h).elim
    · exact congrArg some (R.ready_injective h)⟩

def workAux (v : Plan.Terminal P bits) (g : ℕ) :
    (Aux (B.length v g) × Aux (B.length v g)) ↪ Aux a :=
  ⟨fun h => R.work (B.fit v g) v h.1 h.2,fun _ _ eq =>
    Prod.ext (R.work_injective _ eq).2.1 (R.work_injective _ eq).2.2⟩

theorem work_ne (v : Plan.Terminal P bits) (g : ℕ) (h : Aux (B.length v g) × Aux (B.length v g)) :
    workAux B v g h ≠ fun _ => false := by
  intro e
  have z := congrArg (fun word => (TickAuxiliary.project (R.layout (B.length v g) (B.fit v g)) word).marker) e
  change (TickAuxiliary.project (R.layout (B.length v g) (B.fit v g))
    (R.work (B.fit v g) v h.1 h.2)).marker = false at z
  rw [R.work_fields] at z
  cases z

private theorem zero_not_accepted (L : Layout a) {ph : Phase} (h : ph≠.opening) (d : Aux a) :
    ¬L.accepts ph true (fun _ => false) d := by
  intro ok
  have b := branch_eq_of_accepts _ _ _ _ _ ok
  simp [branch,h] at b

theorem identity (t : ℕ) (hp : c.phase t ≠ .opening) (x y : Ext c a) (d : Aux a) :
    step B t (x,fun _ => false) (y,d) = if d=(fun _ => false) then (1 : Matrix (Ext c a) (Ext c a) F) x y else 0 := by
  simp only [step,ite_eq_right hp]
  cases dec : decode P E bits R.base (fun _ => false) <;>
    by_cases aux : d=(fun _ => false) <;> simp [aux,zero_not_accepted _ hp,Matrix.one_apply]

theorem opening (x y : Ext c a) (d : Aux a) :
    step B 0 (x,fun _ => false) (y,d) =
      if (∃ h, readyAux (R:=R) h=d) ∧ x=y then 1 else 0 := by
  let g := c.group 0
  have exists_ready : (∃ h, readyAux (R:=R) h = d) ↔ d=(fun _ => false) ∨
      ∃ v, d=R.ready v := by
    constructor
    · rintro ⟨(_|v),rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨v,rfl⟩
    · rintro (rfl|⟨v,rfl⟩)
      · exact ⟨none,rfl⟩
      · exact ⟨some v,rfl⟩
  simp only [step,c.opening,ite_true,exists_ready]
  by_cases xy : x=y
  · cases dec : decode P E bits R.base d with
    | none =>
      have no : ¬∃ v, d=R.ready v := by rintro ⟨v,rfl⟩; rw [ready_dec] at dec; contradiction
      simp [xy,no]
    | some v =>
      have ok : (layout B v g).accepts .opening true (fun _ => false) d ↔ d=R.ready v := by
        simpa [dec] using R.opening_iff (B.fit v g) v d
      have only : (∃ w, d=R.ready w) ↔ d=R.ready v := by
        constructor
        · rintro ⟨u,rfl⟩
          have eq : u=v := by simpa only [ready_dec,Option.some.injEq] using dec
          rw [eq]
        · exact fun hv => ⟨v,hv⟩
      by_cases ev : d=R.ready v
      · have accepted : (layout B v (c.group 0)).accepts .opening true
            (fun _ => false) (R.ready v) := ev ▸ ok.mpr ev
        have image : ∃u, R.ready v=R.ready u := ⟨v,rfl⟩
        rw [ev]
        simp [xy,R.ready_no_false v,accepted,image]
      · have rej := mt ok.mp ev
        simp [xy,g,only,ev,rej]
  · cases decode P E bits R.base d <;> simp [xy]

end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
