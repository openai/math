import OAI.Hierarchy.DescentTerminalEpochBits

namespace OAI
/-! # Encoding a dependent sequence of reached selector decks without duplicating branches -/

namespace Hierarchy.DescentTerminalEpochChart
open DescentTerminalEpochBits DescentTerminalEpochFlags DescentSixParty
open scoped Classical
noncomputable section

structure Observation where
  C : ℕ
  count : ℕ
  seats : ℕ
  raw : Fin seats→ℕ

def Observation.Valid (o : Observation) := ∀i,SeatValid o.C o.count (o.raw i) i.val

abbrev RawImage := Σ _C : ℕ, Σ n : ℕ,Fin n→ℕ

def Observation.image (o : Observation) : RawImage := ⟨o.C,o.seats,o.raw⟩

structure Source (A : Type) where
  C : ℕ
  seats : ℕ
  pin : Pins C seats→A

def Source.image {A : Type} (s : Source A) (z : A→Bool) : RawImage :=
  ⟨s.C,s.seats,DescentTerminalEpochBits.raw (z∘s.pin)⟩

def Source.map {A B : Type} (f : A→B) (s : Source A) : Source B := ⟨s.C,s.seats,f∘s.pin⟩

/-- The seed pins remain a fixed subarray at every extension. -/
structure Chart {S Z : Type} (seedBits : Z→S→Bool) (seedOK : (S→Bool)→Prop)
    {U : Type} (source : U→Z) where
  Pin : Type
  [finite : Fintype Pin]
  seed : S→Pin
  store : U→Pin→Bool
  read : (Pin→Bool)→Option U
  rows : (Pin→Bool)→List Observation
  layout : List (Source Pin)
  archived : ∀z, ∃tail,layout.map (fun a=>a.image z)=(rows z).map Observation.image++tail
  complete : ∀z t,read z=some t → layout.map (fun a=>a.image z)=(rows z).map Observation.image
  read_iff : ∀z t,read z=some t ↔ z=store t
  original : ∀t s,store t (seed s)=seedBits (source t) s
  accepted : ∀z,(∃t,read z=some t) ↔ seedOK (z∘seed) ∧ ∀o∈rows z,o.Valid

attribute [instance] Chart.finite

variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {source : U→Z}

theorem Chart.once (c : Chart bits ok source) (t : U) : ∃!z,c.read z=some t := by
  exact ⟨c.store t,(c.read_iff _ _).mpr rfl,fun _ h=>(c.read_iff _ _).mp h⟩

variable (old : Chart bits ok source) {C seats : ℕ} {Fiber I : U→Type}
    (cnt : U→ℕ) (number : ∀u,I u≃Fin (cnt u)) (bound : ∀u,cnt u ≤ seats)
    (profile : ∀u,Fiber u≃(I u→Profile C))

def left (z : old.Pin ⊕ Pins C seats→Bool) := z∘Sum.inl
def right (z : old.Pin ⊕ Pins C seats→Bool) := z∘Sum.inr

def extendedStore (t : Σu,Fiber u) : old.Pin ⊕ Pins C seats→Bool :=
  Sum.elim (old.store t.1) (DescentTerminalEpochBits.store (number t.1) (profile t.1 t.2))

def extendedRead (z : old.Pin ⊕ Pins C seats→Bool) : Option (Σu,Fiber u) :=
  (old.read (left old z)).bind fun u=>
    (DescentTerminalEpochBits.read (number u) (bound u) (right old z)).map fun p=>⟨u,(profile u).symm p⟩

def extendedRows (z : old.Pin ⊕ Pins C seats→Bool) : List Observation :=
  old.rows (left old z) ++ match old.read (left old z) with
    | none=>[]
    | some u=>[⟨C,cnt u,seats,raw (right old z)⟩]

theorem extended_iff (z : old.Pin ⊕ Pins C seats→Bool) (t : Σu,Fiber u) :
    extendedRead old cnt number bound profile z=some t ↔ z=extendedStore old cnt number profile t := by
  rcases t with ⟨u,v⟩
  constructor
  · intro h
    cases c : old.read (left old z) with
    | none=>simp [extendedRead,c] at h
    | some x=>
      cases p : DescentTerminalEpochBits.read (number x) (bound x) (right old z) with
      | none=>simp [extendedRead,c,p] at h
      | some y=>
        simp only [extendedRead,c,p,Option.bind_some,Option.map_some,Option.some.injEq] at h
        cases h
        have hl := (old.read_iff _ _).mp c
        have hr := (DescentTerminalEpochBits.read_iff _ _ _ _).mp p
        funext a
        rcases a with a|a
        · exact congrFun hl a
        · simpa [extendedStore,right] using congrFun hr a
  · rintro rfl
    have l : left old (extendedStore (seats:=seats) old cnt number profile ⟨u,v⟩)=old.store u := rfl
    have r : right old (extendedStore (seats:=seats) old cnt number profile ⟨u,v⟩)=
        DescentTerminalEpochBits.store (number u) (profile u v) := rfl
    rw [extendedRead,l,(old.read_iff _ _).mpr rfl,r]
    simp [(DescentTerminalEpochBits.read_iff _ _ _ _).mpr rfl]

theorem extended_accepts (z : old.Pin ⊕ Pins C seats→Bool) :
    (∃t,extendedRead old cnt number bound profile z=some t) ↔
      ok ((left old z)∘old.seed) ∧ ∀o∈extendedRows old cnt z,o.Valid := by
  have oldGood := old.accepted (left old z)
  cases c : old.read (left old z) with
  | none=>
    have bad : ¬(ok (left old z∘old.seed) ∧ ∀o∈old.rows (left old z),o.Valid) :=
      fun h=>by obtain ⟨t,e⟩:=oldGood.mpr h; rw [c] at e; contradiction
    simp [extendedRead,extendedRows,c,bad]
  | some u=>
    have live := oldGood.mp ⟨u,c⟩
    have fields := DescentTerminalEpochBits.survives (number u) (bound u) (right old z)
    have extra : (Observation.mk C (cnt u) seats (raw (right old z))).Valid ↔ Good (cnt u) (right old z) := Iff.rfl
    cases hp : DescentTerminalEpochBits.read (number u) (bound u) (right old z) with
    | none=>
      have bad : ¬Good (cnt u) (right old z) := fun g=>by
        obtain ⟨p,hit⟩:=fields.mp g; rw [hp] at hit; contradiction
      simp [extendedRead,extendedRows,c,hp,live.1,extra,bad]
    | some p=>
      have good := fields.mpr ⟨p,hp⟩
      simp [extendedRead,extendedRows,c,hp,live.1]
      intro o ho
      rcases ho with prior|rfl
      · exact live.2 _ prior
      · exact extra.mpr good

def extendedLayout : List (Source (old.Pin ⊕ Pins C seats)) :=
  old.layout.map (Source.map Sum.inl) ++ [⟨C,seats,Sum.inr⟩]

private theorem layout_eq (z : old.Pin ⊕ Pins C seats→Bool) :
    (extendedLayout old).map (fun a=>a.image z)=
      old.layout.map (fun a=>a.image (left old z))++[⟨C,seats,raw (right old z)⟩] := by
  simp only [extendedLayout,List.map_append,List.map_map,List.map_cons,List.map_nil]
  rfl

def extend : Chart bits ok (fun t : Σu,Fiber u=>source t.1) where
  Pin := old.Pin ⊕ Pins C seats
  seed := Sum.inl∘old.seed
  store := extendedStore old cnt number profile
  read := extendedRead old cnt number bound profile
  rows := extendedRows old cnt
  layout := extendedLayout old
  archived z := by
    rw [layout_eq]
    cases c : old.read (left old z) with
    | none=>
      obtain ⟨tail,h⟩:=old.archived (left old z)
      refine ⟨tail++[⟨C,seats,raw (right old z)⟩],?_⟩
      simp [extendedRows,c,h,List.append_assoc]
    | some t=>
      refine ⟨[],?_⟩
      simp [extendedRows,c,old.complete _ _ c,Observation.image]
  complete z p hit := by
    rw [layout_eq]
    cases c : old.read (left old z) with
    | none=>simp [extendedRead,c] at hit
    | some t=>simp [extendedRows,c,old.complete _ _ c,Observation.image]
  read_iff := extended_iff old cnt number bound profile
  original t s := old.original t.1 s
  accepted := extended_accepts old cnt number bound profile

end
end Hierarchy.DescentTerminalEpochChart

end OAI
