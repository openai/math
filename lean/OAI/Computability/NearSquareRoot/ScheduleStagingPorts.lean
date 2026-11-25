import OAI.Computability.NearSquareRoot.ScheduleStagingBank
import OAI.Computability.NearSquareRoot.ScheduleStagingReset
import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipeline

/-! # Wiring public digit ports to one controller register

The raw public output tape is the physical controller register that supplied
the query. The public input and the core's private tapes occupy a disjoint
bank. All other controller tapes, including the return stack, stay parked.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingPorts

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline

variable {X J I : Type}

/-- The four public digit symbols have an exact representation in the fixed
controller alphabet, regardless of the original alphabet of a candidate. -/
structure Encoding (X : Type) where
  embed : Public.Letter → X
  read : X → Public.Letter
  decode : ∀ a, read (embed a) = a

abbrev Bank (J I : Type) := J ⊕ Option I

def split (shelves : J → Tape X) (working : Option I → Tape X) : Bank J I → Tape X :=
  Sum.elim shelves working

def marked (R : ℕ) (shelves : J → Tape X) (working : Option I → Tape X) :
    Bank J I → Tape (StagingReset.Symbol X) := fun j => StagingReset.markedTape R (split shelves working j)

def shelves : Route J (Bank J I) where
  index := Function.Embedding.inl
  localIndex := Sum.elim some (fun _ => none)
  exactIndex := by rintro i (j|j) <;> simp [eq_comm]

def working : Route (Option I) (Bank J I) where
  index := Function.Embedding.inr
  localIndex := Sum.elim (fun _ => none) some
  exactIndex := by rintro i (j|j) <;> simp [eq_comm]

def port (one : J) : Index I → Bank J I
  | .inl false => .inr none
  | .inl true => .inl one
  | .inr i => .inr (some i)

def publicRoute [DecidableEq J] (one : J) : Route (Index I) (Bank J I) where
  index := ⟨port one, by rintro (b|i) (b'|j) h <;> first | cases b <;> cases b' <;> simp_all [port] | cases b <;> simp_all [port] | cases b' <;> simp_all [port] | simpa [port] using h⟩
  localIndex
    | .inl j => if j=one then some (.inl true) else none
    | .inr none => some (.inl false)
    | .inr (some i) => some (.inr i)
  exactIndex i j := by
    change _ ↔ port one i = j
    rcases i with b|i <;> rcases j with j|(_|j)
    all_goals first | cases b <;> simp [port,eq_comm] | simp [port,eq_comm]

def copyRoute [DecidableEq J] (one : J) : Route Bool (Bank J I) where
  index := ⟨fun b => if b then .inr none else .inl one, by intro a b e; cases a <;> cases b <;> simp_all⟩
  localIndex
    | .inl j => if j=one then some false else none
    | .inr none => some true
    | .inr (some _) => none
  exactIndex b j := by
    change _ ↔ (if b then Sum.inr none else Sum.inl one) = j
    cases b <;> rcases j with j|(_|j) <;> simp [eq_comm]

def markTrack {A : Type} (rd : X → A) (wr : A → X) : StagingBank.Track A (StagingReset.Symbol X) where
  read x := rd x.1.1
  write x a := ((wr a,x.1.2),x.2)

def frame {A : Type} (rd : X → A) (wr : A → X) (h : ∀ a, rd (wr a) = a)
    (R : ℕ) (offset : I → ℤ) : StagingBank.Frame (markTrack rd wr) I where
  offset := offset
  enc _ z a := StagingReset.symbol R z (wr a)
  read_enc _ _ a := h a
  write_enc _ _ _ _ := rfl

def imageTape {A : Type} (wr : A → X) (offset : ℤ) (t : Tape A) : Tape X :=
  ⟨offset+t.pos,wr ∘ t.view⟩

theorem frame_tape {A : Type} (rd : X → A) (wr : A → X) (h : ∀ a, rd (wr a) = a)
    (R : ℕ) (offset : I → ℤ) (j : I) (t : Tape A) :
    StagingBank.tape (frame rd wr h R offset) j t =
      StagingReset.markedTape R (imageTape wr (offset j) t) := rfl

def headOffset (o : ℤ) : Index I → ℤ
  | .inl true => o
  | _ => 0

def ports (e : Encoding X) (o : ℤ) (t : Index I → Tape Public.Letter) :
    Index I → Tape X := fun i => imageTape e.embed (headOffset o i) (t i)

def active (e : Encoding X) (t : Index I → Tape Public.Letter) : Option I → Tape X
  | none => imageTape e.embed 0 (t (.inl false))
  | some i => imageTape e.embed 0 (t (.inr i))

/-- The representation of the digit output lies on the caller's single
selected register. No other register is transformed by the boundary codec. -/
theorem placed [DecidableEq J] (one : J) (e : Encoding X) (R : ℕ) (o : ℤ)
    (shelf : J → Tape X) (base : Option I → Tape X) (t : Index I → Tape Public.Letter) :
    (publicRoute one).put (fun j => StagingReset.markedTape R (ports e o t j))
        (marked R shelf base) =
      marked R (Function.update shelf one (imageTape e.embed o (t (.inl true)))) (active e t) := by
  funext j
  rcases j with j|(_|j)
  · by_cases eq : j=one
    · subst j; simp [Route.put,publicRoute,marked,split,ports,headOffset]
    · simp [Route.put,publicRoute,marked,split,eq]
  · rfl
  · rfl

theorem image_loaded {A : Type} (wr : A → X) (blank : A) (s : List A) (o : ℤ) :
    imageTape wr o (Tape.loaded blank s) = ⟨o,(Tape.loaded (wr blank) (s.map wr)).view⟩ := by
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  refine ⟨Int.add_zero _,funext fun k => ?_⟩
  cases k <;> simp [Tape.loaded,List.getElem?_map,Option.getD_map]

end StagingPorts

end NearSquareRoot
end Computability
end OAI
