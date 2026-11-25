import OAI.Hierarchy.TaggedWireReachable

namespace OAI
/-! # Reachable calendar cursors for the existing fixed-site trace and selector tape -/

noncomputable section
set_option maxHeartbeats 800000
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM.Calendar Tagged LinearAlgebra.SpectralBooks ChordGraph
open scoped BigOperators Classical
variable {X : Type} {slot : Event→Slot X} {events : List Event} {x₀ : X}
namespace Prefix

structure Cursor (slot : Event→Slot X) (events : List Event) (x₀ : X) where
  todo : List Event
  mem : X
  path : Prefix slot events x₀ todo mem

local notation "P" => Prefix slot events x₀
local notation "V" => Cursor slot events x₀

def nextAt {e tail x} (p : P (e::tail) x) (c : (slot e).choice x) : V :=
  ⟨tail,(slot e).next x c,.advance p c⟩

def atCursor {tail x} (h : P tail x) : V := ⟨tail,x,h⟩

structure Frame (Y : Type) (n : ℕ) where
  choice : Type
  [finite : Fintype choice]
  word : choice ↪ Bits n
  next : choice → Y
attribute [instance] Frame.finite

def idleFrame {Y : Type} (v : Y) (n : ℕ) : Frame Y n where
  choice := Unit
  finite := inferInstance
  word := ⟨fun _ _=>false, fun _ _ _=>Subsingleton.elim ..⟩
  next _ := v

def liveFrame {e tail x} (p : P (e::tail) x) : Frame V (slot e).bits where
  choice := (slot e).choice x
  finite := (slot e).finite x
  word := (slot e).word x
  next := nextAt p

def cursorFrame (e : Event) : V → Frame V (slot e).bits
  | v@⟨[],_,_⟩ => idleFrame v (slot e).bits
  | v@⟨f::_,_,p⟩ =>
    if same : f=e then cast (congrArg (fun a=>Frame V (slot a).bits) same) (liveFrame p)
    else idleFrame v (slot e).bits

theorem frame_live (e : Event) (tail : List Event) (x : X) (p : P (e::tail) x) :
    cursorFrame e (atCursor p) = liveFrame p := by
  simp [cursorFrame,atCursor]

theorem frame_other (e f : Event) (tail : List Event) (x : X) (p : P (f::tail) x) (ne : f ≠ e) :
    cursorFrame e (atCursor p) = idleFrame (atCursor p) (slot e).bits := by
  simp [cursorFrame,atCursor,ne]

theorem frame_nil (e : Event) (x : X) (p : P [] x) :
    cursorFrame e (atCursor p) = idleFrame (atCursor p) (slot e).bits := rfl

def choices (e : Event) (v : V) := (cursorFrame e v).choice
instance choicesFinite (e : Event) (v : V) : Fintype (choices e v) := (cursorFrame e v).finite
def word (e : Event) (v : V) : choices e v ↪ Bits (slot e).bits := (cursorFrame e v).word
def move (e : Event) (v : V) : choices e v → V := (cursorFrame e v).next

def cursorSlot (e : Event) : Slot V where
  bits := (slot e).bits
  choice := choices e
  word := word e
  next := move e

def beginCursor (slot : Event→Slot X) (events : List Event) (x₀ : X) : Cursor slot events x₀ :=
  ⟨events,x₀,.start⟩

private def continuations {Y : Type} {n : ℕ} (Q : Y → Type) (D : Frame Y n) :=
  Σ c : D.choice, Q (D.next c)

def framePair {Y : Type} {n : ℕ} (Q : Y → Type) {D T : Frame Y n}
    (same : D=T) (c : T.choice) (j : Q (T.next c)) : Σ a : D.choice,Q (D.next a) :=
  cast (congrArg (continuations Q) same.symm) ⟨c,j⟩

theorem framePair_word {Y : Type} {n : ℕ} (Q : Y → Type) {D T : Frame Y n}
    (same : D=T) (c : T.choice) (j : Q (T.next c)) (a : Fin n) :
    D.word (framePair Q same c j).1 a = T.word c a := by cases same; rfl

theorem framePair_tail {Y : Type} {B : Sort*} {n : ℕ} (Q : Y → Type) {D T : Frame Y n}
    (same : D=T) (c : T.choice) (j : Q (T.next c)) (eval : ∀v, Q v → B) :
    eval _ (framePair Q same c j).2 = eval _ j := by cases same; rfl

/-- Following the scheduled events reads exactly their original choices. -/
def original : ∀{tail x}(p : P tail x),Path cursorSlot tail (atCursor p)≃Path slot tail x
  | [],_,_=>Equiv.refl Unit
  | e::tail,x,p=>
    (Equiv.cast (congrArg (continuations (Path cursorSlot tail)) (frame_live e tail x p))).trans
      (Equiv.sigmaCongrRight fun a:(slot e).choice x=>original (advance p a))

theorem bitCount (tail : List Event) :
    bits (cursorSlot (events:=events) (x₀:=x₀) (slot:=slot)) tail=bits slot tail := by
  induction tail with
  | nil=>rfl
  | cons e tail ih=>exact congrArg ((slot e).bits+·) ih

/-- Replaying an original semantic history gives a cursor history with the
same input/output memory and exactly the same header words. -/
def replay : ∀{tail x}(p : P tail x),Path slot tail x→Path cursorSlot tail (atCursor p)
  | [],_,_,_=>()
  | e::tail,x,p,⟨c,rest⟩=>
    framePair (Path cursorSlot tail) (frame_live e tail x p) c (replay (advance p c) rest)

/-- Evaluating the rest of a replayed path gives the result at its genuine advanced cursor. -/
theorem replay_tail_apply {e tail x} (p : P (e::tail) x) (c : (slot e).choice x)
    (j : Path slot tail ((slot e).next x c)) {B : Sort*}
    (eval : ∀v : V,Path cursorSlot tail v → B) :
    eval _ (replay p ⟨c,j⟩).2 = eval (atCursor (advance p c)) (replay (advance p c) j) :=
  framePair_tail (Path cursorSlot tail) (frame_live e tail x p) c (replay (advance p c) j) eval

private theorem encode_left (s : Event→Slot X) (e : Event) (tail : List Event) (x : X)
    (j : Path s (e::tail) x) (a : Fin (s e).bits) :
    encode s (e::tail) x j (Fin.castAdd (bits s tail) a) = (s e).word x j.1 a := by
  change (Fin.addCases ((s e).word x j.1) (encode s tail ((s e).next x j.1) j.2) :
    Fin ((s e).bits+bits s tail) → Bool) _ = _
  exact Fin.addCases_left ..

private theorem encode_right (s : Event→Slot X) (e : Event) (tail : List Event) (x : X)
    (j : Path s (e::tail) x) (a : Fin (bits s tail)) :
    encode s (e::tail) x j (Fin.natAdd (s e).bits a) = encode s tail ((s e).next x j.1) j.2 a := by
  change (Fin.addCases ((s e).word x j.1) (encode s tail ((s e).next x j.1) j.2) :
    Fin ((s e).bits+bits s tail) → Bool) _ = _
  exact Fin.addCases_right ..

theorem replay_word : ∀{tail x}(p : P tail x)(j : Path slot tail x)(i : Fin (bits slot tail)),
    encode cursorSlot tail (atCursor p) (replay p j) (i.cast (bitCount (events:=events) (x₀:=x₀) tail).symm) =
      encode slot tail x j i
  | [],_,_,_,i=>i.elim0
  | e::tail,x,p,⟨c,j⟩,i=>by
    let q := replay (advance p c) j
    let same := frame_live e tail x p
    induction i using Fin.addCases with
    | left a=>
      have pos : (a.castAdd (bits slot tail)).cast (bitCount (events:=events) (x₀:=x₀) (e::tail)).symm =
          a.castAdd (bits (cursorSlot (events:=events) (x₀:=x₀) (slot:=slot)) tail) := Fin.ext rfl
      rw [pos]
      exact (encode_left cursorSlot e tail (atCursor p) (replay p ⟨c,j⟩) a).trans
        ((framePair_word (Path cursorSlot tail) same c q a).trans (encode_left slot e tail x ⟨c,j⟩ a).symm)
    | right a=>
      let idx := a.cast (bitCount (events:=events) (x₀:=x₀) tail).symm
      have pos : (Fin.natAdd (slot e).bits a).cast (bitCount (events:=events) (x₀:=x₀) (e::tail)).symm =
          Fin.natAdd (slot e).bits idx := Fin.ext rfl
      rw [pos]
      exact (encode_right cursorSlot e tail (atCursor p) (replay p ⟨c,j⟩) idx).trans
        ((framePair_tail (Path cursorSlot tail) same c q (fun v jj=>encode cursorSlot tail v jj idx)).trans
          ((replay_word (advance p c) j a).trans (encode_right slot e tail x ⟨c,j⟩ a).symm))

variable {S : ℕ} {F : Type*} [Field F] (width : ∀{tail x},Prefix slot events x₀ tail x→Widths S)
    (M : ∀{e tail x}(h : Prefix slot events x₀ (e::tail) x) (c : (slot e).choice x),
      SiteMatrix (State (width h)) (State (width (advance h c))) F)

def atWidth (width : ∀{tail x},Prefix slot events x₀ tail x→Widths S)
    (v : Cursor slot events x₀) : Widths S := width v.path

private def StepLaw : Prop := ∀{e tail x}(p : Prefix slot events x₀ (e::tail) x) (v : ∀ i,State (width p) i),(raw F (width p)).coeff v=
    ∑c,SiteMatrix.act (M p c) (raw F (width (advance p c))).coeff v

/-- Transport the operator together with its sum equation, so the two always use the same
choice type, enumeration and successor on both sides of a cursor comparison. -/
private structure FrameAction (F : Type*) [Field F] {Y : Type} (W : Y→Widths S)
    (v : Y) {n : ℕ} (f : Frame Y n) (law : Prop) where
  matrix : ∀ a : f.choice,SiteMatrix (State (W v)) (State (W (f.next a))) F
  total : law → ∀x,(raw F (W v)).coeff x = (@Finset.univ f.choice f.finite).sum
    (fun a=>SiteMatrix.act (matrix a) (raw F (W (f.next a))).coeff x)

private def idleAction {Y : Type} (W : Y→Widths S) (v : Y) (n : ℕ) (law : Prop) :
    FrameAction F W v (idleFrame v n) law where
  matrix := fun _=>SiteMatrix.identity (State (W v))
  total := by
    intro _ x
    change _=∑ _ : Unit,SiteMatrix.act (SiteMatrix.identity (State (W v))) (raw F (W v)).coeff x
    rw [Fintype.sum_unique]
    exact (SiteMatrix.act_id (B:=State (W v)) (raw F (W v)).coeff x).symm

private def cursorAction (e : Event) (v : Cursor slot events x₀) :
    FrameAction F (atWidth @width) v (cursorFrame e v) (StepLaw (slot:=slot) (events:=events) (x₀:=x₀) @width @M) := by
  obtain ⟨todo,m,p⟩:=v
  cases todo with
  | nil=>
    change FrameAction F (atWidth @width) (atCursor p) (cursorFrame e (atCursor p)) _
    rw [frame_nil e m p]
    exact idleAction _ _ _ _
  | cons f tail=>
    change FrameAction F (atWidth @width) (atCursor p) (cursorFrame e (atCursor p)) _
    by_cases same : f=e
    · subst f
      rw [frame_live e tail m p]
      exact ⟨fun a=>M p a,fun valid x=>valid p x⟩
    · rw [frame_other e f tail m p same]
      exact idleAction _ _ _ _

def atStep (e : Event) (v : Cursor slot events x₀) (c : (cursorSlot e).choice v) :
    SiteMatrix (State (atWidth @width v)) (State (atWidth @width ((cursorSlot e).next v c))) F :=
  (cursorAction @width @M e v).matrix c

theorem atStep_sum (stage : ∀{e tail x}(p : Prefix slot events x₀ (e::tail) x) (v : ∀ i,State (width p) i),(raw F (width p)).coeff v=
    ∑c,SiteMatrix.act (M p c) (raw F (width (advance p c))).coeff v)
    (e : Event) (v : Cursor slot events x₀) (x : ∀i,State (atWidth @width v) i) :
    (raw F (atWidth @width v)).coeff x=∑a,SiteMatrix.act (atStep @width @M e v a)
      (raw F (atWidth @width ((cursorSlot e).next v a))).coeff x :=
  (cursorAction @width @M e v).total @stage x

end Prefix
end Hierarchy.WireTelescope.CalendarTape

end
end OAI
