import OAI.Hierarchy.TaggedWireTapeAdmission

namespace OAI
/-! # The original immutable binary tape, read at the true chronology -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical

variable {X : Type} {W q d : ℕ} {slot : Event→Slot X}

structure WordSlots (slot : Event→Slot X) (W : ℕ) where
  base : Event→ℕ
  cells : Event→ℕ
  width : ∀e,(slot e).bits=cells e*W

namespace WordSlots
variable (L : WordSlots slot W)

def read (e : Event) (m : Memory W) : Bits (slot e).bits :=
  fun j=>arrayBits (L.cells e) W (fun i=>m (L.base e+i.val)) (Fin.cast (L.width e) j)

def install (e : Event) (word : Bits (slot e).bits) (m : Memory W) : Memory W :=
  let data := (arrayBits (L.cells e) W).symm (fun i=>word (Fin.cast (L.width e).symm i))
  fillSegment (L.base e) (L.cells e) (fun a=>if h:a-L.base e<L.cells e then data ⟨a-L.base e,h⟩ else 0) m

theorem read_install (e : Event) (word : Bits (slot e).bits) (m : Memory W) :
    L.read e (L.install e word m)=word := by
  let packed := fun j=>word (Fin.cast (L.width e).symm j)
  have one : (fun i : Fin (L.cells e)=>L.install e word m (L.base e+i.val))=
      (arrayBits _ W).symm packed := by
    funext i
    simp [install,fillSegment,i.isLt,packed]
  funext j
  unfold read
  rw [one,Equiv.apply_symm_apply]
  rfl

def static : (es : List Event)→Memory W→Bits (bits slot es)
  | [],_=>Fin.elim0
  | e::es,m=>Fin.addCases (L.read e m) (static es m)

def header : (es : List Event)→Bits (bits slot es)→Memory W→Memory W
  | [],_,m=>m
  | e::es,raw,m=>L.install e (fun j=>raw (Fin.castAdd (bits slot es) j))
      (header es (fun j=>raw (Fin.natAdd (slot e).bits j)) m)

def disjoint : List Event→Prop
  | []=>True
  | e::es=>(∀t∈es,∀i : Fin (L.cells t),¬(L.base e≤L.base t+i.val ∧ L.base t+i.val<L.base e+L.cells e)) ∧ disjoint es

def agrees (es : List Event) (m m' : Memory W) := ∀e∈es,∀j : Fin (L.cells e),m (L.base e+j.val)=m' (L.base e+j.val)

theorem read_congr (e : Event) {m m' : Memory W}
    (same : ∀j : Fin (L.cells e),m (L.base e+j.val)=m' (L.base e+j.val)) : L.read e m=L.read e m' := by
  unfold read
  rw [funext same]

theorem static_congr (es : List Event) {m m' : Memory W} (same : L.agrees es m m') :
    L.static es m=L.static es m' := by
  induction es with
  | nil=>rfl
  | cons e es ih=>
    change (Fin.addCases (L.read e m) (L.static es m) : Bits ((slot e).bits+bits slot es))=Fin.addCases (L.read e m') (L.static es m')
    rw [L.read_congr e (same e (by simp)),ih (fun t h=>same t (List.mem_cons_of_mem _ h))]

theorem static_header (es : List Event) (raw : Bits (bits slot es)) (m : Memory W) (sep : L.disjoint es) :
    L.static es (L.header es raw m)=raw := by
  induction es with
  | nil=>exact funext fun i=>Fin.elim0 i
  | cons e es ih=>
    let first := fun j=>raw (Fin.castAdd (bits slot es) j)
    let last := fun j=>raw (Fin.natAdd (slot e).bits j)
    let tail := L.header es last m
    have keep : L.agrees es (L.install e first tail) tail := by
      intro t ht j
      simp only [install,fillSegment,ite_eq_right (sep.1 t ht j)]
    change Fin.addCases (L.read e (L.install e first tail)) (L.static es (L.install e first tail))=raw
    rw [L.read_install,L.static_congr es keep,ih last sep.2]
    funext j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> simp [first,last]

theorem chronology (C : Chart W q d) (es : List Event) (m : Memory W)
    (ok : mounted C es m)
    (safe : ∀t∈es,∀i : Fin (L.cells t),∀e∈es,protected C (L.base t+i.val) e) :
    actual slot C L.read es m=L.static es m := by
  induction es generalizing m with
  | nil=>rfl
  | cons e es ih=>
    have keep : L.agrees es (after C e m) m := fun t ht j=>
      after_frame C e m (L.base t+j.val) ok.1 (safe t (List.mem_cons_of_mem _ ht) j e (by simp))
    change (Fin.addCases (L.read e m) (actual slot C L.read es (after C e m)) : Bits ((slot e).bits+bits slot es))=L.static (e::es) m
    rw [ih _ ok.2 (fun t ht j u hu=>safe t (List.mem_cons_of_mem _ ht) j u (List.mem_cons_of_mem _ hu)),
      L.static_congr es keep]
    rfl

theorem initial_agrees (size : ℕ) (es : List Event) (raw : Bits (bits slot es)) (m : Memory W)
    (room : ∀e∈es,L.base e+L.cells e≤ size) :
    L.agrees es (Computability.VPVNP.RAMMemory.initialMemory size (L.header es raw m)) (L.header es raw m) := by
  intro e he j
  have bound := room e he
  have fit := j.isLt
  simp [Computability.VPVNP.RAMMemory.initialMemory,show L.base e+j.val< size by omega]

/-- The word supplied to the host is literally the one tested on the
chronological native execution. A rejected word needs no terminal geometry. -/
theorem admit_raw (C : Chart W q d) (es : List Event) (x : X) (m initial : Memory W)
    (raw : Bits (bits slot es)) (sep : L.disjoint es)
    (same : L.agrees es m (L.header es raw initial)) (ok : mounted C es m)
    (safe : ∀t∈es,∀i : Fin (L.cells t),∀e∈es,protected C (L.base t+i.val) e)
    (relation : List Event→X→Memory W→Prop)
    (accept : ∀e events z v,relation (e::events) z v →
      (accepted C e v ↔ ∃c,(slot e).word z c=L.read e v))
    (step : ∀e events z v,relation (e::events) z v → ∀c,(slot e).word z c=L.read e v →
      relation events ((slot e).next z c) (after C e v))
    (entrance : relation es x m) :
    admissible C es m ↔ ∃! p : Path slot es x,encode slot es x p=raw := by
  rw [admissible_iff slot C L.read relation accept step es x m entrance,L.chronology C es m ok safe,
    L.static_congr es same,L.static_header es raw initial sep]

end WordSlots
end Hierarchy.WireTelescope.CalendarTape

end
end OAI
