import OAI.Computability.BorderVNP.CubeScatterDigits
import Mathlib.Data.List.GetD

/-! # Exact image of a packet scatter with its two routed input streams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

/-- The actual expected bit and the way it reaches its packet slot. -/
inductive Position
  | selector (bit : Bool) | crossing (bit : Bool) | localBit (bit : Bool) | unused

/-- Routed bits carry no local choice. -/
def Position.digit : Position → Digit
  | .selector _ => .selector | .crossing _ => .crossing | .localBit b => .privateBit b | .unused => .unused

/-- Unused reservations have no specified value and retain their incoming word. -/
def Position.value : Position → Option Bool
  | .selector b | .crossing b | .localBit b => some b | .unused => none

/-- The two routed read cursors and the consecutive destination cursor. -/
structure Cursor where
  /-- Address of the next common selector bit. -/
  selector : ℕ
  /-- Address of the next crossing bit after the selector prefix. -/
  crossing : ℕ
  /-- Address of the next reserved word in this packet or singleton block. -/
  dest : ℕ

/-- Each source advances exactly on positions supplied by its corresponding stream. -/
def Cursor.next (c : Cursor) (p : Position) : Cursor :=
  ⟨match p with | .selector _ => c.selector+1 | _ => c.selector,
   match p with | .crossing _ => c.crossing+1 | _ => c.crossing, c.dest+1⟩

/-- The entry ABI of the per-digit scatter. -/
def Cursor.loaded {w : ℕ} (c : Cursor) (s : Bank w) : Prop :=
  s 36 = word w c.selector ∧ s 37 = word w c.crossing ∧ s 38 = word w c.dest ∧ s 59 = 1

/-- Resident, addressable source and a separated packet-bank destination. -/
def Position.ready {w : ℕ} (p : Position) (src : Set ℕ) (c : Cursor) (m : Memory w) : Prop :=
  c.dest ∉ src ∧ c.dest < 2^w ∧ match p with
    | .selector b => c.selector ∈ src ∧ c.selector < 2^w ∧ m c.selector = wordBit w b
    | .crossing b => c.crossing ∈ src ∧ c.crossing < 2^w ∧ m c.crossing = wordBit w b
    | _ => True

/-- The write at a single reserved packet position. -/
def Position.write {w : ℕ} (p : Position) (dst : ℕ) (m : Memory w) : Memory w :=
  match p.value with | some b => Function.update m dst (wordBit w b) | none => m

private theorem ready_congr {w : ℕ} {src : Set ℕ} {c : Cursor} {p : Position} {m m' : Memory w}
    (h : ∀ x ∈ src, m' x = m x) (hp : p.ready src c m) : p.ready src c m' := by
  cases p with
  | selector b | crossing b =>
    obtain ⟨d,e,f,g,i⟩ := hp
    exact ⟨d,e,f,g,(h _ f).trans i⟩
  | localBit _ | unused => exact hp

private theorem writes_outside {w : ℕ} (p : Position) (m : Memory w) {dst x : ℕ} (h : x ≠ dst) :
    p.write dst m x = m x := by
  cases p <;> simp [Position.write,Position.value,Function.update_of_ne h]

/-- Exact word, cursor and register effects of one instruction group. -/
theorem digit_image {w : ℕ} (p : Position) (src : Set ℕ) (c : Cursor) (s : Bank w) (m : Memory w)
    (hc : c.loaded s) (hp : p.ready src c m) :
    let e := p.digit.step s m
    (c.next p).loaded e.bank ∧ e.mem = p.write c.dest m ∧
      ∀ j : Reg, j ∉ ([36,37,38,60] : List Reg) → e.bank j = s j := by
  obtain ⟨h36,h37,h38,h59⟩ := hc
  obtain ⟨_,hd,hr⟩ := hp
  have succWord (a : ℕ) : word w a + 1 = word w (a+1) := (word_add w a 1).symm
  cases p with
  | selector b | crossing b =>
    obtain ⟨_,ha,hb⟩ := hr
    simp (config := {decide := true}) [Position.digit,Digit.step,Digit.mode,Mode.code,copyDigit,
      Code.block,effect,Cursor.next,Cursor.loaded,Position.write,Position.value,
      BinaryOp.eval,Function.update,h36,h37,h38,h59,succWord,-word_add,word_val _ _ hd,
      word_val _ _ ha,hb]
    intro j h36' h37' h38' h60'
    simp [h36',h37',h38',h60']
  | localBit b =>
    cases b <;>
      simp (config := {decide := true}) [Position.digit,Digit.step,Digit.mode,Mode.code,writeLocal,
        Code.block,effect,Cursor.next,Cursor.loaded,Position.write,Position.value,wordBit,
        BinaryOp.eval,Function.update,h36,h37,h38,h59,succWord,-word_add,word_val _ _ hd] <;>
      intro j h36' h37' h38' h60' <;> simp [h38',h60']
  | unused =>
    simp (config := {decide := true}) [Position.digit,Digit.step,Digit.mode,Mode.code,effect,
      Cursor.next,Cursor.loaded,Position.write,Position.value,BinaryOp.eval,Function.update,
      h36,h37,h38,h59,succWord,-word_add]
    intro j h36' h37' h38' h60'
    simp [h38']

/-- Prescribed routed words and separation for every position in chronological order. -/
def Prepared {w : ℕ} (src : Set ℕ) : List Position → Cursor → Memory w → Prop
  | [],_,_ => True
  | p::ps,c,m => p.ready src c m ∧ Prepared src ps (c.next p) m

/-- A prepared scatter depends only on the contents of its routed source addresses. -/
theorem prepared_congr {w : ℕ} {src : Set ℕ} (ps : List Position) (c : Cursor)
    (m m' : Memory w) (h : ∀ x ∈ src, m' x = m x) (hp : Prepared src ps c m) : Prepared src ps c m' := by
  induction ps generalizing c with
  | nil => trivial
  | cons p ps ih => exact ⟨ready_congr h hp.1, ih _ hp.2⟩

/-- Mathematical writes to the destination bank in native order. -/
def image {w : ℕ} : List Position → ℕ → Memory w → Memory w
  | [],_,m => m
  | p::ps,dst,m => image ps (dst+1) (p.write dst m)

/-- Final routed cursor values after the listed positions. -/
def advance : List Position → Cursor → Cursor
  | [],c => c
  | p::ps,c => advance ps (c.next p)

/-- The entire returned packet bank is the mathematical image; all scratch-free registers
retain their values for the surrounding owned-row scan. -/
theorem result_image {w : ℕ} (src : Set ℕ) (ps : List Position) (c : Cursor) (s : Bank w)
    (m : Memory w) (hc : c.loaded s) (hp : Prepared src ps c m) :
    let e := result (ps.map Position.digit) s m
    (advance ps c).loaded e.bank ∧ e.mem = image ps c.dest m ∧
      ∀ j : Reg, j ∉ ([36,37,38,60] : List Reg) → e.bank j = s j := by
  induction ps generalizing c s m with
  | nil => exact ⟨hc,rfl,fun _ _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨hc',hm,hr⟩ := digit_image p src c s m hc hp.1
    have same (x : ℕ) (hx : x ∈ src) : (p.digit.step s m).mem x = m x := by
      rw [hm]
      exact writes_outside p m (by intro h; exact hp.1.1 (h ▸ hx))
    obtain ⟨endc,endm,endr⟩ := ih _ _ _ hc' (prepared_congr ps _ _ _ same hp.2)
    exact ⟨endc,by simpa only [List.map_cons,result,image,Cursor.next,hm] using endm,
      fun j hj => (endr j hj).trans (hr j hj)⟩

/-- An address outside the packet reservation retains its original contents. -/
theorem image_outside {w : ℕ} (ps : List Position) (dst : ℕ) (m : Memory w) {a : ℕ}
    (ha : a < dst ∨ dst+ps.length ≤ a) : image ps dst m a = m a := by
  induction ps generalizing dst m with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.length_cons] at ha
    exact (ih (dst+1) _ (by omega)).trans (writes_outside p m (by omega))

/-- The image of a prepared scatter leaves every word of the routed source region in place. -/
theorem Prepared.image_source {w : ℕ} {src : Set ℕ} {ps : List Position} {c : Cursor} {m : Memory w}
    (hp : Prepared src ps c m) {a : ℕ} (ha : a ∈ src) : image ps c.dest m a = m a := by
  induction ps generalizing c m with
  | nil => rfl
  | cons p ps ih =>
    have kept (j : ℕ) (hj : j ∈ src) : p.write c.dest m j = m j :=
      writes_outside p m (by intro eqn; exact hp.1.1 (eqn ▸ hj))
    have ready := prepared_congr ps (c.next p) m (p.write c.dest m) kept hp.2
    exact (ih (c := c.next p) ready).trans (kept a ha)

/-- Split a single prepared sequence at its prefix, taking the actual prefix writes and cursor
advances into account in the preparation of the remaining positions. -/
theorem Prepared.split {w : ℕ} {src : Set ℕ} {ps qs : List Position} {c : Cursor} {m : Memory w}
    (hp : Prepared src (ps ++ qs) c m) :
    Prepared src ps c m ∧ Prepared src qs (advance ps c) (image ps c.dest m) := by
  have orig : Prepared src ps c m ∧ Prepared src qs (advance ps c) m := by
    induction ps generalizing c with
    | nil => exact ⟨trivial,hp⟩
    | cons p ps ih =>
      obtain ⟨pre,tail⟩ := ih (c := c.next p) hp.2
      exact ⟨⟨hp.1,pre⟩,tail⟩
  exact ⟨orig.1,prepared_congr qs _ _ _ (fun _ ha => orig.1.image_source ha) orig.2⟩

/-- Every used slot contains its prescribed bit at its native word address. -/
theorem image_at {w : ℕ} (ps : List Position) (dst : ℕ) (m : Memory w) (k : Fin ps.length)
    {b : Bool} (hb : ps[k].value = some b) : image ps dst m (dst+k.val) = wordBit w b := by
  induction ps generalizing dst m with
  | nil => exact Fin.elim0 k
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) k hb
    · intro h
      have e : p.value = some b := h
      rw [image,image_outside _ _ _ (Or.inl (by simp)),Position.write,e]
      simp
    · intro h
      have e := ih (dst+1) (p.write dst m) j h
      simpa [image,Nat.add_assoc,Nat.add_comm 1] using e

end Cube.Scatter

end BorderVNP
end Computability
end OAI
