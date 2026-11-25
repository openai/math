import OAI.Computability.NearSquareRoot.FixedLayerDispatch
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Emitting the two-bit physical Fourier-row dispatcher -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate Space FixedPoint DigitPacking FixedLayerTickets
  SynchronizedLayers SynchronizedLayers.ScheduleProgram ShortFourier.BatchWord SynchronizedPadding Matrix
open EffectiveBoundedTask

set_option maxRecDepth 3500
noncomputable section

private theorem budgetFamily {P : Type} [Primcodable P] {I : P → Type}
    {t s tt ss : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    (h : Family t s u v) (D E : ℕ) (ht : ∀ p i, t p i+1 ≤ D*(tt p i+1))
    (hs : ∀ p i, s p i+1 ≤ E*(ss p i+1)) : Family tt ss u v := by
  obtain ⟨c,R,he,hr,hc⟩ := h
  exact ⟨c,R,he,hr,fun p => ⟨(hc p).1,(hc p).2.bound D E (ht p) (hs p)⟩⟩

/-- Dispatch on one encoded bit. Both parameter-dependent command families
carry their own checked code generation and register bounds. -/
theorem effectiveChooseResult {P X : Type} [Primcodable P] {I : P → Type} [Codec X]
    {Y : (p : P) → I p → Type} (xs : ∀ p, I p → X) (bit : X → Bool) (easy : Easy bit)
    (dst : ∀ p (i : I p), Y p i → Tree) (ok : ∀ p (i : I p), Y p i → Prop)
    {t n : ∀ p, I p → ℕ} (hnt : ∀ p i, n p i ≤ t p i) (K : ℕ)
    (vol : ∀ p i, size (xs p i) ≤ K*(n p i+1))
    (branches : ∀ b : Bool, ∃ out : ∀ p (e : {i // bit (xs p i) = b}), Y p e.val,
      Family (fun p e => t p e.val) (fun p e => n p e.val) (fun p e => send (xs p e.val))
        (fun p e => dst p e.val (out p e)) ∧ ∀ p e, ok p e.val (out p e)) :
    ∃ out : ∀ p i, Y p i, Family t n (fun p i => send (xs p i)) (fun p i => dst p i (out p i)) ∧
      ∀ p i, ok p i (out p i) := by
  classical
  choose f fRun fOk using branches
  let y p i := f (bit (xs p i)) p ⟨i,rfl⟩
  refine ⟨y,?_,fun p i => fOk _ p ⟨i,rfl⟩⟩
  have branch (b : Bool) : Family
      (fun p (e : {i // bit (xs p i) = b}) => t p e.val) (fun p e => n p e.val)
      (fun p e => send (xs p e.val)) (fun p e => dst p e.val (y p e.val)) := by
    apply (fRun b).conform (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    rintro p ⟨i,rfl⟩
    rfl
  have setup : Family t n (fun p i => send (xs p i))
      (fun p i => send (bit (xs p i),xs p i)) :=
    Family.joint (linearTree (fun x => (bit x,x)) (easy.pair Easy.identity)
      (fun z : Sigma I => xs z.1 z.2) K (fun z => hnt z.1 z.2) (fun z => vol z.1 z.2))
  have interpret := Family.control (t := t) (s := n) (u := fun p i => send (xs p i))
    (v := fun p i => dst p i (y p i)) (fun p i => bit (xs p i)) (branch false) (branch true)
  exact setup.sequence (budgetFamily interpret 1 (K+2) (fun _ _ => by simp) (fun p i => by
    have hs := vol p i
    change n p i + size (xs p i) + 1 ≤ _
    rw [Nat.add_mul]; omega))

open private classify actual_code inputSize from OAI.Computability.NearSquareRoot.FixedLayerDispatch

variable {P : Type} [Primcodable P] {I : P → Type}
  (n : ∀ p, I p → ℕ) (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)
  (hd : ∀ p i, 4 ≤ (box (n p i)).length)

/-- A generated command for one of the three row types, including the
accuracy certificate for the actual array the command returned. -/
def EffectiveImplementsAt (arena clock : P → ℕ → ℕ) (kind : Kind) : Prop :=
  ∃ y : ∀ p (e : {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) kind e}),
      Array (n p e.val.instanceIndex),
    Family (fun p e => clock p (n p e.val.instanceIndex)) (fun p e => arena p (n p e.val.instanceIndex))
      (fun p e => send (encodedInput (n p) (hv p) (dir p) e.val)) (fun p e => framed (y p e)) ∧
      ∀ p e, rowError (n p) (hv p) (dir p) (hd p) e.val (y p e)

/-- A linearly bounded generated row family. -/
def EffectiveImplements (clock : P → ℕ → ℕ) (kind : Kind) : Prop :=
  EffectiveImplementsAt n hv dir hd (fun _ j => j) clock kind

/-- The two physical opcode bits select a generated Walsh, diagonal or
permutation command. The finite register cutoff is common to all parameters. -/
theorem effectiveDispatchAt (hn : ∀ p i, 2 ≤ n p i) (arena clock : P → ℕ → ℕ)
    (fit : ∀ p i, n p i ≤ arena p (n p i)) (lin : ∀ p i, arena p (n p i) ≤ clock p (n p i))
    (runs : ∀ kind, EffectiveImplementsAt n hv dir hd arena clock kind) :
    ∃ y : ∀ p (e : RowInput (n p) (hv p) (dir p)), Array (n p e.instanceIndex),
      Family (fun p e => clock p (n p e.instanceIndex)) (fun p e => arena p (n p e.instanceIndex))
        (fun p e => send (encodedInput (n p) (hv p) (dir p) e)) (fun p e => framed (y p e)) ∧
        ∀ p e, rowError (n p) (hv p) (dir p) (hd p) e (y p e) := by
  let X p := RowInput (n p) (hv p) (dir p)
  let src p := encodedInput (n p) (hv p) (dir p)
  let fst (x : Payload) := x.1.1.1
  let snd (x : Payload) := x.1.1.2
  have fe : Easy fst := by unfold fst; fun_prop
  have se : Easy snd := by unfold snd; fun_prop
  have hcode p (e : X p) : kindCode (classify ((e.ticket (n p) (hv p) (dir p)).1)) = (e.ticket (n p) (hv p) (dir p)).1 := by
    rw [RowInput.ticket,header_at]
    exact actual_code _ _
  have volume p (e : X p) : size (src p e) ≤ 1920000100000*(arena p (n p e.instanceIndex)+1) :=
    (inputSize (n p) (hv p) (dir p) (hn p) e).trans
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ (fit p e.instanceIndex)))
  apply effectiveChooseResult src fst fe (fun _ _ => framed)
    (fun p => rowError (n p) (hv p) (dir p) (hd p)) (fun p e => lin p e.instanceIndex)
    1920000100000 volume
  intro a
  cases a with
  | true =>
    let J p := {e : X p // fst (src p e) = true}
    have cast p (e : J p) : HasKind (n p) (hv p) (dir p) .walsh e.val := by
      have h := hcode p e.val
      have ha : (e.val.ticket (n p) (hv p) (dir p)).1.1 = true := e.property
      simpa [HasKind,classify,ha] using h.symm
    obtain ⟨out,machine,num⟩ := runs .walsh
    let f p (e : J p) := (⟨e.val,cast p e⟩ : {e : X p // HasKind (n p) (hv p) (dir p) .walsh e})
    exact ⟨fun p e => out p (f p e),machine.on f,fun p e => num p (f p e)⟩
  | false =>
    let J p := {e : X p // fst (src p e) = false}
    apply effectiveChooseResult (fun p (e : J p) => src p e.val) snd se (fun _ _ => framed)
      (fun p e => rowError (n p) (hv p) (dir p) (hd p) e.val)
      (fun p e => lin p e.val.instanceIndex) 1920000100000
      (fun p e => volume p e.val)
    intro b
    let L p := {e : J p // snd (src p e.val) = b}
    let kind : Kind := if b then .diagonal else .permutation
    have cast p (e : L p) : HasKind (n p) (hv p) (dir p) kind e.val.val := by
      have h := hcode p e.val.val
      have ha : (e.val.val.ticket (n p) (hv p) (dir p)).1.1 = false := e.val.property
      have hb : (e.val.val.ticket (n p) (hv p) (dir p)).1.2 = b := e.property
      simpa [HasKind,classify,ha,hb,kind] using h.symm
    obtain ⟨out,machine,num⟩ := runs kind
    let f p (e : L p) := (⟨e.val.val,cast p e⟩ : {e : X p // HasKind (n p) (hv p) (dir p) kind e})
    exact ⟨fun p e => out p (f p e),machine.on f,fun p e => num p (f p e)⟩


/-- Dispatch with the operand length as the shared arena. -/
theorem effectiveDispatch (hn : ∀ p i, 2 ≤ n p i) (clock : P → ℕ → ℕ) (lin : ∀ p i, n p i ≤ clock p (n p i))
    (runs : ∀ kind, EffectiveImplements n hv dir hd clock kind) :
    ∃ y : ∀ p (e : RowInput (n p) (hv p) (dir p)), Array (n p e.instanceIndex),
      Family (fun p e => clock p (n p e.instanceIndex)) (fun p e => n p e.instanceIndex)
        (fun p e => send (encodedInput (n p) (hv p) (dir p) e)) (fun p e => framed (y p e)) ∧
        ∀ p e, rowError (n p) (hv p) (dir p) (hd p) e (y p e) :=
  effectiveDispatchAt n hv dir hd hn (fun _ j => j) clock (fun _ _ => le_rfl) lin runs

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
