import OAI.Computability.NearSquareRoot.FixedLayerSweep
import OAI.Computability.NearSquareRoot.FixedLayerFrame
import OAI.Computability.NearSquareRoot.FixedCandidateGuard
import OAI.Computability.NearSquareRoot.SynchronizedRowMembership
import OAI.Computability.NearSquareRoot.PhysicalBoxPhase

/-! # Dispatching a physical row by its two encoded opcode bits -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate Space FixedPoint DigitPacking FixedLayerTickets
  SynchronizedLayers SynchronizedLayers.ScheduleProgram ShortFourier.BatchWord SynchronizedPadding Matrix

set_option maxRecDepth 3500
noncomputable section

/-- Branch output values may have different dependent types at different widths.
Only the input bit is consulted to select their physical commands. -/
theorem chooseResult {I X : Type} [Codec X] {Y : I → Type}
    (xs : I → X) (bit : X → Bool) (easy : Easy bit)
    (dst : (i : I) → Y i → Tree) (ok : (i : I) → Y i → Prop)
    {t n : I → ℕ} (hnt : ∀ i, n i ≤ t i) (K : ℕ) (vol : ∀ i, size (xs i) ≤ K*(n i+1))
    (branches : ∀ b : Bool, ∃ out : (e : {i // bit (xs i) = b}) → Y e.val,
      BoundedTask (fun e => t e.val) (fun e => n e.val) (fun e => send (xs e.val))
        (fun e => dst e.val (out e)) ∧ ∀ e, ok e.val (out e)) :
    ∃ out : (i : I) → Y i, BoundedTask t n (fun i => send (xs i)) (fun i => dst i (out i)) ∧
      ∀ i, ok i (out i) := by
  classical
  choose f hrun hok using branches
  let y i := f (bit (xs i)) ⟨i,rfl⟩
  refine ⟨y,?_,fun i => hok _ ⟨i,rfl⟩⟩
  have branch (b : Bool) :
      BoundedTask (fun e : {i // bit (xs i) = b} => t e.val) (fun e => n e.val)
        (fun e => send (xs e.val)) (fun e => dst e.val (y e.val)) := by
    apply (hrun b).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rintro ⟨i, rfl⟩
    rfl
  have setup := linearTree (fun x => (bit x,x)) (easy.pair Easy.identity) xs K hnt vol
  have interpret := BoundedTask.control (t := t) (s := n) (src := fun i => send (xs i))
    (dst := fun i => dst i (y i)) (fun i => bit (xs i)) (branch false) (branch true)
  apply sequence setup
  apply interpret.bound 1 (K+2) (fun _ => by simp)
  intro i
  have h := vol i
  change n i + size (xs i) + 1 ≤ _
  rw [Nat.add_mul]
  omega

private def classify (bits : Bool × Bool) : Kind :=
  if bits.1 then .walsh else if bits.2 then .diagonal else .permutation

private theorem classify_code (s : Kind) : classify (kindCode s) = s := by cases s <;> rfl

private theorem second_mem {X : Type} {b : Bool} {w : List X} {r : Bool × X}
    (hr : r ∈ orientRows (b,w)) : r.2 ∈ w := by
  cases b
  · change r ∈ w.map (fun x => (false,x)) at hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact hx
  · change r ∈ w.reverse.map (fun x => (true,x)) at hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact List.mem_reverse.mp hx

private theorem actual_code (p : Key) (j : Fin (directedPlan p).length) :
    kindCode (classify (directedPlan p)[j.val].2.1) = (directedPlan p)[j.val].2.1 := by
  let r := (directedPlan p)[j.val]
  have mem : r ∈ orientRows (p.1,boxPlan p.2) := List.getElem_mem ..
  have h := second_mem mem
  obtain ⟨u,_,hc⟩ := List.mem_flatMap.mp h
  simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at hc
  change kindCode (classify r.2.1) = r.2.1
  rcases hc with z|z|z <;> rw [z] <;> rfl

variable {I : Type} (n : I → ℕ) (hv : ∀ i, Directory (n i)) (dir : I → Bool)
  (hd : ∀ i, 4 ≤ (box (n i)).length)

abbrev Payload := Ticket × (Tally × List Dusk.Pair)

def encodedInput (e : RowInput n hv dir) : Payload :=
  (e.ticket n hv dir,tally (n e.instanceIndex),records e.payload)

def rowError (e : RowInput n hv dir) (y : Array (n e.instanceIndex)) : Prop :=
  let _ := BoxFin.modulus_neZero (hv e.instanceIndex)
  let r := (directedPlan (rowKey n dir e.instanceIndex))[e.position.val]
  let M := boxRow (physicalLayout (hv e.instanceIndex)) (hd e.instanceIndex) r
  ‖recordArray (y ∘ index (hv e.instanceIndex)) - WithLp.toLp 2
    (M *ᵥ (fun z => recordArray (e.payload ∘ index (hv e.instanceIndex)) z))‖ ≤
      1/(2:ℝ)^(50*addressBits (n e.instanceIndex))

def HasKind (kind : Kind) (e : RowInput n hv dir) : Prop :=
  (e.ticket n hv dir).1 = kindCode kind

def Implements (clock : ℕ → ℕ) (kind : Kind) : Prop :=
  ∃ y : (e : {e : RowInput n hv dir // HasKind n hv dir kind e}) → Array (n e.val.instanceIndex),
    BoundedTask (fun e => clock (n e.val.instanceIndex)) (fun e => n e.val.instanceIndex)
      (fun e => send (encodedInput n hv dir e.val)) (fun e => framed (y e)) ∧
      ∀ e, rowError n hv dir hd e.val (y e)

private theorem inputSize (hn : ∀ i, 2 ≤ n i) (e : RowInput n hv dir) :
    size (encodedInput n hv dir e) ≤ 1920000100000*(n e.instanceIndex+1) := by
  let i := e.instanceIndex
  have h := phaseStageTicket_size (addressBits (n i)) (dir i) e.position.val e.position.isLt
  have w : addressBits (n i)+1 ≤ 192*n i :=
    (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans (array_volume (hn i))
  have q := framed_size (hn i) e.payload
  have head : e.ticket n hv dir = phaseStageTicket (addressBits (n i)) (dir i) e.position.val e.position.isLt :=
    header_at _ _
  change (send (e.ticket n hv dir)).count + (framed e.payload).count + 1 ≤ _
  rw [head]
  change size _ + _ + 1 ≤ _
  dsimp only [i] at *
  omega

/-- A single dispatcher runs all three physical row implementations. -/
theorem dispatch (hn : ∀ i, 2 ≤ n i) (clock : ℕ → ℕ) (lin : ∀ i, n i ≤ clock (n i))
    (runs : ∀ kind, Implements n hv dir hd clock kind) :
    ∃ y : (e : RowInput n hv dir) → Array (n e.instanceIndex),
      BoundedTask (fun e => clock (n e.instanceIndex)) (fun e => n e.instanceIndex)
        (fun e => send (encodedInput n hv dir e)) (fun e => framed (y e)) ∧
      ∀ e, rowError n hv dir hd e (y e) := by
  let X := RowInput n hv dir
  let src := encodedInput n hv dir
  let fst (x : Payload) := x.1.1.1
  let snd (x : Payload) := x.1.1.2
  have fe : Easy fst := by unfold fst; fun_prop
  have se : Easy snd := by unfold snd; fun_prop
  have hcode (e : X) : kindCode (classify ((e.ticket n hv dir).1)) = (e.ticket n hv dir).1 := by
    rw [RowInput.ticket,header_at]
    exact actual_code _ _
  apply chooseResult src fst fe (fun _ => framed) (rowError n hv dir hd) (fun e => lin e.instanceIndex)
    1920000100000 (inputSize n hv dir hn)
  intro a
  cases a with
  | true =>
    let J := {e : X // fst (src e) = true}
    have cast (e : J) : HasKind n hv dir .walsh e.val := by
      have h := hcode e.val
      have ha : (e.val.ticket n hv dir).1.1 = true := e.property
      simpa [HasKind,classify,ha] using h.symm
    obtain ⟨out,run,num⟩ := runs .walsh
    let f (e : J) := (⟨e.val,cast e⟩ : {e : X // HasKind n hv dir .walsh e})
    exact ⟨fun e => out (f e),run.on f,fun e => num (f e)⟩
  | false =>
    let J := {e : X // fst (src e) = false}
    apply chooseResult (fun e : J => src e.val) snd se (fun _ => framed) (fun e => rowError n hv dir hd e.val)
      (fun e => lin e.val.instanceIndex) 1920000100000 (fun e => inputSize n hv dir hn e.val)
    intro b
    let L := {e : J // snd (src e.val) = b}
    let kind : Kind := if b then .diagonal else .permutation
    have cast (e : L) : HasKind n hv dir kind e.val.val := by
      have h := hcode e.val.val
      have ha : (e.val.val.ticket n hv dir).1.1 = false := e.val.property
      have hb : (e.val.val.ticket n hv dir).1.2 = b := e.property
      simpa [HasKind,classify,ha,hb,kind] using h.symm
    obtain ⟨out,run,num⟩ := runs kind
    let f (e : L) := (⟨e.val.val,cast e⟩ : {e : X // HasKind n hv dir kind e})
    exact ⟨fun e => out (f e),run.on f,fun e => num (f e)⟩

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
