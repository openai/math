import OAI.Computability.NearSquareRoot.ScheduleRegisterLookup
import OAI.Computability.NearSquareRoot.ScheduleRegisterDivide
import OAI.Computability.NearSquareRoot.KernelSelectorAlign

/-! # Common-register access to an arity-dependent set of address slots -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterAlign
open IntegerMultiplication Code RegisterWitness KernelSelectorAlign Filter

theorem left {X : Type*} {R : ℕ} (hR : 0 < R) {t : X → ℕ} {p q : X → Tree}
    (h : Timed R t p q) (z : X → Tree) :
    Timed R t (fun x => .fork (p x) (z x)) (fun x => .fork (q x) (z x)) :=
  register_witness R from Task.left (forget h) z

theorem right {X : Type*} {R : ℕ} (hR : 3 ≤ R) {t : X → ℕ} {p q : X → Tree}
    (h : Timed R t p q) (z : X → Tree) :
    Timed R (fun x => (z x).count+t x) (fun x => .fork (z x) (p x)) (fun x => .fork (z x) (q x)) :=
  register_witness R from Task.right (forget h) z

private theorem bitSize (l : List Bool) : size l = 2*l.length+1 :=
  KernelSelectorAlign.columns_size 0 l

/-- A zipper compiled on pairs of raw trees applies at every user type and encoding. -/
theorem align : ∀ᶠ R in atTop, ∀ n,
    Timed R List.length (slots n) (fun xs : List (Column n) => send xs) := by
  have zip := RegisterSelect.checked_eventually (Task.zipTrees (Prod.fst : Tree × Tree → Tree) Prod.snd)
  filter_upwards [eventually_ge_atTop 4, zip] with R hR hz
  intro n
  induction n with
  | zero =>
    exact register_witness R from (Task.self (b := List.length) (p := send (X := List Bool)))
  | succ n ih =>
    let tail (xs : List (Column (n+1))) := xs.map (fun c => c.2)
    let hd (xs : List (Column (n+1))) := send (xs.map (fun c => c.1))
    let pair (v : Column (n+1)) : Tree × Tree := (send v.1,send v.2)
    have input (xs : List (Column (n+1))) :
        Tree.fork (Task.forest Prod.fst (xs.map pair)) (Task.forest Prod.snd (xs.map pair)) =
          Tree.fork (hd xs) (send (tail xs)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons,Task.forest_cons,Tree.fork.injEq] at ih ⊢
        exact ⟨congrArg (Tree.fork (send x.1)) ih.1,congrArg (Tree.fork (send x.2)) ih.2⟩
    have output (xs : List (Column (n+1))) :
        Task.forest (fun z => Tree.fork z.1 z.2) (xs.map pair) = send xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => exact congrArg (Tree.fork (send x)) ih
    have merge := (Timed.on hz (List.map pair)).conform (fun _ => rfl) input output
    have h := (right (by omega) (ih.on tail) hd).compose merge
    apply h.bound (2*n+10)
    intro xs
    have c := input xs
    simp only [Tree.fork.injEq] at c
    change (hd xs).count + (tail xs).length +
      ((Task.forest Prod.fst (xs.map pair)).count + (Task.forest Prod.snd (xs.map pair)).count) + 1 ≤ _
    rw [c.1,c.2]
    change size (xs.map (fun v => v.1)) + (tail xs).length +
      (size (xs.map (fun v => v.1)) + size (tail xs)) + 1 ≤ _
    rw [bitSize,columns_size n]
    simp only [tail,List.length_map]
    ring_nf
    omega

private theorem frame {R : ℕ} (hR : 4 ≤ R) : ∀ n,
    Timed R List.length (fun xs => send (bitStreams n xs)) (slots n)
  | 0 => by
    have h := register_witness R from (Task.dropRight (fun xs : List (Column 0) => send xs)
      (fun _ => send ([] : List (List Bool))))
    exact (Timed.bound h 4 fun xs => by change size xs+1+1 ≤ _; rw [columns_size]; omega)
  | n+1 => by
    have h := right (by omega) ((frame hR n).on (fun xs : List (Column (n+1)) => xs.map Prod.snd))
      (fun xs => send (xs.map Prod.fst))
    apply h.bound 4
    intro xs
    change size (xs.map Prod.fst)+(xs.map Prod.snd).length+1 ≤ _
    rw [bitSize,List.length_map,List.length_map]
    omega

private theorem slotRulers : ∀ (n : ℕ) (xs : List (Column n)),
    (bitStreams n xs).map (tally ∘ List.length) = List.replicate (n+1) (tally xs.length)
  | 0, _ => rfl
  | n+1, xs => by simp [bitStreams, slotRulers, List.replicate_succ]

private theorem repeatTally {R : ℕ} (hR : 3 ≤ R) : ∀ n : ℕ,
    RegisterWitness.Easy R (fun x : Tally => List.replicate n x)
  | 0 => RegisterWitness.Easy.const (by omega) []
  | n+1 => by
    simpa only [List.replicate_succ,id_eq] using
      (RegisterWitness.Easy.identity.pair hR (repeatTally hR n)).compose RegisterWitness.Easy.cons

/-- Segment a flat slot-major address. Only the arity-specific division and
replication instructions vary, both with a fixed register budget. -/
theorem flatToSlots : ∀ᶠ R in atTop, ∀ n, Timed R List.length
    (fun xs => send (flatBits n xs)) (slots n) := by
  have rulerTask := RegisterSelect.easy_eventually (Code.Easy.ruler (Code.Easy.identity (X := List Bool)))
  have segTask := RegisterSelect.easy_eventually (Piecework.easy (X := Bool)).fstCompose
  filter_upwards [eventually_ge_atTop 4,rulerTask,segTask] with R hR hru hseg
  intro n
  let src := flatBits n
  let W (xs : List (Column n)) := tally xs.length
  have extract := hru.on src
  have width := (RegisterDivide.divide (R := R) (by omega) n).on (fun xs : List (Column n) => xs.length)
  have fit (xs : List (Column n)) : send (ruler (src xs)) = send (tally ((n+1)*xs.length)) := by
    rw [← recover_tally (ruler (src xs))]
    simp [src]
  have width' := (extract.conform (fun _ => rfl) (fun _ => rfl) fit).compose width
  have ws := width'.compose ((repeatTally (R := R) (by omega) (n+1)).on W)
  let d := fun xs : List (Column n) => send (src xs)
  have dup := register_witness R from Task.copy d
  have joint := (Timed.compose dup (left (by omega) ws d))
  let packet (xs : List (Column n)) := (List.replicate (n+1) (W xs),src xs)
  have cut := hseg.on packet
  have same (xs : List (Column n)) : (Piecework.segment (packet xs).1 (packet xs).2).1 = bitStreams n xs := by
    dsimp only [packet,W,src,flatBits]
    rw [← slotRulers,Piecework.prescribed]
  have full := (joint.compose (cut.conform (fun _ => rfl) (fun _ => rfl)
    (fun xs => congrArg send (same xs)))).compose (frame hR n)
  apply full.bound (20*(n+1)+20)
  intro xs
  have sizeRep (k : ℕ) : size (List.replicate k (W xs)) = k*(2*xs.length+2)+1 := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ,size_cons,size_tally,W,ih,Nat.succ_mul] at *
                   omega
  change size (src xs) + (size (src xs)+xs.length+size (W xs)) + size (packet xs) + xs.length + 1 ≤ _
  rw [show size (packet xs) = size (List.replicate (n+1) (W xs))+size (src xs)+1 from rfl,
    sizeRep,bitSize,flat_length,size_tally]
  simp only [W,tally_length]
  ring_nf
  omega

end RegisterAlign

end NearSquareRoot
end Computability
end OAI
