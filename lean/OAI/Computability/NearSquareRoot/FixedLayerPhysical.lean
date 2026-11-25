import OAI.Computability.NearSquareRoot.FixedLayerDispatch
import OAI.Computability.NearSquareRoot.FixedLayerSetup
import OAI.Computability.NearSquareRoot.FixedLayerPlan

/-! # Physical execution of an entire generated Fourier or adjoint word

Every matrix is taken from the generated word. Every array allowed by the
input energy bound can be used as the payload of the same tape program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space FixedLayerTickets
  DigitPacking ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram

set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
noncomputable section

theorem diagonal {I : Type} (n : I → ℕ) (hv : ∀ i, Directory (n i)) (dir : I → Bool)
    (hd : ∀ i, 4 ≤ (box (n i)).length) (hn : ∀ i, 2 ≤ n i)
    (clock : ℕ → ℕ) (hl : ∀ i, phaseClock (n i) ≤ clock (n i)) :
    Implements n hv dir hd clock .diagonal := by
  let J := {e : RowInput n hv dir // HasKind n hv dir .diagonal e}
  let idx (e : J) := e.val.instanceIndex
  have tags (e : J) :
      ((directedPlan (rowKey n dir (idx e)))[e.val.position.val]).2.1 = kindCode .diagonal := by
    have h := e.property
    simpa only [HasKind,RowInput.ticket,header_at] using h
  obtain ⟨out,hr,he⟩ := phaseRowBranch (fun e : J => n (idx e)) (fun e => e.val.position.val)
    (fun e => dir (idx e)) (fun e => hn (idx e)) (fun e => hv (idx e)) (fun e => hd (idx e))
    (fun e => e.val.position.isLt) tags (fun e => e.val.payload) (fun e => e.val.inRange)
  refine ⟨out,?_,he⟩
  apply (hr.mono (fun e => hl (idx e)) (fun _ => le_rfl)).conform
    (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl)
  intro e
  change .fork (send _) (framed _) = Tree.fork (send (e.val.ticket n hv dir)) (framed _)
  rw [RowInput.ticket,header_at]
  rfl

/-- The selected physical source at a working array determines the rounded
mathematical update. Values outside the proven working range only extend the
mathematical map to a total function. The tape command reads the opcode. -/
theorem transform {I : Type} (n : I → ℕ) (hv : ∀ i, Directory (n i)) (dir : Bool)
    (hd : ∀ i, 4 ≤ (box (n i)).length) (hn : ∀ i, 2 ≤ n i) (hk : ∀ i, 1024 ≤ addressBits (n i))
    (clock : ℕ → ℕ) (hl : ∀ i, phaseClock (n i) ≤ clock (n i))
    (perm : Implements n hv (fun _ => dir) hd clock .permutation)
    (walsh : Implements n hv (fun _ => dir) hd clock .walsh) :
    ∃ F : (i : I) → Program (hv i), (∀ i, if dir then InverseOK (hv i) (F i) else ForwardOK (hv i) (F i)) ∧
      AdmissiblePass n hv (fun m => 3*boxDepth (addressBits m)*clock m + m)
        (fun i => eval (hv i) (F i)) := by
  classical
  let d (_ : I) := dir
  obtain ⟨y,run,err⟩ := dispatch n hv d hd hn clock (fun i => (Nat.le_mul_of_pos_right _
    (Nat.zero_lt_succ _)).trans (hl i)) (fun kind => by
      cases kind
      · exact perm
      · exact diagonal n hv d hd hn clock hl
      · exact walsh)
  let out (i : I) (j : Fin (tickets (n i) dir).length) (x : Array (n i)) : Array (n i) :=
    if h : working (hv i) x then y ⟨i,j,x,h⟩ else x
  have action (e : RowInput n hv d) : out e.instanceIndex e.position e.payload = y e := by
    cases e with
    | mk i j x h => simp [out,h]
  have num (i : I) : TicketError (hv i) (hd i) dir (out i) := by
    intro j x hx
    let e : RowInput n hv d := ⟨i,j,x,hx⟩
    exact (action e) ▸ err e
  let F i := programOfRows (hv i) (hd i) dir (out i)
  have valid i := programOfRows_correct (hv i) (hd i) (hk i) dir (out i) (num i)
  refine ⟨F,valid,?_⟩
  let E (u : Tally) := chronological (dir,u)
  have hp : Poly E := ((Code.Poly.const dir).pair Code.Poly.identity).compose chronological_poly
  obtain ⟨K,hK⟩ := headerVolume n hn E hp
  apply runProgram n hv d hn (fun i => (by have := hk i; omega)) F
    (fun i => programOfRows_steps ..)
    (fun i => by
      cases h : dir with
      | false => exact Or.inl (by simpa only [h,Bool.false_eq_true,ite_false] using valid i)
      | true => exact Or.inr (by simpa only [h,ite_true] using valid i))
    out (fun i j x => programOfRows_nextArray (hv i) (hd i) dir (out i) j.val j.isLt x)
    clock _ _ K hK
  · apply run.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro e
    exact congrArg framed (action e).symm
  · exact prepareHeader (fun e : Admitted n hv => n e.val.1) (fun e => hn e.val.1) E hp (fun e => e.val.2)

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
