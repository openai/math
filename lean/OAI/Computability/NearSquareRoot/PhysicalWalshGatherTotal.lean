import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # The selected-bit controller with unrestricted subroutine clocks

Both physical routing calls and the grouped transform retain their named
command files. Their time and workspace may depend on the complete input row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code KernelPass FixedPoint EffectiveBoundedTask Controlled.Reflections
open KernelEffectiveFamily

/-- The router physically returns the permuted records at each admitted width. -/
def PositionTotalAt (router : Cmd) (K : ℕ := 0) : Prop :=
  ∃ t s : {v : PositionInput // K ≤ v.k} → ℕ, EffectiveBoundedTask.Runs router t s
    (fun q => send (table q.val.positions,Odd.words q.val.row))
    (fun q => send (Odd.words (q.val.row ∘ (BoxFin.bitAddress q.val.positions).symm)))

theorem PositionRunsAt.total {router : Cmd} {ρ : ℝ} {K : ℕ}
    (h : PositionRunsAt router ρ K) : PositionTotalAt router K := ⟨_,_,h⟩

/-- The same mask controller executes with arbitrary routing and grouped-pass budgets,
including different costs on the forward and inverse tables. -/
theorem selectedTaskTotal {a W K : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (router grouped : Cmd)
    (route : PositionTotalAt router K)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
    (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i))
    (large : ∀ i,K ≤ k i) (hm : ∀ i, mask i = flags (bits i))
    (inner : ∃ t s : I → ℕ, EffectiveBoundedTask.Runs grouped t s
      (fun i => send ((tally (k i),tally (bits i).card),
        Pieces.words (2^k i) (lift (gatherInput (gatherPerm (bits i)) (x i)))))
      (fun i => send (Odd.words (Pieces.result hw p (k i) (bits i).card
        (lift (gatherInput (gatherPerm (bits i)) (x i))))))) :
    ∃ t s : I → ℕ, EffectiveBoundedTask.Runs (selectedCmd router grouped) t s
      (fun i => send (mask i,Odd.words (x i)))
      (fun i => send (Odd.words (selectedResult hw p (bits i) (x i)))) := by
  let n i := (bits i).card
  let pos i := gatherPerm (bits i)
  let u i := gatherInput (pos i) (x i)
  let y i := Pieces.result hw p (k i) (n i) (lift (u i))
  let f (i : I) : {v : PositionInput // K ≤ v.k} := ⟨⟨k i,pos i,x i⟩,large i⟩
  let b (i : I) : {v : PositionInput // K ≤ v.k} := ⟨⟨k i,(pos i).symm,y i⟩,large i⟩
  obtain ⟨t,s,hr⟩ := route
  obtain ⟨tg,sg,hg⟩ := inner
  let T i := max (t (f i)) (t (b i))
  let S i := max (s (f i)) (s (b i))
  have forward := (hr.on f).mono (t' := T) (s' := S)
    (fun _ => le_max_left ..) (fun _ => le_max_left ..)
  have backward := (hr.on b).mono (t' := T) (s' := S)
    (fun _ => le_max_right ..) (fun _ => le_max_right ..)
  have groupedRun : EffectiveBoundedTask.Runs grouped tg sg
      (fun i => send ((tally (k i),tally (n i)),Odd.words (u i)))
      (fun i => send (Odd.words (y i))) := by
    simpa only [lift_words,n,u,y,pos] using hg
  let runCmd := ((((beginCmd.join (leftCmd router)).join middleCmd).join (leftCmd grouped)).join restoreCmd).join router
  have stages : EffectiveBoundedTask.Runs runCmd (fun i => T i + tg i + Odd.volume (k i))
      (fun i => max (S i) (sg i) + Odd.volume (k i))
      (fun i => send (control (n i) (pos i),Odd.words (x i)))
      (fun i => send (Odd.words (selectedResult hw p (bits i) (x i)))) :=
    command_contract runCmd from
      conjugate k n (fun i => by simpa [n] using (bits i).card_le_univ) pos x u y
        (fun i => selectedResult hw p (bits i) (x i)) T S tg sg forward.task groupedRun.task backward.task
  have scanner : EffectiveBoundedTask.Runs maskCmd (fun m : List Bool => Odd.volume m.length) (fun m => Odd.volume m.length)
      send (fun m => send (control (m.count true) (GatherMask.perm m))) := GatherMask.control_volume.choose_spec
  have prep := AgendaOps.left (scanner.on mask) (fun i => send (Odd.words (x i)))
  have packet i : control ((mask i).count true) (GatherMask.perm (mask i)) = control (n i) (pos i) := by
    rw [hm i]; exact (control_eq (bits i)).symm
  dsimp only [Function.comp_apply] at prep
  simp only [packet] at prep
  exact ⟨_,_,AgendaOps.compose prep stages⟩

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
