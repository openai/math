import OAI.Computability.BorderVNP.TeamSiteEndpointArray
import OAI.Computability.BorderVNP.TeamSiteConsistencyRows

/-!
# Elapsed times recovered from the shared physical frame array

Each accepted local block spends exactly its cumulative native instruction and
burst charge. Summing the verified local transitions identifies the incoming
offset of every processor and fixes the final word-sized elapsed timestamp.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamSiteConsistency

variable {w p r k a teams : ℕ}

/-- The clock recorded by a single independent physical endpoint is exactly the
incoming clock plus the charged local path, without wraparound. -/
theorem EndpointRow.elapsed_cost {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {first out : Frame w r}
    {es : List (TeamRAM.Event w)} (row : EndpointRow P pub lib H limit cap first es out) :
    out.elapsed.val = first.elapsed.val + cost es ∧ out.elapsed ≤ limit := by
  cases first with
  | accepted t =>
    obtain ⟨rfl,ht,rfl⟩ := row
    exact ⟨by simp [Frame.elapsed,cost,RAMBuckets.cost],ht⟩
  | live word regs t =>
    obtain ⟨ht,pc,z,fin,_,run,endMode⟩ := row
    have tot := blockWindow_total H limit t cap ht
    have safe : (blockWindow H limit t cap).Safe := by unfold Window.Safe; rw [← tot]; exact limit.isLt
    obtain ⟨_,hg,_,_,_,hz,_⟩ := run.clock safe
    change limit.val = t.val+(blockWindow H limit t cap).global.val at tot
    change fin.elapsed.val = t.val+cost es at hz
    have bounded : fin.elapsed ≤ limit := show fin.elapsed.val ≤ limit.val by omega
    rcases endMode with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> exact ⟨hz,bounded⟩

private theorem offset_indices (teams : ℕ) (first : Frame w r) (input out : Fin teams → Frame w r)
    (blocks : Fin teams → List (TeamRAM.Event w)) (head : ∀ j, j.val = 0 → input j = first)
    (adj : ∀ i j, j.val = i.val+1 → input j = out i)
    (time : ∀ j, (out j).elapsed.val = (input j).elapsed.val + cost (blocks j)) :
    ∀ j, (input j).elapsed.val = first.elapsed.val + blockOffset blocks j := by
  induction teams generalizing first with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    refine Fin.cases ?_ ?_
    · simp [head 0 rfl,blockOffset,RAMBuckets.cost]
    · intro j
      have sub := ih (out 0) (fun j => input j.succ) (fun j => out j.succ) (fun j => blocks j.succ)
        (fun j h => adj 0 j.succ (by simp [h]))
        (fun i j h => adj i.succ j.succ (by simp [h])) (fun j => time j.succ) j
      rw [sub,time 0,head 0 rfl]
      simp [blockOffset,cost,Nat.add_assoc]

/-- The physical incoming clock agrees with the timestamp used to lay out this
processor's sorter records. This holds even for empty trailing blocks after acceptance. -/
theorem EndpointRows.predecessor_elapsed {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {first : Frame w r}
    {blocks : Fin teams → List (TeamRAM.Event w)} {out : Fin teams → Frame w r}
    (rows : EndpointRows P pub lib H limit cap first (List.ofFn blocks) (List.ofFn out)) (j : Fin teams) :
    (predecessor first out j).elapsed.val = first.elapsed.val + blockOffset blocks j :=
  let checks := native_frame_checks first out
  offset_indices teams first _ out blocks checks.initial checks.adjacent
    (fun i => (((endpointRows_iff_pointwise ..).mp rows i).elapsed_cost).1) j

/-- The final elapsed word stores the total charge of the concatenated native path. -/
theorem EndpointRows.last_elapsed {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {first final : Frame w r}
    {rows : List (List (TeamRAM.Event w))} {out : List (Frame w r)}
    (checked : EndpointRows P pub lib H limit cap first rows out) (last : out.getLast? = some final) :
    final.elapsed.val = first.elapsed.val + cost rows.flatten := by
  induction rows generalizing first out with
  | nil =>
    have eq : out = [] := checked
    simp [eq] at last
  | cons es rest ih =>
    cases out with
    | nil => simp at last
    | cons next fs =>
      have here := checked.1.elapsed_cost.1
      cases fs with
      | nil =>
        have e : next = final := by simpa using last
        subst final
        cases rest with
        | nil => simpa [cost] using here
        | cons => exact False.elim checked.2
      | cons f fs =>
        have hz := ih checked.2 (by simpa only [List.getLast?_cons_cons] using last)
        simp [hz,here,cost,Nat.add_assoc]

/-- Testing only the actual final halt bit recovers the complete canonical final frame
and exact total time when the initial public timestamp is zero. -/
theorem EndpointRows.final_frame {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {first final : Frame w r}
    {rows : List (List (TeamRAM.Event w))} {out : List (Frame w r)}
    (checked : EndpointRows P pub lib H limit cap first rows out) (zero : first.elapsed = 0)
    (last : out.getLast? = some final) (halt : final.halted = true) :
    out.getLast? = some (.accepted (packed w (cost rows.flatten))) := by
  have he := checked.last_elapsed last
  rw [zero,Fin.val_zero,Nat.zero_add] at he
  cases final with
  | live => contradiction
  | accepted t =>
    change t.val = cost rows.flatten at he
    have word : t = packed w (cost rows.flatten) := by
      apply Fin.ext
      rw [packed_val (he ▸ t.isLt),he]
    exact word ▸ last

end TeamSite

end BorderVNP
end Computability
end OAI
