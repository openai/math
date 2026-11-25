import OAI.Computability.BorderVNP.CellFragmentWords

/-! # Reading sparse generator records once, in order

The reader extracts only the current command into private scratch. Its extent is recorded in
the bit framing. A nested body can be replayed by retaining its framed description locally.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape RationalHitting.StackLanguage

/-- Record stream with an iteration marker in front of each self-delimiting command. -/
def records : List (List Bool) → List Bool
  | [] => []
  | row :: rest => true :: (codeWord row ++ records rest)

private def rowPorts : IO → IO ⊕ Unit
  | .row => .inr ()
  | .env => .inl .env
  | .out => .inl .out

private theorem rowPorts_inj : Function.Injective rowPorts := by
  intro a b h; cases a <;> cases b <;> simp_all [rowPorts]

private def iteration (handler : Fragment IO) : Fragment (IO ⊕ Unit) :=
  (Fragment.split (.inl .row) (.inr ())).seq (handler.mount rowPorts)

/-- A finite driver for every sparse command list handled by the given fixed dispatcher. -/
def scan (handler : Fragment IO) : Fragment IO :=
  (Fragment.each (.inl .row) (iteration handler)).hide

private def work (rest env out row : List Bool) : Stacks (IO ⊕ Unit) :=
  Sum.elim (io rest env out) fun _ => row

private theorem setDir (a e o r v : List Bool) :
    Function.update (work a e o r) (.inl .row) v = work v e o r := by
  funext i; cases i with
  | inl k => cases k <;> simp [work,io]
  | inr u => simp [work]

private theorem setRow (a e o r v : List Bool) :
    Function.update (work a e o r) (.inr ()) v = work a e o v := by
  funext i
  cases i with
  | inl k => simp [work]
  | inr u => cases u; simp [work]

private theorem iteration_run (handler : Fragment IO) (row rest env out emitted : List Bool)
    {t : ℕ} (h : handler.Runs t (io row env out) (io [] env (emitted.reverse ++ out))) :
    ∃ u ≤ 2*(7*row.length+10)+t, (iteration handler).Runs u
      (work (codeWord row ++ rest) env out []) (work rest env (emitted.reverse ++ out) []) := by
  obtain ⟨u, hu, split⟩ := Fragment.split_run (src := (Sum.inl IO.row : IO ⊕ Unit))
    (dst := Sum.inr ()) (by simp) (work (codeWord row ++ rest) env out []) row rest rfl rfl
  rw [setDir, setRow] at split
  refine ⟨u+t, by omega, Fragment.runs_seq _ _ split ?_⟩
  apply handler.runs_mount rowPorts_inj h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro k hk
    rcases k with (k|u)
    · cases k with
      | row => rfl
      | env => exact (hk .env rfl).elim
      | out => exact (hk .out rfl).elim
    · cases u; exact (hk .row rfl).elim

private theorem scan_steps {α : Type} (handler : Fragment IO) (payload emitted : α → List Bool)
    (cost : α → ℕ) (env : List Bool) (rows : List α) (out : List Bool)
    (h : ∀ a ∈ rows, ∀ acc, ∃ t ≤ cost a, handler.Runs t (io (payload a) env acc)
      (io [] env ((emitted a).reverse ++ acc))) :
    ∃ d ≤ (rows.map (fun a => 2*(7*(payload a).length+10)+cost a+1)).sum+1,
      (Fragment.each (.inl .row) (iteration handler)).Runs d
        (work (records (rows.map payload)) env out [])
        (work [] env ((rows.flatMap emitted).reverse ++ out) []) := by
  induction rows generalizing out with
  | nil =>
    exact ⟨1, le_rfl, Fragment.each_empty _ _ _ rfl⟩
  | cons a rows ih =>
    obtain ⟨t, ht, hr⟩ := h a List.mem_cons_self out
    obtain ⟨u, hu, run⟩ := iteration_run handler (payload a) (records (rows.map payload))
      env out (emitted a) hr
    obtain ⟨d, hd, next⟩ := ih ((emitted a).reverse ++ out) (fun i hi => h i (List.mem_cons_of_mem _ hi))
    refine ⟨1+u+d, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, records, List.flatMap_cons, List.reverse_append, List.append_assoc]
      apply Fragment.each_cons (u := work (records (rows.map payload)) env ((emitted a).reverse ++ out) [])
        (s := work (true :: (codeWord (payload a) ++ records (rows.map payload))) env out []) rfl _ next
      rwa [setDir]

/-- All sparse commands are passed to the dispatcher exactly once. The stream-processing
overhead is linear in the total encoded length, including for empty command lists. -/
theorem scan_run {α : Type} (handler : Fragment IO) (payload emitted : α → List Bool)
    (cost : α → ℕ) (env : List Bool) (rows : List α) (out : List Bool)
    (h : ∀ a ∈ rows, ∀ acc, ∃ t ≤ cost a, handler.Runs t (io (payload a) env acc)
      (io [] env ((emitted a).reverse ++ acc))) :
    ∃ d ≤ (rows.map (fun a => 2*(7*(payload a).length+10)+cost a+1)).sum+1,
      (scan handler).Runs d (io (records (rows.map payload)) env out)
        (io [] env ((rows.flatMap emitted).reverse ++ out)) := by
  obtain ⟨d, hd, run⟩ := scan_steps handler payload emitted cost env rows out h
  exact ⟨d,hd,Fragment.runs_hide run⟩

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
