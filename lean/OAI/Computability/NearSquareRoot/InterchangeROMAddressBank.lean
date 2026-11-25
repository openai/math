import OAI.Computability.NearSquareRoot.InterchangeROMColorLabels
import OAI.Computability.NearSquareRoot.InterchangeROMAddressLanes

/-! # Compiling source and destination mask banks

The same descriptor processor runs on every pair of projections in a
runtime-length catalog. The data stream stays parked during this whole loop.
After the masks have been produced, one fixed stable routing program consumes
the mask bank and the stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROMColors Space

variable {D : Type} (desc mask : D → Tree) (cost : D → ℕ)

def pairDesc (p : D × D) : Tree := .fork (desc p.1) (desc p.2)
def pairMasks (p : D × D) : Tree := .fork (mask p.1) (mask p.2)
def pairPrice (p : D × D) := (desc p.1).count + cost p.2 + cost p.1

def bankPrice (xs : List (D × D)) :=
  costSum (pairPrice desc cost) xs + (Task.forest (pairDesc desc) xs).count

theorem bank_task (each : Task cost desc mask) :
    Task (bankPrice desc cost) (Task.forest (pairDesc desc)) (Task.forest (pairMasks mask)) := by
  have pairRun : Task (pairPrice desc cost) (pairDesc desc) (pairMasks mask) :=
    (((each.on (Prod.snd : D × D → D)).right (desc ∘ Prod.fst)).compose
      ((each.on (Prod.fst : D × D → D)).left (mask ∘ Prod.snd)))
  let valid (_ : Unit) (_ : D × D) := True
  have run := Task.mapTask Unit (fun _ => pairDesc desc) (fun _ => pairMasks mask)
    (a:=fun _ => pairPrice desc cost) (B:=valid)
    (pairRun.on (fun s : {s : Unit × (D × D) // valid s.1 s.2} => s.val.2))
  exact run.on fun xs : List (D × D) => ⟨((),xs), by simp [valid]⟩

/-- Constraints for each computed pair of masks and the native row labels.
The comparison descriptors can carry proofs or data erased from their
physical representation. -/
structure BankInput (D : Type) (mask : D → Tree) where
  rows : Labeled (ℕ × ℕ)
  faces : (ℕ × ℕ) → D × D
  correct : ∀ k ∈ rows.colors, pairMasks mask (faces k) = send (rows.masks k)

namespace BankInput

variable {mask}

def configs (x : BankInput D mask) := x.rows.colors.map x.faces

def before (x : BankInput D mask) : Tree := .fork (Task.forest (pairDesc desc) x.configs)
  (send (x.rows.source.map Prod.snd))

theorem ready (x : BankInput D mask) :
    Task.forest (pairMasks mask) x.configs = send (x.rows.colors.map x.rows.masks) := by
  let cols := x.rows.colors
  change Task.forest _ (cols.map x.faces) = send (cols.map x.rows.masks)
  have ok := x.correct
  change ∀ k ∈ cols, _ at ok
  revert ok
  generalize cols = ls
  intro ok
  induction ls with
  | nil => rfl
  | cons c cols ih =>
    simp only [List.map_cons,Task.forest_cons,send_cons, ok c List.mem_cons_self,
      ih (fun k hk => ok k (List.mem_cons_of_mem _ hk))]

def total (x : BankInput D mask) := bankPrice desc cost x.configs + x.rows.work

theorem program (each : Task cost desc mask) :
    Task (total desc cost) (before desc) (fun x : BankInput D mask => x.rows.answer) := by
  have generate := ((bank_task desc mask cost each).on (@configs D mask)).left
    (fun x : BankInput D mask => send (x.rows.source.map Prod.snd))
  let e : (ℕ × ℕ) ↪ ℕ := ⟨fun p => Nat.pair p.1 p.2,fun x y h => by
    simpa only [Nat.unpair_pair] using congrArg Nat.unpair h⟩
  have route := InterchangeROMColors.batch_task.on (fun x : BankInput D mask => x.rows.encode e)
  have physical : Task (fun x : BankInput D mask => x.rows.work) (fun x => x.rows.query)
      (fun x => x.rows.answer) := by
    simpa only [Labeled.encode_work,Labeled.encode_query,Labeled.encode_answer] using route
  apply (generate.conform (fun _ => rfl) (fun _ => rfl)
    (fun x => congrArg (fun h => Tree.fork h (send (x.rows.source.map Prod.snd))) x.ready)).compose physical

end BankInput
end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
