import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomZip
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomMap
import OAI.Computability.NearSquareRoot.InterchangeROMProgramEffective

/-! # Broadcasting a numerical sign mask over packed payloads

The zipper aligns the narrow mask with one existing wide row. At each address
the inner loop consumes the original payload and copies its mask once for each
payload cell, including the empty payload.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters LoomRegisters Space

private def repeatBody : Cmd :=
  splitRoot 0 (fun _ => give 0 false)
    ((discard 0).join ((Prog.again 0).join ((clone 1 0 2).join (pack 0))))

def repeatMask : Cmd :=
  splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((Prog.tie repeatBody).join (discard 1)))

theorem repeatMask_within : Within 4 repeatMask := by
  unfold repeatMask repeatBody
  exact split_within (by decide) (fun _ => trivial) ⟨move_within (by decide) (by decide) (by decide),
    split_within (by decide) (fun _ => (by decide : 0 < 4))
      ⟨discard_within (by decide),trivial,clone_within (by decide) (by decide) (by decide),(by decide : 0 < 4)⟩,
    discard_within (by decide)⟩

private theorem repeatBody_fits {K : Type} (tag : Tree) (v : K → Tree) (l : List K) (env : Env) (deck : Deck) :
    let E := repeatBody::env
    Fits E repeatBody (pile 0 (Task.forest v l) (pile 1 tag deck))
      (pile 0 (Task.forest (fun _ => tag) l) (pile 1 tag deck))
      (80 * ((Task.forest v l).count + (Task.forest (fun _ => tag) l).count)) := by
  let E := repeatBody::env
  induction l with
  | nil => exact (fits_bit (i:=0) (c:=fun _ => give 0 false) (b:=false) (fits_give false _ 0 E)).mono (m:=160) (by decide)
  | cons a l ih =>
    let ys := Task.forest (fun _ : K => tag) l
    let xs := Task.forest v l
    have drop := fits_discard 0 (v a) E (pile 0 xs (pile 1 tag deck))
    have tail := ih.again0
    have clone := fits_clone (i:=1) (j:=0) (u:=2) (by decide) (by decide) (by decide)
      tag E (pile 0 ys deck)
    rw [pile_comm 1 tag _ 0 _ (by decide),pile_comm 1 tag _ 0 _ (by decide),
      pile_comm 1 tag _ 0 _ (by decide)] at clone
    have pair := fits_pack tag ys (pile 1 tag deck) 0 E
    have h := fits_pair (c:=fun _ => give 0 false) (drop.join (tail.join (clone.join pair)))
    apply h.mono
    simp only [Task.forest_cons,Tree.count,Nat.mul_add]
    omega

theorem repeatMask_fits {K : Type} (tag : Tree) (v : K → Tree) (l : List K) (env : Env) (deck : Deck) :
    Fits env repeatMask (pile 0 (.fork tag (Task.forest v l)) deck)
      (pile 0 (Task.forest (fun _ => tag) l) deck)
      (100 * (tag.count + (Task.forest v l).count + (Task.forest (fun _ => tag) l).count + 1)) := by
  have mv := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide)
    tag env (pile 0 (Task.forest v l) deck)
  rw [pile_comm 1 _ _ 0 _ (by decide)] at mv
  have core := repeatBody_fits tag v l env deck
  dsimp only at core
  have sub := core.tie
  have dr := fits_discard 1 tag env (pile 0 (Task.forest (fun _ : K => tag) l) deck)
  rw [pile_comm 1 _ _ 0 _ (by decide)] at dr
  exact (fits_pair (mv.join (sub.join dr))).mono (by omega)

/-- Transform a pair of row forests into a single row of packed tags. -/
def amplify : Cmd := zipCommand.join (mapCommand repeatMask)

theorem amplify_within : Within 4 amplify :=
  ⟨zip_within,map_within (by decide) repeatMask_within⟩

theorem amplify_fits {A : Type} {P : A → Type} (tag : A → Tree) (v : (a : A) → P a → Tree)
    (l : List A) (payload : (a : A) → List (P a)) (env : Env) (deck : Deck) :
    let tags := Task.forest tag l
    let row := Task.forest (fun a => Task.forest (v a) (payload a)) l
    let out := Task.forest (fun a => Task.forest (fun _ => tag a) (payload a)) l
    Fits env amplify (pile 0 (.fork tags row) deck) (pile 0 out deck)
      (500 * (tags.count + row.count + out.count + 1)) := by
  let row a := Task.forest (v a) (payload a)
  let wide a := Task.forest (fun _ => tag a) (payload a)
  let pair a := Tree.fork (tag a) (row a)
  let t a := 100 * ((tag a).count + (row a).count + (wide a).count + 1)
  have h (a : A) (env : Env) (deck : Deck) :
      Fits env repeatMask (pile 0 (pair a) deck) (pile 0 (wide a) deck) (t a) :=
    repeatMask_fits (tag a) (v a) (payload a) env deck
  have bound : costSum t l ≤ 100*((Task.forest tag l).count+(Task.forest row l).count+(Task.forest wide l).count) := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [costSum_cons,Task.forest_cons,Tree.count,t,Nat.mul_add] at *; omega
  have x := zip_fits tag row l env deck
  have y := map_fits l pair wide repeatMask t h env deck
  apply (x.join y).mono
  change _ ≤ 500*((Task.forest tag l).count + (Task.forest row l).count + (Task.forest wide l).count + 1)
  omega

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
