import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomWitness
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomMap
import OAI.Computability.NearSquareRoot.ScheduleRegisterLookup

/-!
# Compiled table calls on aligned column banks

A scaffold provides one empty leaf for each record. A nonempty input bank
supplies the same scaffold by erasing one of its columns. A record operation
then acts on the ordered tuple of input fields and produces its output tuple.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

private def eraseCell : Cmd := (discard 0).join (give 0 false)

private def scaffold (rank : ℕ) : Cmd :=
  (clone 0 1 2).join ((cellCommand rank).join ((mapCommand eraseCell).join ((move 1 0 2).join (pack 0))))

private theorem erase_fits (v : Tree) (env : Env) (r : Deck) :
    Fits env eraseCell (pile 0 v r) (pile 0 (.atom false) r) (17 * v.count + 3) :=
  (fits_discard 0 v env r).join (fits_give false ..)

theorem scaffold_within (rank : ℕ) : Within 4 (scaffold rank) :=
  ⟨clone_within (by decide) (by decide) (by decide),
   RegisterSelect.within_mono (by decide : 3 ≤ 4) _ (cell_within _),
   map_within (by decide : 3 ≤ 4) ⟨discard_within (by decide), (by decide : 0 < 4)⟩,
   move_within (by decide) (by decide) (by decide), (by decide : 0 < 4)⟩

private theorem erase_charge {A : Type} (v : A → Tree) (l : List A) :
    costSum (fun a => 17 * (v a).count + 3) l + 100 * (Task.forest (fun _ => .atom false) l).count + 10 ≤
      240 * (Task.forest v l).count := by
  induction l with
  | nil => exact (by decide : 0 + 100 * 1 + 10 ≤ 240 * 1)
  | cons a l ih =>
    simp only [Task.forest_cons, Tree.count, costSum_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Construct the row scaffold from one column, with all other columns restored. -/
theorem scaffold_fits {K A : Type} [DecidableEq K] (cols : Series K) (rows : Series A)
    (v : A → K → Tree) (k : K) (env : Env) (r : Deck) :
    let bank := stripe cols (fun k => stripe rows (fun a => v a k))
    Fits env (scaffold (cols.explore.idxOf k)) (pile 0 bank r)
      (pile 0 (.fork bank (stripe rows (fun _ => .atom false))) r) (430 * bank.count + 10) := by
  let col k := stripe rows (fun a => v a k)
  let bank := stripe cols col
  let blank := stripe rows (fun _ => .atom false)
  have small : (col k).count ≤ bank.count := by
    rw [show bank = Task.forest col cols.explore from stripe_simple ..]
    exact count_le_forest col (cols.complete k)
  have cp := fits_clone (i := 0) (j := 1) (u := 2) (by decide) (by decide) (by decide) bank env r
  have sel := cell_fits col cols.explore _ k (List.getElem?_idxOf (cols.complete k)) env (pile 1 bank r)
  rw [← stripe_simple] at sel
  have er := map_fits rows.explore (fun a => v a k) (fun _ => .atom false) eraseCell
    (fun a => 17 * (v a k).count + 3) (fun a => erase_fits (v a k)) env (pile 1 bank r)
  have er' := er.mono (erase_charge (fun a => v a k) rows.explore)
  rw [← stripe_simple, ← stripe_simple] at er'
  change Fits _ _ _ (pile 0 blank (pile 1 bank r)) _ at er'
  rw [pile_comm 0 blank r 1 bank (by decide)] at er'
  have mv := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) bank env (pile 0 blank r)
  apply (cp.join (sel.join (er'.join (mv.join (fits_pack bank blank r 0 env))))).mono
  change 45 * bank.count + (90 * bank.count + (240 * (col k).count +
    (42 * bank.count + 1 + 2) + 2) + 2) + 2 ≤ 430 * bank.count + 10
  omega

/-- A compiled conjugation on a bank supplied together with its empty-row scaffold. -/
def alignedCore {L : Type} [DecidableEq L] (dst : Series L) (op : Cmd) : Cmd :=
  blendCommand.join ((mapCommand op).join (transposeCommand dst))

/-- A nonempty bank obtains its row count and scaffold by one physical column read. -/
def alignedCommand {L : Type} [DecidableEq L] (rank : ℕ) (dst : Series L) (op : Cmd) : Cmd :=
  (scaffold rank).join (alignedCore dst op)

theorem alignedCore_within {L : Type} [DecidableEq L] (dst : Series L) {op : Cmd}
    (ho : Within 4 op) : Within 4 (alignedCore dst op) :=
  ⟨blend_within, map_within (by decide) ho,
   RegisterSelect.within_mono (by decide : 3 ≤ 4) _ (transpose_within dst)⟩

theorem aligned_within {L : Type} [DecidableEq L] (rank : ℕ) (dst : Series L) {op : Cmd}
    (ho : Within 4 op) : Within 4 (alignedCommand rank dst op) :=
  ⟨scaffold_within _, alignedCore_within dst ho⟩

/-- The full operation clock when the scaffold is supplied. Its middle term sums
the actual leaf budgets across the stream. -/
def alignClock (fields outFields vin vout leafWork : ℕ) : ℕ :=
  401 * (fields + 1) * (vin + 1) + leafWork + 100 * vout + 10 +
    250 * (outFields + 1) * (vout + 1) + 4


/-- The working space of the aligned operation comprises one active record call
and constant multiples of its input and output matrices. -/
def alignSpace (leafSpace fields vin vout : ℕ) : ℕ :=
  leafSpace + 320 * vin + 320 * vout + 2 * fields + 20

open private row_bound rowForest blendInput colForest emptyRows from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomBlend

theorem alignedCore_bounded {K L A : Type} [DecidableEq L] (cols : Series K) (dst : Series L)
    (rows : Series A) (v : A → K → Tree) (w : A → L → Tree) (op : Cmd) (t : A → ℕ) (S : ℕ)
    (hc : ∀ a env r base, DeckCap base r →
      BoundedFits env op (pile 0 (stripe cols (v a)) r) (pile 0 (stripe dst (w a)) r)
        (t a) (base + S) S) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let p := Tree.fork (stripe cols (fun k => stripe rows (fun a => v a k))) (stripe rows (fun _ => .atom false))
    let out := stripe dst (fun l => stripe rows (fun a => w a l))
    let V := (stripe rows (stripe dst ∘ w)).count
    let D := alignSpace S dst.count p.count V
    BoundedFits env (alignedCore dst op) (pile 0 p r) (pile 0 out r)
      (alignClock cols.count dst.count p.count V (costSum t rows.explore)) (base + D) D := by
  let p := Tree.fork (stripe cols (fun k => stripe rows (fun a => v a k))) (stripe rows (fun _ => .atom false))
  let ri := stripe rows (stripe cols ∘ v)
  let ro := stripe rows (stripe dst ∘ w)
  let D := alignSpace S dst.count p.count ro.count
  have small : ri.count ≤ p.count := by
    simpa only [ri, p, stripe_simple, Function.comp_def, rowForest, blendInput, colForest, emptyRows] using row_bound v rows.explore cols.explore
  have b := (blend_bounded cols rows v env r base hr).mono le_rfl
    (show base + 300 * p.count ≤ base + D by dsimp only [D,alignSpace]; omega)
    (show 300 * p.count ≤ D - 1 by dsimp only [D,alignSpace]; omega)
  have m := map_bounded rows.explore (stripe cols ∘ v) (stripe dst ∘ w) op t S hc env r base hr
  dsimp only at m
  rw [← stripe_simple, ← stripe_simple] at m
  have m' := m.mono le_rfl (show base + mapSpace S ri ro ≤ base + D by dsimp only [D,alignSpace,mapSpace]; omega)
    (show mapSpace S ri ro ≤ D - 1 by dsimp only [D,alignSpace,mapSpace]; omega)
  have u := (transpose_bounded dst rows w env r base hr).mono le_rfl
    (show base + 253 * ro.count + 2 * dst.count + 10 ≤ base + D by dsimp only [D,alignSpace]; omega)
    (show 252 * ro.count + 10 ≤ D by dsimp only [D,alignSpace]; omega)
  have room : D - 1 + 1 ≤ D := by dsimp only [D,alignSpace]; omega
  apply (b.join (m'.join u room) room).mono _ le_rfl le_rfl
  dsimp only [alignClock]
  omega

/-- An ordinary nonempty column bank constructs the scaffold before the aligned call. -/
theorem aligned_bounded {K L A : Type} [DecidableEq K] [DecidableEq L] (cols : Series K) (dst : Series L)
    (rows : Series A) (k : K) (v : A → K → Tree) (w : A → L → Tree) (op : Cmd) (t : A → ℕ) (S : ℕ)
    (hc : ∀ a env r base, DeckCap base r →
      BoundedFits env op (pile 0 (stripe cols (v a)) r) (pile 0 (stripe dst (w a)) r)
        (t a) (base + S) S) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let bank := stripe cols (fun k => stripe rows (fun a => v a k))
    let p := Tree.fork bank (stripe rows (fun _ => .atom false))
    let out := stripe dst (fun l => stripe rows (fun a => w a l))
    let V := (stripe rows (stripe dst ∘ w)).count
    let D := alignSpace S dst.count p.count V + 432 * bank.count + 12
    BoundedFits env (alignedCommand (cols.explore.idxOf k) dst op) (pile 0 bank r) (pile 0 out r)
      (430 * bank.count + 12 + alignClock cols.count dst.count p.count V (costSum t rows.explore))
      (base + D) D := by
  let bank := stripe cols (fun k => stripe rows (fun a => v a k))
  let p := Tree.fork bank (stripe rows (fun _ => .atom false))
  let V := (stripe rows (stripe dst ∘ w)).count
  let d := alignSpace S dst.count p.count V
  let D := d + 432 * bank.count + 12
  have sf := scaffold_fits cols rows v k env r
  have one := BoundedFits.of_fits sf (cap := base + D) (depth := D - 1)
    (fun i => by have b := hr.pile 0 bank i; change (letters (pile 0 bank r) i).length + (430 * bank.count + 10) ≤ _; dsimp only [D]; omega)
    (by change 430 * bank.count + 10 ≤ _; dsimp only [D]; omega)
  have run := (alignedCore_bounded cols dst rows v w op t S hc env r base hr).mono le_rfl
    (show base + d ≤ base + D by dsimp only [D]; omega) (show d ≤ D by dsimp only [D]; omega)
  apply (one.join run (by dsimp only [D]; omega)).mono _ le_rfl le_rfl
  omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
