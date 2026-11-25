import OAI.Computability.NearSquareRoot.InterchangeROMStageRows
import OAI.Computability.NearSquareRoot.InterchangeROMStageQuote

/-! # Physical execution of the numbered sparse movement banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM CommonRegisters Space

variable {g : Frame} (r : Realization g)

noncomputable def cells (n d : ℕ) : List (r.Boundary n × Fin d) :=
  (r.order n).explore.flatMap fun a => (List.finRange d).map (Prod.mk a)

private theorem rangeMap {A : Type} (d : ℕ) (f : ℕ → A) :
    (List.finRange d).map (fun i => f i.val) = (List.range d).map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem cells_map {A : Type} (n d : ℕ) (x : Role → ℕ → A) :
    (r.cells n d).map (fun z => x (r.code n z.1) z.2.val) = blocks (bank g n) d x := by
  rw [← r.order_tab n]
  simp only [Series.tab,blocks,cells,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro i _
  exact rangeMap _ _

theorem length_cells (n d : ℕ) : (r.cells n d).length = (bank g n).length*d := by
  simpa only [List.length_map,length_blocks] using
    congrArg List.length (r.cells_map n d (fun _ _ => ()))

/-- The real, fixed-register collection of one movement instruction per ground
row. Each child clock in the finite ledger enters with coefficient one. -/
theorem execute_route {n d : ℕ} {src : r.Boundary (n+1) → r.Boundary n}
    {mv : r.Boundary (n+1) → r.NativeMove} (ok : r.CorrectRoute n src mv)
    (impl : Frame.Move → Cmd) (hdr : Tree) (x y : Role → ℕ → Tree)
    (time : r.Boundary (n+1) × Fin d → ℕ) (S D : ℕ) (env : Env)
    (child : ∀ (b : r.Boundary (n+1)) (k : Fin d) rest base, DeckCap base rest →
      BoundedFits env (impl (r.operand (mv b))) (pile 0 (.fork hdr (x (r.code n (src b)) k.val)) rest)
        (pile 0 (y (r.code (n+1) b) k.val) rest) (time (b,k)) (base+S) D)
    (rest : Deck) (base : ℕ) (hbase : DeckCap base rest) :
    let v := packet hdr (blocks (bank g n) d x)
    let w := packet hdr (blocks (bank g (n+1)) d y)
    BoundedFits env (routeCommand impl (route g d n)) (pile 0 v rest) (pile 0 w rest)
      (((bank g (n+1)).length*d+2)*(160*(v.count+1)) + costSum time (r.cells (n+1) d))
      (base+170*(v.count+1)+w.count+S) (170*(v.count+1)+D) := by
  let roles := bank g n
  let xs := blocks roles d x
  let out := fun z : r.Boundary (n+1) × Fin d => y (r.code (n+1) z.1) z.2.val
  let sel := fun z : r.Boundary (n+1) × Fin d =>
    (roles.idxOf (r.code n (src z.1))*d+z.2.val,r.operand (mv z.1))
  have move : ∀ (z : r.Boundary (n+1) × Fin d) rr b, DeckCap b rr →
      BoundedFits env (impl (sel z).2) (pile 0 (.fork hdr (InterchangeROM.source xs (sel z).1)) rr)
        (pile 0 (out z) rr) (time z) (b+S) D := by
    rintro ⟨a,k⟩ rr b h
    simpa only [xs,roles,sel,out,source_blocks _ _ _ _ (r.code_mem n (src a)) _ k.isLt]
      using child a k rr b h
  have ix (z : r.Boundary (n+1) × Fin d) : (sel z).1 < xs.length := by
    change roles.idxOf (r.code n (src z.1))*d+z.2.val < (blocks roles d x).length
    rw [length_blocks]
    have lt := r.physRank_lt n (src z.1)
    have b := Nat.mul_le_mul_right d (Nat.succ_le_of_lt lt)
    rw [Nat.succ_mul] at b
    have hd := z.2.isLt
    dsimp only [roles]
    omega
  have run := route_bounded hdr xs (r.cells (n+1) d) sel impl out time S D env ix move rest base hbase
  have compiled : (r.cells (n+1) d).map sel = route g d n := by
    let key := fun v k => ((bank g n).idxOf (leg g n v).1*d+k,(leg g n v).2)
    have result := r.cells_map (n+1) d key
    have eq (z : r.Boundary (n+1) × Fin d) : key (r.code (n+1) z.1) z.2.val = sel z := by
      simp only [key,sel,roles,ok z.1]
    simp only [eq] at result
    apply result.trans
    apply List.flatMap_congr
    intro v _
    simp only [key]
  have output := congrArg (Task.forest id) (r.cells_map (n+1) d y)
  rw [Task.forest_map] at output
  change Task.forest out (r.cells (n+1) d) = _ at output
  rw [compiled,output,r.length_cells] at run
  exact run

end InterchangeROMStage.Frame.Realization

namespace InterchangeROMStage
open IntegerMultiplication IntegerMultiplication.Code Space InterchangeROM

/-- Sum of unscaled individual step clocks, with one join per instruction. -/
def traceClock (time : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 1
  | len+1 => time start + traceClock time (start+1) len + 2

/-- A list of raw operators is executable on a specified trajectory of packed
states. Only one extra return slot is used, independently of list length. -/
theorem execute_trace {T M : Type} (tab : T → Cmd) (op : M → Cmd) (env : Env)
    (state : ℕ → Tree) (time : ℕ → ℕ) (cap depth : ℕ) (ops : List (Instruction T M)) (start : ℕ)
    (last : (state (start+ops.length)).count ≤ cap)
    (step : ∀ i (hi : i < ops.length) r base, DeckCap base r →
      BoundedFits env (instruction tab op ops[i]) (pile 0 (state (start+i)) r)
        (pile 0 (state (start+i+1)) r) (time (start+i)) (base+cap) depth)
    (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (program tab op ops) (pile 0 (state start) r) (pile 0 (state (start+ops.length)) r)
      (traceClock time start ops.length) (base+cap) (depth+1) := by
  induction ops generalizing start with
  | nil =>
    exact BoundedFits.pass (fun j => by
      have hj := hr.pile 0 (state start) j
      simp only [List.length_nil,Nat.add_zero] at last ⊢
      omega)
  | cons a ops ih =>
    have first := step 0 (by simp) r base hr
    simp only [Nat.add_zero,List.getElem_cons_zero] at first
    have hend : start+1+ops.length = start+(a::ops).length := by simp; omega
    have tail := ih (start+1) (by rw [hend]; exact last) (by
      intro i hi d b hd
      rw [show start+1+i = start+(i+1) by omega]
      exact step (i+1) (by simpa) d b hd)
    rw [hend] at tail
    exact first.join tail (by omega)

end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
