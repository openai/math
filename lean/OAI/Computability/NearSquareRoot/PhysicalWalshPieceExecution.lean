import OAI.Computability.NearSquareRoot.PhysicalWalshSweep
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshPadding

/-! # Rounded even-piece execution on the padded record stream

The semantic trajectory calls the recursive rounded program at every active
piece of the generated schedule. A representation guard is required at these
actual calls. The geometry supplies every fanout divisibility witness and
keeps the padded record count fixed across the whole sequence.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

/-- Transported width occurs only in the semantic family of grid records. -/
def castRow {w u : ℕ} (h : w=u) (x : ℕ → Dusk.Grain w) : ℕ → Dusk.Grain u := h ▸ x

/-- Record trajectory in physical address order after `n` complete even pieces. -/
def trajectory {w : ℕ} (l : List Shape) (x : ℕ → Dusk.Grain w) : ℕ → ℕ → Dusk.Grain w
  | 0 => x
  | n+1 =>
    let before := trajectory l x n
    if hj : n < l.length then
      let u := l[n]
      if eq : u.w = w then castRow eq (run hw p u (castRow eq.symm before)) else before
    else before

theorem trajectory_succ {w : ℕ} (l : List Shape) (j : Fin l.length) (h : (l.get j).w=w)
    (x : ℕ → Dusk.Grain w) :
    trajectory hw p l x (j.val+1) = castRow h (run hw p (l.get j)
      (castRow h.symm (trajectory hw p l x j))) := by
  simp only [trajectory,j.isLt,↓reduceDIte,List.get_eq_getElem] at h ⊢
  simp only [h,↓reduceDIte]

/-- One record stream beginning at ordinal zero, including every padded row. -/
def words {w : ℕ} (N : ℕ) (x : ℕ → Dusk.Grain w) := (List.range N).map (Dusk.mark ∘ x)

private theorem words_cast {u w : ℕ} (e : u=w) (N : ℕ) (x : ℕ → Dusk.Grain u) :
    words N (castRow e x) = words N x := by cases e; rfl

abbrev extent (A W k s : ℕ) := WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s)*2^s

theorem get_geometry {A : ℕ} (ha : 1 < A) (k s w : ℕ) (j : Fin (schedule A W hw k s w).length) :
    let u := (schedule A W hw k s w).get j
    u.w=w ∧ count A u=extent A W k s ∧ W^u.level ∣ u.pref := by
  intro u
  obtain ⟨d,t,he⟩ := (mem_schedule hw k s w u).mp (List.get_mem _ j)
  rw [← he]
  exact ⟨rfl,count_shape hw _ _ _ _ _ t.isLt,pref_dvd ha hw _ _ _ d _⟩

structure Root where
  k : ℕ
  s : ℕ
  w : ℕ
  row : ℕ → Dusk.Grain w

namespace Root

abbrev pieces (b : Root) := schedule (a+1) W hw b.k b.s b.w

abbrev stage (b : Root) (n : ℕ) := trajectory hw p (b.pieces (a:=a) hw) b.row n

def reached (ha : 1<a+1) (b : Root) (j : Fin (b.pieces (a:=a) hw).length) :
    Data ((b.pieces hw).get j) := castRow (get_geometry hw ha b.k b.s b.w j).1.symm (b.stage hw p j)

/-- Numeric condition on the actual rounded input to each scheduled piece. -/
def Feasible (ha : 1<a+1) (b : Root) := ∀ j : Fin (b.pieces (a:=a) hw).length,
  Good hw p ((b.pieces hw).get j) (b.reached hw p ha j)

abbrev size (b : Root) := extent (a+1) W b.k b.s

abbrev stream (b : Root) (n : ℕ) := words (b.size (a:=a) (W:=W)) (b.stage hw p n)

theorem stream_size (b : Root) (j : ℕ) :
    Code.size (b.stream hw p j) = (b.size (a:=a) (W:=W))*(4*(b.w+1)+4)+1 := by
  change Code.size ((List.range _).map (Dusk.mark ∘ b.stage hw p j)) = _
  rw [←List.map_map, Padding.marks_size,List.length_map,List.length_range]

end Root

/-- A fixed command on admissible individual root calls provides the raw
packet interface to the recursive piece evaluator. -/
abbrev Admissible := {v : Invocation hw p // count (a+1) v.shape ≤ 2^(v.shape.w+1)}

/-- Input and output packets at each position of the actual finite agenda.
Their shape and charged ordinal array agree with the admitted node interface. -/
theorem reachedPackets (ha : 1<a+1) (b : Root) (cap : b.size (a:=a) (W:=W) ≤ 2^(b.w+1))
    (fits : b.Feasible hw p ha) (j : Fin (b.pieces (a:=a) hw).length) :
    let u := (b.pieces (a:=a) hw).get j
    ∃ v : Admissible hw p, v.val.shape = u ∧
      buffer (a+1) v.val.shape v.val.row = send (Header.wire (a+1) u,b.stream hw p j) ∧
      buffer (a+1) v.val.shape (run hw p v.val.shape v.val.row) =
        send (Header.wire (a+1) u,b.stream hw p (j.val+1)) := by
  intro u
  have geom := get_geometry hw ha b.k b.s b.w j
  let v : Admissible hw p := ⟨⟨u,b.reached hw p ha j,geom.2.2,fits j⟩,by
    change count (a+1) u ≤ 2^(u.w+1)
    exact geom.2.1.trans_le (cap.trans_eq (congrArg (fun n => 2^(n+1)) geom.1.symm))⟩
  refine ⟨v,rfl,?_,?_⟩
  · change send (Header.wire (a+1) u,words (count (a+1) u) (castRow _ _)) = _
    rw [geom.2.1,words_cast]
  · change send (Header.wire (a+1) u, words (count (a+1) u) _) =
      send (Header.wire (a+1) u,words _ (trajectory hw p (b.pieces hw) b.row (j.val+1)))
    rw [trajectory_succ hw p (b.pieces hw) j geom.1,words_cast]
    exact congrArg (fun n => send (Header.wire (a+1) u,words n
      (run hw p u (b.reached hw p ha j)))) geom.2.1

/-- One fixed program generates the piece list and executes the full rounded
trajectory. Its clock counts each recursion level with its exact base digit. -/
theorem roundedSweep {I : Type} (ha : 1<a+1) (b : I → Root)
    (capacity : ∀ i,(b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1))
    (fits : ∀ i,(b i).Feasible hw p ha) (T S : Shape → ℕ)
    (raw : BoundedTask (fun v : Admissible hw p => T v.val.shape) (fun v => S v.val.shape)
      (fun v => buffer (a+1) v.val.shape v.val.row)
      (fun v => buffer (a+1) v.val.shape (run hw p v.val.shape v.val.row)))
    (clockAt : I → ℕ → ℕ) (arena : I → ℕ)
    (times : ∀ i (j : Fin ((b i).pieces (a:=a) hw).length), T (((b i).pieces hw).get j) ≤
      clockAt i (((b i).pieces hw).get j).level)
    (spaces : ∀ i (j : Fin ((b i).pieces (a:=a) hw).length), S (((b i).pieces hw).get j) ≤ arena i)
    (vol : ∀ i, (b i).size (a:=a) (W:=W)*(4*((b i).w+1)+4)+1 ≤ arena i) :
    ∃ d C : ℕ,
      let G i := C*((b i).k+(b i).s+(b i).w+1)^d+arena i
      let time i := 2*(G i+1) + ∑ j : Fin (walshPieceDigits (a+1) (b i).s).length,
        (walshPieceDigits (a+1) (b i).s).get j * (clockAt i j+G i+1)
      BoundedTask time G (fun i => send (((tally (b i).k,tally (b i).s),tally ((b i).w+1)),
          words ((b i).size (a:=a) (W:=W)) (b i).row))
        (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) := by
  let L (i : I) := (b i).pieces (a:=a) hw
  let X := (i : I) × Fin (L i).length
  have packet (z : X) := reachedPackets hw p ha (b z.1) (capacity _) (fits _) z.2
  let inv (z : X) := (packet z).choose
  have time (z : X) := (times z.1 z.2)
  have space (z : X) := (spaces z.1 z.2)
  have localRun := (raw.on inv).mono (fun z => ((congrArg T (packet z).choose_spec.1).trans_le (time z)))
    (fun z => ((congrArg S (packet z).choose_spec.1).trans_le (space z)))
  apply generatedSweep ha hw (fun i => (b i).k) (fun i => (b i).s) (fun i => (b i).w)
    (fun i => (b i).stream hw p) clockAt arena
  · intro i j _; exact ((b i).stream_size hw p j).le.trans (vol i)
  · exact localRun.conform (fun _ => rfl) (fun _ => rfl) (fun z => (packet z).choose_spec.2.1)
      (fun z => (packet z).choose_spec.2.2)

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
