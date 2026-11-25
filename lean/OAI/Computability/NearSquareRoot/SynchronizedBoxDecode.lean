import OAI.Computability.NearSquareRoot.SynchronizedBoxRow
import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanDepth
import OAI.Computability.NearSquareRoot.SynchronizedBoxWord

/-! # Exact semantics of the full finite-tape box program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code Matrix SynchronizedBlocks SynchronizedLayers.ScheduleProgram
  SynchronizedPadding ResidueFourier

noncomputable section

variable {k : ℕ} {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]
  (layout : BoxLayout b)

private theorem adequate_spectators {L : ℕ} (h : BoxShape.Valid k L b)
    (j : Fin (b.length/4)) (i : Fin (count j)) :
    8 ≤ Fintype.card (Spectators (axisMod b j) (axisPad b j) i) := by
  classical
  let w := fun t : Fin b.length => (b.get t).1
  calc
    8 ≤ ∏ t ∈ Finset.univ.erase i, 2 ^ w (axis j t) :=
      spectatorFibers_ge_eight w (fun t => (h.axisBounds _ (List.get_mem b t)).1) j i
    _ = Fintype.card (Spectators (axisMod b j) (axisPad b j) i) := by
      rw [Finset.prod_subtype (Finset.univ.erase i) (p := fun t => t ≠ i) (F := inferInstance)
        (by simp) (fun t => 2 ^ w (axis j t))]
      have shape (t : Fin (count j)) : axisMod b j t + axisPad b j t = 2 ^ w (axis j t) :=
        Nat.add_sub_of_le (h.axisBounds _ (List.get_mem b (axis j t))).2.2.2
      simp [Spectators, BlockAxis, Fintype.card_pi, shape]

private theorem local_decode {L : ℕ} (h : BoxShape.Valid k L b)
    (j : Fin (b.length/4)) :
    let w := localSlots (block (List.ofFn fun i => tally (expAt b j i)))
    (w.map (fun r => (boxSlot layout j r).matrix (layout.bits j))).prod =
        tensorMatrix (fun i => axisPadding (b := Fin (axisPad b j i)) (axisMatrix (axisMod b j i))) ∧
      ∀ r ∈ w, (boxSlot layout j r).kind = slotKind r :=
  localSlots_correct _ _ _ (layout.spectator j) (fun _ => active_bound _)
    (fun _ => (doubled_pad_lt (NeZero.pos _)).le) (layout.bits j) (even_card (layout.bits j))
    (fun _ => paddedLog_covers _) (adequate_spectators h j)

/-- Each live emitted block descriptor decodes to the kind given by its tag. -/
theorem boxSlot_kind_of_mem {L : ℕ} (h : BoxShape.Valid k L b) (j : Fin (b.length/4))
    {z : SlotDescriptor} (hz : z ∈ localSlots (block (List.ofFn fun i => tally (expAt b j i)))) :
    (boxSlot layout j z).kind = slotKind z := (local_decode layout h j).2 z hz

private theorem reverse_rows {X A : Type} [Fintype A] [DecidableEq A]
    (f : X → Matrix A A ℂ) (w : List X) :
    (w.reverse.map (fun x => (f x)ᴴ)).prod = (w.map f).prodᴴ := by
  induction w with
  | nil => simp
  | cons x w ih => simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, conjTranspose_mul, ih]

private theorem orientRows_member {X : Type} (dir : Bool) (rows : List X) (r : Bool × X)
    (hr : r ∈ orientRows (dir,rows)) : r.2 ∈ rows := by
  cases dir <;> simp [orientRows, polyPush] at hr <;> obtain ⟨x,h,rfl⟩ := hr <;> exact h

variable [∀ i, NeZero (BoxFin.modulus (CoprimeBox.box k) i)]

/-- Decoding the forward rows in grouped physical coordinates gives precisely the
normalized padded Fourier tensor. -/
theorem boxPlan_correct (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (hd : 4 ≤ (CoprimeBox.box k).length) (layout : BoxLayout (CoprimeBox.box k)) :
    let eval := fun j x => (boxSlot layout j x).matrix (layout.bits j)
    let e := regroup hd (BoxAxis (CoprimeBox.box k))
    let rows := boxPlan (tally k)
    (reindexRingEquiv ℂ e.symm) ((rows.map (rowMatrix eval)).prod) = paddedFourier (CoprimeBox.box k) ∧
      ∀ r ∈ rows, GlobalStage layout.bits (rowMatrix eval r) := by
  let b := CoprimeBox.box k
  let w := fun j : Fin (b.length/4) => localSlots (block (List.ofFn fun i => tally (expAt b j i)))
  let eval := fun (j : Fin (b.length/4)) x => (boxSlot layout j x).matrix (layout.bits j)
  let reg := regroup hd (BoxAxis b)
  let relabel := reindexRingEquiv ℂ reg.symm
  have hw : boxPlan (tally k) = plan slotKind (List.ofFn w,tally (boxDepth k)) :=
    boxPlan_eq k
  obtain ⟨hp,hs,_⟩ := plan_correct slotKind layout.bits eval w (local_length_le h)
    (fun j x hx => ⟨boxSlot layout j x, (local_decode layout h j).2 x hx, rfl⟩)
  rw [← hw] at hp hs
  have matrix : ((boxPlan (tally k)).map (rowMatrix eval)).prod =
      tensorMatrix (fun j : Fin (b.length/4) => tensorMatrix (fun i =>
        axisPadding (b := Fin (axisPad b j i)) (axisMatrix (axisMod b j i)))) := by
    rw [hp]
    exact congrArg tensorMatrix (funext fun j => (local_decode layout h j).1)
  have hf : relabel (((boxPlan (tally k)).map (rowMatrix eval)).prod) = paddedFourier b := by
    rw [matrix]
    exact regroup_tensor hd (fun i : Fin b.length => axisPadding (b := Fin (BoxFin.padding b i))
      (axisMatrix (BoxFin.modulus b i)))
  exact ⟨hf, hs⟩

private theorem orient_box_rows {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]
    (hd : 4 ≤ b.length) (layout : BoxLayout b) (rows : List (Row SlotDescriptor)) (dir : Bool) :
    let eval := fun j x => (boxSlot layout j x).matrix (layout.bits j)
    let reg := regroup hd (BoxAxis b)
    let U := (reindexRingEquiv ℂ reg.symm) ((rows.map (rowMatrix eval)).prod)
    ((orientRows (dir,rows)).map (boxRow layout hd)).prod = (if dir then Uᴴ else U) := by
  let f := rowMatrix (fun j x => (boxSlot layout j x).matrix (layout.bits j))
  let reg := regroup hd (BoxAxis b)
  let relabel := reindexRingEquiv ℂ reg.symm
  cases dir
  · change (((rows.map (fun x => (false,x))).map (boxRow layout hd)).prod) = relabel ((rows.map f).prod)
    rw [map_list_prod, List.map_map, List.map_map]
    rfl
  · change (((rows.reverse.map (fun x => (true,x))).map (boxRow layout hd)).prod) =
        (((rows.map f).prod).submatrix reg reg)ᴴ
    rw [conjTranspose_submatrix, ← reverse_rows]
    change _ = relabel ((rows.reverse.map fun x => (f x)ᴴ).prod)
    rw [map_list_prod, List.map_map, List.map_map]
    rfl

private theorem orient_box_stages {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]
    (hd : 4 ≤ b.length) (layout : BoxLayout b) (rows : List (Row SlotDescriptor)) (dir : Bool)
    (hs : ∀ r ∈ rows, GlobalStage layout.bits
      (rowMatrix (fun j x => (boxSlot layout j x).matrix (layout.bits j)) r)) :
    ∀ r ∈ orientRows (dir, rows), BoxStage hd layout.bits (boxRow layout hd r) := by
  rintro ⟨d,s⟩ hmem
  have hm := hs s (orientRows_member dir rows (d,s) hmem)
  cases d
  · exact ⟨_, hm, rfl⟩
  · exact ⟨_, hm.adjoint, rfl⟩

/-- Both directed products from the machine's tape equal the normalized padded
Fourier transform. Every generated row decodes to an allowed global stage. -/
theorem directedPlan_correct (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (hd : 4 ≤ (CoprimeBox.box k).length) (layout : BoxLayout (CoprimeBox.box k)) (dir : Bool) :
    let rows := directedPlan (dir,tally k)
    (rows.map (boxRow layout hd)).prod =
        (if dir then (paddedFourier (CoprimeBox.box k))ᴴ else paddedFourier (CoprimeBox.box k)) ∧
      (∀ r ∈ rows, BoxStage hd layout.bits (boxRow layout hd r)) ∧ rows.length = 3 * boxDepth k := by
  obtain ⟨hp,hs⟩ := boxPlan_correct h hd layout
  refine ⟨?_, orient_box_stages hd layout (boxPlan (tally k)) dir hs, directedPlan_length dir k⟩
  rw [directedPlan, orient_box_rows, hp]

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
