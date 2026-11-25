import OAI.Hierarchy.ProbeStagePhase
import OAI.Hierarchy.ProbeStageExport

namespace OAI
/-! # Running the complete subdivision from the input permutation -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

private theorem phase_order {h d k l : ℕ} (order : k≤l) :
    phase h d copies k ≤ phase h d copies l :=
  Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ order) _)

private theorem row_before {h d j : ℕ} (r : Fin (2^h)) (c : Fin 9) :
    output h d copies j+c.val*2^h+r.val<phase h d copies (j+1) := by
  have atEnd := output_end h d copies j
  have last : c.val*2^h+r.val < 9*2^h := (Nat.add_lt_add_left r.isLt _).trans_le (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ c.isLt)
  omega

structure After {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (input : Memory (wordBits h d copies)) (k : ℕ) : Prop where
  parent : ParentStored d π k (images h d input k)
  future : ∀ (j : Fin (rounds d)),k≤j.val → GeometryStored (h:=h) j (images h d input k) ∧
    allArrays h d _ j (images h d input k)
  rows : ∀ (j : Fin (rounds d)),j.val<k → ∀ (r : Fin (2^h)) (c : Fin 9),
    images h d input k (output h d copies j.val+c.val*2^h+r.val)=
      (rowWords (history h d π j.val).tiles (radix_pos h d) (assigned j π)
        (history h d π j.val).encode r c : Word _)
  scans : ∀ (j : Fin (rounds d)),j.val<k → ∀ r : Fin (2^h),
    rowScans h d j.val r.val (prior h d j.val (images h d input j.val) r.val)≤expectedScans h d π j.val r
  clears : ∀ (j : Fin (rounds d)),j.val<k → ∀ r : Fin (2^h),
    rowClears h d j.val r.val (prior h d j.val (images h d input j.val) r.val)≤expectedClears h d π j.val r
  above : ∀ a,heapEnd h d copies≤a → images h d input k a=input a

private theorem root_frame {h d w : ℕ} (m : Memory w) (a : ℕ) (lo : phase h d copies 0≤a) :
    result (rootPasses h) m a=m a := by
  have nr := height_extent h d
  simp only [phase,Nat.zero_mul,Nat.add_zero] at lo
  apply columns_frame
  right
  change 2^h+2*2^h≤a
  omega

theorem after_root {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (raw : Memory (wordBits h d copies))
    (read : ∀ r : Fin (2^h),raw r.val=((π r).val : Word _)) :
    After (d:=d) π (inputTape h d _ raw) 0 := by
  let input := inputTape h d _ raw
  obtain ⟨_,_,g,s,t⟩ := root_exec h d copies π input (fun r => (inputTape_root raw r.isLt).trans (read r))
  refine ⟨⟨g,s,t⟩,?_,?_,?_,?_,?_⟩
  · intro j _
    have start := phase_order (h:=h) (d:=d) (Nat.zero_le j.val)
    constructor
    · intro c i
      let x : GeometryCell h d := ⟨j,c,i⟩
      have low := start.trans ((Nat.le_add_right _ _).trans (geometry_interval x).1)
      exact (root_frame input _ low).trans (geometryStored_tape h d _ j raw c i)
    · intro c i hi
      let x : ArrayCell h d := ⟨j,c,⟨i,hi⟩⟩
      exact (root_frame input _ (start.trans x.low)).trans (inputTape_array raw x)
  · intros;omega
  · intros;omega
  · intros;omega
  · intro a high
    exact root_frame input a ((phase_order (Nat.zero_le (rounds d))).trans high)

theorem after_levels {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (wordBits h d copies)) (read : ∀ r : Fin (2^h),raw r.val=((π r).val : Word _))
    (visit : ∀ j,RowCorrect hd π j) : ∀ k≤rounds d,After (d:=d) π (inputTape h d _ raw) k := by
  let input := inputTape h d _ raw
  intro k
  induction k with
  | zero => intro _;exact after_root π raw read
  | succ k ih =>
    intro bound
    let j : Fin (rounds d) := ⟨k,by omega⟩
    have prev := ih (by omega)
    obtain ⟨fixed,fresh⟩ := prev.future j le_rfl
    have reached := phase_result hd π j (images h d input k) fixed prev.parent fresh (visit j)
    refine ⟨reached.child,?_,?_,?_,?_,?_⟩
    · intro future higher
      obtain ⟨geom,arrays⟩ := prev.future future (by omega)
      have begin_ := phase_order (h:=h) (d:=d) higher
      constructor
      · intro c i
        let x : GeometryCell h d := ⟨future,c,i⟩
        have low := begin_.trans ((Nat.le_add_right _ _).trans (geometry_interval x).1)
        exact (reached.frame _ (Or.inr low)).trans (geom c i)
      · intro c i hi
        let x : ArrayCell h d := ⟨future,c,⟨i,hi⟩⟩
        exact (reached.frame _ (Or.inr (begin_.trans x.low))).trans (arrays c i hi)
    · intro q limit r c
      by_cases active : q=j
      · subst q;exact reached.output r c
      · have old : q.val<k := by have ne : q.val≠k := fun e => active (Fin.ext e);omega
        exact (reached.frame _ (Or.inl ((row_before r c).trans_le (phase_order old)))).trans (prev.rows q old r c)
    · intro q limit r
      by_cases active : q=j
      · subst q;exact reached.scans r
      · have ne : q.val≠k := fun e => active (Fin.ext e)
        exact prev.scans q (by omega) r
    · intro q limit r
      by_cases active : q=j
      · subst q;exact reached.clears r
      · have ne : q.val≠k := fun e => active (Fin.ext e)
        exact prev.clears q (by omega) r
    · intro a high
      have lower : phase h d copies (k+1)≤a := (phase_in_heap bound).trans high
      exact (reached.frame _ (Or.inr lower)).trans (prev.above a high)

/-- A caller can preinstall any later sampler or circuit advice once, above
the last subdivision address. All its words survive the full execution. -/
theorem images_above {h d : ℕ} {π : Equiv.Perm (Fin (2^h))} (raw : Memory (wordBits h d copies))
    (complete : After (d:=d) π (inputTape h d _ raw) (rounds d)) {a : ℕ} (high : heapEnd h d copies≤a) :
    images h d (inputTape h d _ raw) (rounds d) a=raw a :=
  (complete.above a high).trans (inputTape_above raw high)

theorem native_linear_run {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (wordBits h d copies)) (read : ∀ r : Fin (2^h),raw r.val=((π r).val : Word _))
    (visit : ∀ j,RowCorrect hd π j) :
    let input := inputTape h d _ raw
    (subdivisionProgram h d).Exec input (images h d input (rounds d)) (subdivisionConstant d*2^h) ∧
      After (d:=d) π input (rounds d) := by
  let input := inputTape h d _ raw
  have end_ := after_levels hd π raw read visit (rounds d) le_rfl
  have limit := linear_of_readback hd π input (fun j => end_.scans j j.isLt) (fun j => end_.clears j j.isLt)
  refine ⟨?_,end_⟩
  exact Procedure.Spec.mono (subdivision_exec h d input) (fun _ h=>h) (fun _ _ h=>h) limit

end
end Hierarchy.ProbeStage.Native

end OAI
