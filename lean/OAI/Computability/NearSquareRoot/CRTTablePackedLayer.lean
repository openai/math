import OAI.Computability.NearSquareRoot.CRTTablePackedAddress
import OAI.Computability.NearSquareRoot.CRTTableSchedule
import OAI.Computability.NearSquareRoot.CRTTableWordPorts

/-! # Conjugating a whole padded CRT level to controlled permutations of words

Each target's port permutation is determined by the external coordinates.
Zeros in the target fields give one complete padded address representing
any such control setting. Correctness of the physical table on all ports
and correctness on the current address then identify the simultaneous action.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

variable {d : ℕ} (a w : Fin d → ℕ) [∀ i, NeZero (a i)] (hwidth : ∀ g, a g ≤ 2^w g)

abbrev AxisPadding (g : Fin d) := Fin (2^w g - a g)

/-- Canonical complete address with the supplied external setting. -/
noncomputable def representative (n : ℕ) (x : ExternalValues a w n) :
    CRT.Address a (AxisPadding a w) :=
  (packAddress a w hwidth n).symm (x, fun b => wordEquiv (w (targetAxis d n b)) 0)

theorem representative_external (n : ℕ) (x : ExternalValues a w n) (g : ExternalAxis d n) :
    representative a w hwidth n x g.val = x g := by
  exact congrArg (fun z : Packed a w n => z.1 g)
    ((packAddress a w hwidth n).apply_symm_apply (x, fun b => wordEquiv (w (targetAxis d n b)) 0))

/-- All left coordinates used to compute a node's offset are external. -/
theorem representative_offset (n : ℕ) (hn : n < Nat.clog 2 d) (j : LevelNode d n)
    (y : CRT.Address a (AxisPadding a w)) :
    let s := Stage.atLevel d n hn j
    CRT.mergeOffset (s.left a (AxisPadding a w))
        (representative a w hwidth n ((packAddress a w hwidth n y).1)) =
      CRT.mergeOffset (s.left a (AxisPadding a w)) y := by
  intro s
  apply CRT.mergeOffset_reads
  intro g hg
  have he := (external_iff_mem_left d n g).mpr ⟨j, List.mem_toFinset.mp hg⟩
  exact representative_external a w hwidth n _ ⟨g,he⟩

/-- The binary port permutation for one target of a level at one fixed
external setting. -/
noncomputable def blockPerm (n : ℕ) (hn : n < Nat.clog 2 d)
    (inv : Bool) (x : ExternalValues a w n) (b : TargetIndex d n) :
    Equiv.Perm (Benes.Word (w (targetAxis d n b))) :=
  let s := Stage.atLevel d n hn b.1
  let g := targetAxis d n b
  let δ := CRT.mergeOffset (s.left a (AxisPadding a w)) (representative a w hwidth n x) g
  let e := wordEquiv (w g)
  e.symm.trans ((portPerm (hwidth g) (bif inv then -δ else δ)).trans e)

theorem blockPerm_on (n : ℕ) (hn : n < Nat.clog 2 d) (inv : Bool)
    (y : CRT.Address a (AxisPadding a w)) (b : TargetIndex d n) :
    let s := Stage.atLevel d n hn b.1
    let g := targetAxis d n b
    let δ := CRT.mergeOffset (s.left a (AxisPadding a w)) y g
    let e := wordEquiv (w g)
    blockPerm a w hwidth n hn inv ((packAddress a w hwidth n y).1) b =
      e.symm.trans ((portPerm (hwidth g) (bif inv then -δ else δ)).trans e) := by
  dsimp only [blockPerm]
  rw [representative_offset a w hwidth n hn b.1 y]

omit hwidth in
private theorem row_external (n : ℕ) (hn : n < Nat.clog 2 d) (inv : Bool)
    (y : CRT.Address a (AxisPadding a w)) (g : ExternalAxis d n) :
    let row := Stage.layerPerm a (AxisPadding a w) (Stage.atDepth d n hn)
    ((bif inv then row.symm else row) y) g.val = y g.val := by
  intro row
  obtain ⟨j,hj⟩ := (external_iff_mem_left d n g.val).mp g.property
  let s := Stage.atLevel d n hn j
  have hleft : g.val ∈ (CRTTree.left s.node).toFinset := List.mem_toFinset.mpr hj
  have hright := Finset.disjoint_left.mp s.disjoint hleft
  have hnode : g.val ∈ s.node := List.mem_of_mem_take hj
  have hs : s ∈ Stage.atDepth d n hn := List.mem_map_of_mem (f := Stage.atLevel d n hn) (by simp)
  cases inv with
  | false =>
    change row y g.val = y g.val
    rw [Stage.layerPerm_on a _ _ (Stage.atDepth_disjoint n hn) s hs y _ hnode]
    exact ite_eq_right hright
  | true =>
    change row.symm y g.val = y g.val
    rw [Stage.layerPerm_symm_on a _ _ (Stage.atDepth_disjoint n hn) s hs y _ hnode]
    exact ite_eq_right hright

theorem packedLayer_apply (hdense : ∀ g, 2^w g ≤ 2*a g)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (inv : Bool) (y : CRT.Address a (AxisPadding a w)) :
    let row := Stage.layerPerm a (AxisPadding a w) (Stage.atDepth d n hn)
    packAddress a w hwidth n ((bif inv then row.symm else row) y) =
      Benes.controlledPerm (blockPerm a w hwidth n hn inv) (packAddress a w hwidth n y) := by
  intro row
  apply Prod.ext
  · exact funext fun g => row_external a w n hn inv y g
  · funext b
    let g := targetAxis d n b
    let s := Stage.atLevel d n hn b.1
    let z := (bif inv then row.symm else row) y
    let u := axisNumber (hwidth g) (y g)
    let δ := CRT.mergeOffset (s.left a (AxisPadding a w)) y g
    let π := portPerm (hwidth g) (bif inv then -δ else δ)
    let tabs := levelTables (levelQuery a w (fun _ => id) n y inv)
    have h₁ := levelTables_apply_row a w (fun _ => id) hwidth hdense hcop n hn b.1 y inv b.2
    have h₂ := (levelTables_portPerm a w (fun _ => id) hwidth hdense hcop n hn b.1 y inv b.2).2 u
    change tableEntry tabs b.1.val b.2.val (coordinate id (y g)) = coordinate id (z g) at h₁
    change tableEntry tabs b.1.val b.2.val u.val = (π u).val at h₂
    have hnum : axisNumber (hwidth g) (z g) = π u := by
      apply Fin.ext
      rw [axisNumber_val, ← h₁]
      simpa only [u, axisNumber_val] using h₂
    change wordEquiv (w g) (axisNumber (hwidth g) (z g)) =
      blockPerm a w hwidth n hn inv ((packAddress a w hwidth n y).1) b (wordEquiv (w g) u)
    rw [blockPerm_on a w hwidth n hn inv y b]
    change wordEquiv (w g) (axisNumber (hwidth g) (z g)) =
      wordEquiv (w g) (π ((wordEquiv (w g)).symm (wordEquiv (w g) u)))
    rw [Equiv.symm_apply_apply, hnum]

end CRTTable

end NearSquareRoot
end Computability
end OAI
