import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTriple
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisitTeams
import OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide
import OAI.Computability.BorderVNP.CubeTeamOwnedRun

/-! # Complete chronological owned-vertex triple column

The prefix ends at precisely the physical cursor used by the native owned-group
program. A strict role appends its dense selected records, a diagonal role
preserves the existing column, and a foreign row performs no writes. Publication
of the resulting count preserves every completed record.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA
open DiagonalTallyPacketEmit (Visit)
open scoped Classical

variable {w n d blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}

/-- Emitted vertices from the first `q` positions of the native square-table loop. -/
noncomputable def visited (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → ℕ) (team q : ℕ) :=
  ((List.finRange (d*d)).take q).flatMap (CubeVisits.teamRow axis blocks owner team)

private theorem prefix_step (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → ℕ) (team : ℕ) (q : Fin (d*d)) :
    visited axis blocks owner team (q.val+1) = visited axis blocks owner team q.val ++ CubeVisits.teamRow axis blocks owner team q := by
  unfold visited
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using q.isLt)]
  simp only [List.flatMap_append,List.getElem_finRange,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

private theorem length_row (axis : Fin (n+1)) (blocks : ℕ) (i j : Fin d) :
    (CubeVisits.orderedRow axis blocks i j).length = if i=j then 0 else strictVertices n d blocks := by
  rcases lt_trichotomy i j with lo | rfl | hi
  · simp only [CubeVisits.orderedRow,dite_eq_left lo,ite_eq_right lo.ne,CubeVisits.row,List.length_ofFn]; rfl
  · simp only [CubeVisits.orderedRow,dite_eq_right (lt_irrefl i),List.length_nil,ite_true]
  · simp only [CubeVisits.orderedRow,dite_eq_right hi.not_gt,dite_eq_left hi,ite_eq_right hi.ne',CubeVisits.row,List.length_ofFn]; rfl

/-- The physical counter's prefix size is the actual number of entries in the
semantically ordered team directory, including both roles of a co-located pair. -/
theorem prefix_length (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin l.d → ℕ) (q : ℕ) (bound : q ≤ l.d*l.d) :
    (visited axis blocks owner l.teamID q).length = vertexPrefix l (wordOwner owner) n blocks q := by
  induction q with
  | zero => simp [visited,vertexPrefix]
  | succ q ih =>
    let k : Fin (l.d*l.d) := ⟨q,bound⟩
    let p := pairAt l.d k
    rw [prefix_step axis blocks owner l.teamID k,List.length_append,ih (by omega)]
    have hx : wordOwner owner (q/l.d) = owner p.1 := by
      have lo : q/l.d < l.d := p.1.isLt
      simp only [wordOwner,lo,dite_true]; rfl
    have eq : q/l.d = q%l.d ↔ p.1=p.2 := by
      change p.1.val = p.2.val ↔ p.1 = p.2
      exact Fin.val_inj
    simp only [vertexPrefix,Finset.sum_range_succ,hx]
    change _ + (if owner p.1=l.teamID then CubeVisits.orderedRow axis blocks p.1 p.2 else []).length = _
    by_cases o : owner p.1=l.teamID <;> by_cases same : p.1=p.2 <;>
      simp [o,same,length_row,eq] <;> simp [CubeVisits.orderedRow]

variable (A : Data n l.d blocks b h K s)

local notation "reading" => visit A.packetBase (bankWidth n b h K s) A.select A.demand A.supply

/-- The physical triplets for all already visited owned vertices are resident
at the actual consecutive addresses of the team's output column. -/
def Past (owner : Fin l.d → ℕ) (base q : ℕ) (mem : Memory w) : Prop :=
  Stored (readings mem) base ((visited A.axis blocks owner l.teamID q).map reading)

theorem past_zero (owner : Fin l.d → ℕ) (base : ℕ) (mem : Memory w) : Past (l := l) A owner base 0 mem := by
  intro i
  exact Fin.elim0 (by simpa only [visited,List.take_zero,List.flatMap_nil,List.map_nil,List.length_nil] using i)

variable {A} {owner : Fin l.d → ℕ} {base : ℕ} {m mt : Memory w}

/-- The excluded foreign row contributes no slots. -/
theorem Past.skip (q : Fin (l.d*l.d)) (old : Past (l := l) A owner base q.val m)
    (miss : owner (pairAt l.d q).1 ≠ l.teamID) : Past (l := l) A owner base (q.val+1) m := by
  simpa only [Past,prefix_step,CubeVisits.teamRow,ite_eq_right miss,List.append_nil] using old

/-- An owned native role appends the physical column for its ordered row. -/
theorem Past.extend (q : Fin (l.d*l.d)) (old : Past (l := l) A owner base q.val m)
    (keep : ∀ a, base ≤ a → a < base+3*vertexPrefix l (wordOwner owner) n blocks q.val → mt a=m a)
    (appended : Stored (readings mt) (base+3*vertexPrefix l (wordOwner owner) n blocks q.val)
      ((CubeVisits.teamRow A.axis blocks owner l.teamID q).map reading)) : Past (l := l) A owner base (q.val+1) mt := by
  have count := prefix_length A.axis blocks owner q.val q.isLt.le
  unfold Past at old ⊢
  rw [prefix_step,List.map_append]
  apply Stored.append
  · apply old.preserve
    intro a lo hi
    simp only [List.length_map,count] at hi
    exact congrArg Fin.val (keep a lo hi)
  · simpa only [List.length_map,count] using appended

/-- A strict directed role appends the actual selected packet/vertex ranks
certified by `strict_stored`. -/
theorem Past.strict (q : Fin (l.d*l.d)) (old : Past (l := l) A owner base q.val m)
    (pair : Symbols l.d) (high : Bool) (atRole : pairAt l.d q = if high then pair.val.swap else pair.val)
    (own : owner (pairAt l.d q).1 = l.teamID)
    (keep : ∀ a, base ≤ a → a < base+3*vertexPrefix l (wordOwner owner) n blocks q.val → mt a=m a)
    (appended : Stored (readings mt) (base+3*vertexPrefix l (wordOwner owner) n blocks q.val)
      ((CubeVisits.row A.axis pair high blocks).map reading)) : Past (l := l) A owner base (q.val+1) mt := by
  apply old.extend q keep
  rw [CubeVisits.teamRow,ite_eq_left own,atRole]
  have lt := pair.property
  cases high
  · simpa only [Bool.false_eq_true,ite_false,CubeVisits.orderedRow,dite_eq_left lt] using appended
  · simpa only [ite_true,Prod.fst_swap,Prod.snd_swap,CubeVisits.orderedRow,dite_eq_right lt.not_gt,dite_eq_left lt] using appended

/-- A diagonal role keeps the already emitted records and appends no vertices. -/
theorem Past.diagonal (q : Fin (l.d*l.d)) (old : Past (l := l) A owner base q.val m)
    (same : (pairAt l.d q).1 = (pairAt l.d q).2)
    (keep : ∀ a, base ≤ a → a < base+3*vertexPrefix l (wordOwner owner) n blocks q.val → mt a=m a) :
    Past (l := l) A owner base (q.val+1) mt := by
  apply old.extend q keep
  intro i
  have empty : CubeVisits.teamRow A.axis blocks owner l.teamID q=[] := by
    dsimp only [CubeVisits.teamRow]
    split
    · simp only [CubeVisits.orderedRow,same,dite_eq_right (lt_irrefl _)]
    · rfl
  exact Fin.elim0 (by simpa only [empty,List.map_nil,List.length_nil] using i)

variable (A)

/-- After the true directory publication, frame word 46 is the length of the
owned semantic visit list, frame word 78 is its physical base, and every
published row has the exact three native words expected by the lookup. -/
theorem published (owner : Fin l.d → ℕ) (base : ℕ) (pre : Memory w) (r : Bank w)
    (past : Past (l := l) A owner base (l.d*l.d) pre)
    (ptr : readings pre (l.frame+78) = base) (frameBefore : l.frame+46 < base)
    (cursor : readings r 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (l.d*l.d)) :
    let xs := CubeVisits.teamList A.axis blocks owner l.teamID
    let mt := publishVertexCount pre l.frame (vertexPrefix l (wordOwner owner) n blocks (l.d*l.d))
    readings mt (l.frame+46)=xs.length ∧ readings mt (l.frame+78)=base ∧
      ∀ i : Fin xs.length, (reading (xs.get i)).tripleAt (readings mt) (base+3*i.val) := by
  intro xs mt
  have full : visited A.axis blocks owner l.teamID (l.d*l.d)=xs := by
    simp only [visited,List.take_of_length_le (show (List.finRange (l.d*l.d)).length ≤ l.d*l.d by simp),xs,CubeVisits.teamList]
  have count := prefix_length A.axis blocks owner (l.d*l.d) le_rfl
  rw [full] at count
  have size : readings r 7 < 2^w := (r 7).isLt
  have fit : vertexPrefix l (wordOwner owner) n blocks (l.d*l.d) < 2^w := by omega
  refine ⟨(publishVertexCount_here _ _ _ fit).trans count.symm,
    (congrArg Fin.val (publishVertexCount_other _ _ _ _ (by omega))).trans ptr,?_⟩
  unfold Past at past
  rw [full] at past
  have final := past.preserve (y := readings mt) (fun a lo _ =>
    congrArg Fin.val (publishVertexCount_other _ _ _ _ (by omega)))
  intro i
  simpa only [List.getElem_map,List.get_eq_getElem] using final ⟨i.val,by simpa only [List.length_map] using i.isLt⟩

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
