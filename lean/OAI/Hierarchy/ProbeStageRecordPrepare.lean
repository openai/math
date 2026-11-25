import OAI.Hierarchy.ProbeStageRecord

namespace OAI
/-! # The six physical directory lookups preceding the packed-word search -/

namespace Hierarchy.ProbeStage.Record
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

structure Load where
  dst : ℕ
  base : ℕ
  index : ℕ

/-- Exactly one indirect read of an immutable table of words. -/
def Load.expr (d : Load) : Write := ⟨d.dst,RankUpdate.directory d.base d.index⟩

def Load.addr {w : ℕ} (d : Load) (m : Memory w) := ((d.base:Word w)+m (d.index:Word w).val).val

def dirs (a : Advice) (r : Row) (s : Scratch) : List Load :=
 [⟨s.leftCount,a.leftCounts,r.leftID⟩, ⟨s.rightCount,a.rightCounts,r.rightID⟩,
  ⟨s.leftMask,a.leftMasks,r.leftID⟩,⟨s.rightMask,a.rightMasks,r.rightID⟩,
  ⟨s.wordOffset,a.wordOffsets,r.stringID⟩,⟨s.stringOffset,a.stringOffsets,r.stringID⟩]

theorem prepare_eq (a : Advice) (r : Row) (s : Scratch) : prepare a r s=(dirs a r s).map Load.expr := rfl

theorem writes_frame {w : ℕ} (xs : List Write) (m : Memory w) (x : ℕ) (fresh : ∀ z∈xs,x≠z.dst) :
    writes xs m x=m x := by
  induction xs generalizing m with
  | nil => rfl
  | cons z zs ih =>
    rw [writes,ih _ (fun d hd => fresh d (by simp [hd]))]
    exact Function.update_of_ne (fresh z (by simp)) _ _

def staticWrites {w : ℕ} (original : Memory w) : List Load → Memory w → Memory w
  | [],m => m
  | z::zs,m => staticWrites original zs (Function.update m z.dst (original (z.addr original)))

theorem freeze_dirs {w : ℕ} (xs : List Load) (m : Memory w)
    (apart : ∀ d∈xs, ∀ e∈xs, (d.index:Word w).val≠e.dst ∧ d.addr m≠e.dst) :
    writes (xs.map Load.expr) m=staticWrites m xs m := by
  have aux (ys : List Load) (mem : Memory w) (inside : ∀ d∈ys,d∈xs)
      (same : ∀ d∈xs, mem (d.index:Word w).val=m (d.index:Word w).val ∧ mem (d.addr m)=m (d.addr m)) :
      writes (ys.map Load.expr) mem=staticWrites m ys mem := by
    induction ys generalizing mem with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.map_cons,writes,staticWrites]
      have hd := inside d (by simp)
      have read : RankUpdate.assign d.dst (RankUpdate.directory d.base d.index) mem=
          Function.update mem d.dst (m (d.addr m)) := by
        apply congrArg (Function.update mem d.dst)
        change mem (d.addr mem)=m (d.addr m)
        have key : d.addr mem=d.addr m := by unfold Load.addr; rw [(same d hd).1]
        rw [key]
        exact (same d hd).2
      change writes (ds.map Load.expr) (RankUpdate.assign d.dst (RankUpdate.directory d.base d.index) mem)=_
      rw [read]
      apply ih _ (fun e he=>inside e (by simp [he]))
      intro e he
      have h := apart e he d hd
      simpa only [Function.update_of_ne h.1,Function.update_of_ne h.2] using same e he
  exact aux xs m (fun _=>id) (fun _ _=>⟨rfl,rfl⟩)

theorem static_frame {w : ℕ} (m m' : Memory w) (xs : List Load) (x : ℕ) (other : ∀ e∈xs,x≠e.dst) :
    staticWrites m xs m' x=m' x := by
  induction xs generalizing m' with
  | nil => rfl
  | cons e es ih =>
    rw [staticWrites,ih _ (fun d hd=>other d (by simp [hd]))]
    exact Function.update_of_ne (other e (by simp)) _ _

theorem static_at {w : ℕ} (m m' : Memory w) (xs : List Load) (unique : (xs.map Load.dst).Nodup)
    (z : Load) (hz : z∈xs) : staticWrites m xs m' z.dst=m (z.addr m) := by
  induction xs generalizing m' with
  | nil => simp at hz
  | cons d ds ih =>
    simp only [List.map_cons,List.nodup_cons,List.mem_map] at unique
    rcases List.mem_cons.mp hz with eqn|later
    · subst z
      rw [staticWrites,static_frame,Function.update_self]
      intro e he eqn
      exact unique.1 ⟨e,he,eqn.symm⟩
    · exact ih _ unique.2 later

theorem prepared_lookup {w : ℕ} (a : Advice) (r : Row) (s : Scratch) (m : Memory w)
    (apr : ∀ d∈dirs a r s, ∀ e∈dirs a r s,(d.index:Word w).val≠e.dst ∧ d.addr m≠e.dst)
    (uniq : ((dirs a r s).map Load.dst).Nodup) (z : Load) (member : z∈dirs a r s) :
    writes (prepare a r s) m z.dst=m (z.addr m) := by
  rw [prepare_eq,freeze_dirs _ _ apr]
  exact static_at _ _ _ uniq _ member

end Hierarchy.ProbeStage.Record

end OAI
