import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reading the outputs of disjoint chronological scans -/

namespace Hierarchy.ProtocolRAM.Calendar.FeedLayout
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical
variable {w : ℕ}

private theorem memory_frame (xs : List Pass) (mem : Memory w) (u : ℕ)
    (untouched : ∀ p∈xs,u<p.out ∨ p.out+p.rows≤u) : result xs mem u=mem u := by
  induction xs generalizing mem with
  | nil => rfl
  | cons p ps ih =>
    change result ps (p.apply mem) u=_
    rw [ih (p.apply mem) (fun s hs=>untouched s (List.mem_cons_of_mem _ hs))]
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ mem u (untouched p (by simp))

/-- Reading a word produced by a chronological list of disjoint physical scans. -/
theorem scheduled_read (ps : List Pass) (mem : Memory w) (p : Pass) (hp : p∈ps)
    (i : Fin p.rows) (cut : ℕ) (inputs : p.term.Fits w cut) (fresh : ∀ s∈ps,cut ≤ s.out)
    (disjoint : ps.Pairwise fun a b=>a.out+a.rows ≤ b.out ∨ b.out+b.rows ≤ a.out) :
    result ps mem (p.out+i.val)=p.term.eval mem (i.val:Word w) := by
  obtain ⟨xs,ys,split⟩ := List.append_of_mem hp
  rw [split] at disjoint ⊢
  rw [result_append]
  change result ys (p.apply (result xs mem)) (p.out+i.val)=_
  rw [memory_frame]
  · exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (eval_below _ _ mem _ inputs (fun u hu=>
      result_below xs mem u fun s hs=>hu.trans_le (fresh s (split ▸ List.mem_append_left _ hs))))
  · intro s hs
    have sep := (List.pairwise_cons.mp (List.pairwise_append.mp disjoint).2.1).1 s hs
    have hi := i.isLt
    omega

end Hierarchy.ProtocolRAM.Calendar.FeedLayout

end OAI
