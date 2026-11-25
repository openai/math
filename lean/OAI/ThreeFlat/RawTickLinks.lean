import OAI.ThreeFlat.RawTickSocketOrder
import OAI.ThreeFlat.RawTickOrderedScan

namespace OAI
/-! # Correctness of the streamed predecessor and destination arrays -/

namespace ThreeFlat.RawTick

open Collapse.TickLinkScan
noncomputable section
variable {F : Type*} {p : ℕ} (N : BitNetwork F p)
local notation "S" => sources N.internal p
local notation "K" => sockets N.cells

theorem trunk_live (s : N.Source) (j : Fin (N.arity s+1)) :
    (edgeIndex N (.inl ⟨s,j⟩)).val =
      last S (source N) (stop K (occurrence N s) j) (sourceIndex s).val := by
  rw [last_at_stop (source N) (occurrence N s) (occurrence_strictMono N s)
    (occurrence_lt N s) (fun _ => occurrence_iff N s)]
  induction j using Fin.cases with
  | zero => exact edge_root N s
  | succ j => exact edge_middle N s j

theorem prev_occurrence (s : N.Source) (i : Fin (N.arity s)) :
    prev S (source N) (occurrence N s i) = (edgeIndex N (.inl ⟨s,i.castSucc⟩)).val := by
  unfold prev
  have h := source_at N (N.socketAt s i)
  rw [N.address_socketAt] at h
  rw [show source N (occurrence N s i) = (sourceIndex s).val from h,trunk_live]
  simp [stop]

theorem last_source (s : N.Source) :
    last S (source N) K (sourceIndex s).val = (edgeIndex N (.inl ⟨s,Fin.last (N.arity s)⟩)).val := by
  rw [trunk_live]
  simp [stop]

/-- The tail sweep gives a destination to the final live trunk of every source,
including an unused hidden bit or an unattached input value. -/
theorem trunk_dest (initial : ℕ → ℕ) (s : N.Source) (j : Fin (N.arity s+1)) :
    dest S (source N) N.cells K initial (edgeIndex N (.inl ⟨s,j⟩)).val =
      (siteIndex N (N.copyDst (.inl ⟨s,j⟩))).val := by
  induction j using Fin.lastCases with
  | last =>
    rw [← last_source,dest_last _ _ _ (sourceIndex s).isLt]
    change tailSite _ _ _ _ = (siteIndex N (.inr ⟨s,(Fin.last (N.arity s)).succ⟩)).val
    rw [site_tail]
    unfold tailSite
    omega
  | cast i =>
    rw [← prev_occurrence,dest_prev _ _ _ (source_lt N) (occurrence_lt N s i)]
    change middleSite _ _ _ = (siteIndex N (.inr ⟨s,i.castSucc.succ⟩)).val
    rw [site_middle]
    unfold middleSite occurrence
    omega

/-- Both endpoints of a spoke are arithmetic. Only the trunk destination needs a table. -/
def srcSite (cells sourceCount socketCount edge : ℕ) :=
  if edge<sourceCount+socketCount then cells+edge else cells+(edge-socketCount)

def dstSite (sourceCount socketCount : ℕ) (trunk : ℕ → ℕ) (edge : ℕ) :=
  if edge<sourceCount+socketCount then trunk edge else (edge-(sourceCount+socketCount))/3

theorem srcSite_correct (e : N.CopyEdge) :
    srcSite N.cells S K (edgeIndex N e).val=(siteIndex N (N.copySrc e)).val := by
  rcases e with ⟨s,j⟩ | u
  · induction j using Fin.cases with
    | zero =>
      rw [edge_root]
      change srcSite _ _ _ _ = (siteIndex N (.inr ⟨s,0⟩)).val
      rw [site_root]
      have := (sourceIndex s).isLt
      unfold srcSite
      split <;> omega
    | succ j =>
      rw [edge_middle]
      change srcSite _ _ _ _ = (siteIndex N (.inr ⟨s,j.castSucc.succ⟩)).val
      rw [site_middle]
      have bound := occurrence_lt N s j
      unfold occurrence at bound
      unfold srcSite
      split <;> omega
  · rw [edge_spoke]
    change srcSite _ _ _ _ = (siteIndex N (.inr ⟨N.address u,(N.socketOffset u).castSucc.succ⟩)).val
    rw [site_middle,N.socketAt_offset]
    unfold srcSite
    split <;> omega

theorem dstSite_correct (initial : ℕ → ℕ) (e : N.CopyEdge) :
    dstSite S K (dest S (source N) N.cells K initial) (edgeIndex N e).val =
      (siteIndex N (N.copyDst e)).val := by
  rcases e with ⟨s,j⟩ | u
  · have bound : (edgeIndex N (.inl ⟨s,j⟩)).val < S+K := by
      induction j using Fin.cases with
      | zero => rw [edge_root]; have := (sourceIndex s).isLt; omega
      | succ j => rw [edge_middle]; exact Nat.add_lt_add_left (occurrence_lt N s j) _
    rw [dstSite,ite_eq_left bound,trunk_dest]
  · rw [edge_spoke]
    change dstSite _ _ _ _ = (siteIndex N (.inl u.1)).val
    rw [site_cell,dstSite,ite_eq_right (by omega),ordinal_val]
    have := u.2.isLt
    omega

end
end ThreeFlat.RawTick

end OAI
