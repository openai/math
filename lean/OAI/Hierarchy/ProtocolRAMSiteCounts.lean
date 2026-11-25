import OAI.Hierarchy.ProtocolRAMScalarCounts
import OAI.Computability.BorderVNP.FragmentBucketOrder
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # The actual cardinalities used to build the stable endpoint-site directory -/

namespace Hierarchy.ProtocolRAMSiteCounts

open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.BorderVNP.FragmentBucket
open scoped Fin.CommRing

variable {w n sites : ℕ}

def siteAt (site : Fin n→Fin sites) (t : ℕ) : ℕ :=
  if h : t < n then (site ⟨t,h⟩).val else 0

def program (w src base n sites : ℕ) : Procedure w :=
  (ProtocolRAMScalarCounts.clear w base sites).seq (ProtocolRAMScalarCounts.counting w src base n)

def image (base : ℕ) (site : Fin n→Fin sites) (m : Memory w) : Memory w :=
  ProtocolRAMScalarCounts.accumulated base (siteAt site) (fillSegment base sites (fun _ => 0) m) n

private theorem prior_eq (site : Fin n→Fin sites) (s : Fin sites) (t : ℕ) (ht : t ≤ n) :
    (∑ j ∈ Finset.range t, if siteAt site j=s.val then 1 else 0) = prior site t s := by
  induction t with
  | zero => simp [prior_zero]
  | succ t ih =>
    have live : t < n := by omega
    let i : Fin n := ⟨t,live⟩
    have step := prior_step site i s
    change prior site (t+1) s = prior site t s + if site i=s then 1 else 0 at step
    rw [Finset.sum_range_succ,ih (by omega),step]
    simp only [siteAt,dite_eq_left live,Fin.val_inj,i]

theorem bin (base : ℕ) (site : Fin n→Fin sites) (m : Memory w) (s : Fin sites) :
    image base site m (base+s.val)=(count site s : Word w) := by
  unfold image
  rw [ProtocolRAMScalarCounts.bin,prior_eq site s n le_rfl,prior_end]
  simp [fillSegment,show base+s.val < base+sites by have := s.isLt; omega]

theorem frame (base : ℕ) (site : Fin n→Fin sites) (m : Memory w) (a : ℕ)
    (away : a < base ∨ base+sites ≤ a) : image base site m a=m a := by
  let blank := fillSegment base sites (fun _ => (0:Word w)) m
  have acc (t : ℕ) (ht : t ≤ n) :
      ProtocolRAMScalarCounts.accumulated base (siteAt site) blank t a=blank a := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have live : t < n := by omega
      have small : siteAt site t < sites := by simp [siteAt,live]
      simpa [ProtocolRAMScalarCounts.accumulated,show a≠base+siteAt site t by omega] using ih (by omega)
  apply (acc n le_rfl).trans
  simp [blank,fillSegment,show ¬(base ≤ a ∧ a < base+sites) by omega]

theorem run (src base : ℕ) (site : Fin n→Fin sites) (m : Memory w)
    (safe : src+n ≤ base) (fit : base+sites<2^w)
    (loaded : ∀ i, m (src+i.val)=((site i).val:Word w)) :
    (program w src base n sites).Exec m (image base site m) ((4+6*sites)+(3+11*n)) := by
  let blank := fillSegment base sites (fun _ => (0:Word w)) m
  have clearRun : (ProtocolRAMScalarCounts.clear w base sites).Exec m blank (4+6*sites) := by
    unfold ProtocolRAMScalarCounts.clear
    have num : 4+6*sites=4+sites*(2*(Term.literal (w:=w) (k:=0) (n:=1) 0).binds+4) := by
      change 4+6*sites=4+sites*(2*1+4)
      omega
    rw [num]
    intro P R K mach pc reg pub exit code data cfg raw enter eq
    subst raw
    exact PhysicalInputPhases.writing_spec (.literal 0 : Term w 0 1) Fin.elim0 base sites fit
      (fun _=>True) (fun _=>0) (by intros;exact Term.eval_literal ..) mach pc reg pub exit code data cfg m enter trivial
  have keyRead : ∀ t < n, blank (src+t)=(siteAt site t:Word w) := by
    intro t ht
    simpa [blank,fillSegment,show ¬(base ≤ src+t ∧ src+t < base+sites) by omega,
      siteAt,ht] using loaded ⟨t,ht⟩
  apply clearRun.then
  intro P R K mach pc reg pub exit code data cfg raw enter eq
  subst raw
  exact ProtocolRAMScalarCounts.run src base sites n (siteAt site) safe fit (by omega)
    (fun t ht => by simp [siteAt,ht]) mach pc reg pub exit code data cfg blank enter keyRead


end Hierarchy.ProtocolRAMSiteCounts

end OAI
