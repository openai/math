import OAI.Hierarchy.ProtocolRAMReservePrefixReplay
import OAI.Hierarchy.ProtocolRAMPaidPrefixRank
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDirectory

namespace OAI
/-! # True chronological prefixes of the original owner and debit archive -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open CatalystArchive Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard
open scoped BigOperators Classical

variable {count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)

def date (length n : ℕ) : Fin (length+1) := ⟨min n length,by omega⟩

/-- The full row directory uses date-major finite-sigma numbering. Reading exactly
this initial segment therefore requires no second copy of the pointer/origin directory. -/
def countAt (j : ℕ) : Fin (recordCount c issued+1) :=
  let w := fun t=>(atTime c issued t).rows
  ⟨PaidPrefixRank.prefixCount w (date (events c).length j),
    Nat.lt_succ_of_le (PaidPrefixRank.le w _)⟩

/-- The physical code lengths at every date depend only on published row arities. -/
def publicCount (arity : Attempt→ℕ) (j : ℕ) : Fin (rowOnlyCount c arity+1) :=
  let w := fun t=>rowArity arity ((events c).get t)
  ⟨PaidPrefixRank.prefixCount w (date (events c).length j),
    Nat.lt_succ_of_le (PaidPrefixRank.le w _)⟩

theorem public_count_eq (arity : Attempt→ℕ) (same : ∀a,(issued a).rows=arity a) (j : ℕ) :
    (countAt c issued j).val=(publicCount c arity j).val := by
  dsimp only [countAt,publicCount]
  apply congrArg (fun w : Fin (events c).length→ℕ=>PaidPrefixRank.prefixCount w (date (events c).length j))
  funext t
  change (eventEntry issued ((events c).get t)).rows = rowArity arity ((events c).get t)
  cases (events c).get t with
  | attempt a => exact same a
  | feed _ => rfl

theorem public_program_eq (arity : Attempt→ℕ) (same : ∀a,(issued a).rows=arity a)
    (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (a : ReserveUse.Archive)
    (reserve W last : ℕ) :
    program L old a (countAt c issued) reserve W last =
      program L old a (publicCount c arity) reserve W last := by
  induction last with
  | zero =>
    change ReserveUse.native W a (banks L old 0) count (countAt c issued 0).val reserve = _
    rw [public_count_eq c issued arity same]; rfl
  | succ j ih =>
    change (program L old a (countAt c issued) reserve W j).seq
      (ReserveUse.native W a (banks L old (j+1)) count (countAt c issued (j+1)).val reserve) = _
    rw [ih,public_count_eq c issued arity same]; rfl

theorem chronological (j : ℕ) (i : Fin count) :
    used (site c issued) (debit c issued) (countAt c issued j) i =
    ∑ r : Fin (recordCount c issued),
      if ((rank c issued).symm r).1.val<j ∧ site c issued r=i then debit c issued r else 0 := by
  let w := fun t=>(atTime c issued t).rows
  let n := countAt c issued j
  let value (r : Fin (recordCount c issued)) := if site c issued r=i then debit c issued r else 0
  change (∑ b : Fin n.val,value (Fin.castLE (Nat.le_of_lt_succ n.isLt) b)) = _
  rw [PaidPrefixRank.sum_initial (Nat.le_of_lt_succ n.isLt) value]
  apply Finset.sum_congr rfl
  intro r _
  have iff := PaidPrefixRank.lt_iff w (date (events c).length j) r
  change r.val < n.val ↔ ((rank c issued).symm r).1.val < min j (events c).length at iff
  have bound := ((rank c issued).symm r).1.isLt
  have counted : r.val<n.val ↔ ((rank c issued).symm r).1.val<j := by omega
  by_cases early : ((rank c issued).symm r).1.val < j
  · simp [counted.mpr early,early,value]
  · simp [mt counted.mp early,early]

/-- One native date adds just the rows emitted at that date, including the zero
contribution at feed and transparent events. -/
theorem chronological_step (j : Fin (events c).length) (i : Fin count) :
    used (site c issued) (debit c issued) (countAt c issued (j.val+1)) i =
    used (site c issued) (debit c issued) (countAt c issued j.val) i +
      ∑ r : Fin (recordCount c issued),
        if ((rank c issued).symm r).1.val=j.val ∧ site c issued r=i then debit c issued r else 0 := by
  rw [chronological,chronological,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases owner : site c issued r=i
  · simp only [owner,and_true]
    split_ifs <;> omega
  · simp [owner]

theorem funded (j : ℕ) (i : Fin count) :
    used (site c issued) (debit c issued) (countAt c issued j) i≤fuel c*payload := by
  rw [chronological]
  exact CatalystArchive.prefix_funded c issued j i

/-- Recover the reusable prefix directory from the installed native pointer, kind and
event archive words that already certify the terminal reserve reporter. -/
theorem Directory.of_archive {n w : ℕ} (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw mem : Memory w) (site : Fin n→Fin count) (bits : Fin n→ℕ)
    (ordered : a.kind.base+2*n≤a.pointer.base) (ks : 2*n≤a.kind.size)
    (ps : 2*n≤a.pointer.size) (wide : 2*n≤2^w)
    (kept : ∀ (u : ℕ),u<2*n →
      mem (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      mem (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u))
    (owners : ∀i,id i<a.history.size ∧ id i<2^w ∧
      mem (a.history.base+id i)=((site i).val:Word w))
    (amounts : ∀i,amt i<a.history.size ∧ amt i<2^w ∧
      mem (a.history.base+amt i)=(bits i:Word w)) :
    Directory a site bits mem := by
  obtain ⟨kind,owner,amount⟩ := CatalystArchive.observed_fields a id amt raw mem site bits
    ordered ks ps wide kept owners amounts
  exact ⟨kind,owner,amount⟩

/-- Reading immutable origin, indirection and debit words commutes with prior width
replays whose writing starts above all three archived banks. -/
theorem Directory.preserved {W N : ℕ} {a : ReserveUse.Archive} {site : Fin N→Fin count} {debit : Fin N→ℕ}
    {m u : Memory W} (dir : Directory a site debit m) (floor : ℕ)
    (same : ∀ x<floor,u x=m x)
    (below : a.kind.base+a.kind.size≤floor ∧ a.pointer.base+a.pointer.size≤floor ∧ a.history.base+a.history.size≤floor) :
    Directory a site debit u := by
  have read (b : Bank) (endAt : b.base+b.size≤floor) (x : Word W) : b.read u x=b.read m x := by
    change u (b.base+x.val%b.size)=m (b.base+x.val%b.size)
    have small : x.val%b.size<b.size := Nat.mod_lt _ (Nat.two_pow_pos _)
    exact same _ (by omega)
  refine ⟨fun i=>?_,fun i=>?_,fun i=>?_⟩
  · simpa only [read a.kind below.1] using dir.kind i
  · rw [read a.pointer below.2.1,read a.history below.2.2]
    exact dir.owner i
  · rw [read a.pointer below.2.1,read a.history below.2.2]
    exact dir.amount i

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve

end
end OAI
