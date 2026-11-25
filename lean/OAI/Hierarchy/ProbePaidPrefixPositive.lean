import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCalendarPrefixWidths
import OAI.Hierarchy.ProtocolRAMCatalogueMount

namespace OAI
/-! # Positive prefix loads and the physical born row that carries them -/
noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM Calendar
open scoped BigOperators Classical Fin.CommRing
variable {W edges : ℕ}

theorem positive_in_slice (s : Slice) (m : Memory W) (e : Fin edges) (paid : 0 < s.load m e) :
    ∃i : Fin s.count,(s.edge.eval m (i.val:Word W)).val=e.val ∧ 0<(s.amount.eval m (i.val:Word W)).val := by
  by_contra none
  have zero : s.load m e=0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hit
    · by_contra nonzero
      exact none ⟨i,hit,Nat.pos_of_ne_zero nonzero⟩
    · rfl
  omega

theorem positive_in_list (ss : List Slice) (m : Memory W) (e : Fin edges) (paid : 0 < total ss m e) :
    ∃s∈ss,0 < s.load m e := by
  induction ss with
  | nil => simp [total] at paid
  | cons s ss ih =>
    change 0 < s.load m e+total ss m e at paid
    by_cases first : 0 < s.load m e
    · exact ⟨s,by simp,first⟩
    · obtain ⟨r,mem,pos⟩:=ih (by omega)
      exact ⟨r,List.mem_cons_of_mem _ mem,pos⟩

theorem positive_in_prefix (es : List Event) (schedule : Event→List Slice) (j : ℕ)
    (m : Memory W) (e : Fin edges) (paid : 0 < total (PrefixWidths.prefixRows es schedule j) m e) :
    ∃t : Fin es.length,t.val < j ∧ ∃s∈schedule (es.get t),∃i : Fin s.count,
      (s.edge.eval m (i.val:Word W)).val=e.val ∧ 0<(s.amount.eval m (i.val:Word W)).val := by
  obtain ⟨s,record,positive⟩:=positive_in_list _ _ _ paid
  obtain ⟨ev,early,found⟩:=List.mem_flatMap.mp record
  obtain ⟨i,hi,entry⟩:=List.mem_take_iff_getElem.mp early
  let t : Fin es.length := ⟨i,hi.trans_le (min_le_right ..)⟩
  have date : es.get t=ev:=entry
  exact ⟨t,hi.trans_le (min_le_left ..),s,by rw [date];exact found,positive_in_slice _ _ _ positive⟩

end Hierarchy.ProtocolRAM.PaidWidths

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe
open scoped Classical Fin.CommRing
variable {w h W k K : ℕ} {S : PurchaseSampler}

theorem Board.paid_mount_ends (b : Board) (π : Equiv.Perm (Fin (2^h))) (place : Site h (2^W) k→Fin K)
    (ordering : Fin b.coreRows≃Edges S h (2^W) k) (left right : Memory w) (e : Fin b.rows)
    (view : ∀i : Fin b.boughtRows,b.boughtIndex i=e→
      (b.bought.view left (i.val:Word w)).left=(b.bought.view right (i.val:Word w)).left ∧
      (b.bought.view left (i.val:Word w)).right=(b.bought.view right (i.val:Word w)).right) :
    (b.coreMount π place ordering left).actual.tail e=(b.coreMount π place ordering right).actual.tail e ∧
    (b.coreMount π place ordering left).actual.head e=(b.coreMount π place ordering right).actual.head e := by
  by_cases core : e.val < b.coreRows
  · let i : Fin b.coreRows:=⟨e.val,core⟩
    have eq : e=b.coreIndex i:=Fin.ext rfl
    simp only [eq,Board.coreMount,Board.byKind_core,and_self]
  · let i : Fin b.boughtRows:=⟨e.val-b.coreRows,by have := e.isLt;unfold Board.rows at this;omega⟩
    have eq : b.boughtIndex i=e:=by
      apply Fin.ext
      change b.coreRows+(e.val-b.coreRows)=e.val
      omega
    have pair:=view i eq
    simp only [←eq,Board.coreMount,Board.byKind_bought,pair.1,pair.2,and_self]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
