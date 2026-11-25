import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Size of the issued native paid-width table -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open scoped Classical
variable {z d k q goods r edges : ℕ}

theorem Format.paid_shape (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ) (role : Expr)
    (ids : Fin goods→Expr) (tree core : Traversals) (bits cap : ℕ)
    (direct : p.pricedArea.occurrences≤cap) (forest : tree.positions≤cap) (spilled : core.positions≤cap) :
    let out:=p.paidSlices sink idBase role ids tree core bits
    out.length≤4 ∧ ∀t∈out,t.count≤cap := by
  intro out
  cases m : tree.catalystMate with
  | none =>
    constructor
    · simp [out,Format.paidSlices,Format.mateSlices,m]
    · intro t ht
      simp [out,Format.paidSlices,Format.mateSlices,m] at ht
      rcases ht with eq|eq|eq <;> subst t
      · exact direct
      · exact forest
      · exact spilled
  | some pair =>
    constructor
    · simp [out,Format.paidSlices,Format.mateSlices,m]
    · intro t ht
      simp [out,Format.paidSlices,Format.mateSlices,m] at ht
      rcases ht with eq|eq|eq|eq <;> subst t
      · exact direct
      · exact direct
      · exact forest
      · exact spilled

theorem sparse_length {α β : Type*} (ls : List α) (emit : α→List β) (cap : ℕ)
    (small : ∀x∈ls,(emit x).length≤cap) : (ls.flatMap emit).length≤ls.length*cap := by
  induction ls with
  | nil => simp
  | cons a tail ih =>
    have top:=small a (by simp)
    have rest:=ih (fun x hx=>small x (List.mem_cons_of_mem _ hx))
    simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add top rest

theorem sparse_count (ls : List PaidWidths.Slice) (cap : ℕ) (small : ∀x∈ls,x.count≤cap) :
    (ls.map PaidWidths.Slice.count).sum≤ls.length*cap := by
  induction ls with
  | nil => simp
  | cons a tail ih =>
    have top:=small a (by simp)
    have rest:=ih (fun x hx=>small x (List.mem_cons_of_mem _ hx))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add top rest

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
