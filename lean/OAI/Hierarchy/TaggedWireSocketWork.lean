import OAI.Hierarchy.TaggedWireRoleProgramCore

namespace OAI
/-! # Instruction count of the native signed-role column program -/

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM
noncomputable section

/-- This counts the four actual input expressions. Literals with large
addresses and bank descriptors have the same native instruction counts. -/
structure Socket.Work (x : Socket) (n : ℕ) : Prop where
  positive : x.positive.work≤n
  ordinal : x.ordinal.work≤n
  group : x.group.work≤n
  slot : x.slot.work≤n

theorem socket_work (L : Chart) (x : Socket) {n : ℕ} (ok : x.Work n) :
    (socketSite L x).work≤4*n+18 ∧ (socketCode L x).work≤4*n+18 := by
  obtain ⟨a,b,c,d⟩ := ok
  dsimp [socketSite,socketCode,choose,ReportSockets.SiteROM.siteExpr,RoleROM.positiveKey,RoleROM.expr,Expr.work]
  omega

private theorem sorted_work (a b x y : Expr) (s : Bool) {t n : ℕ}
    (ha : a.work≤t) (hb : b.work≤t) (hx : x.work≤n) (hy : y.work≤n) :
    (sortedRead a b s x y).work≤2*t+2*n+1 := by
  cases s <;> dsimp [sortedRead,Expr.work] <;> omega

theorem field_work (L : Chart) (v : Bool→Socket) {n : ℕ} (ok : ∀s,(v s).Work n)
    (reported : Bool) (j : Fin 4) : (field L v reported j).work≤8*(4*n+18)+5 := by
  have l := socket_work L (v false) (ok false)
  have r := socket_work L (v true) (ok true)
  have site (s : Bool) := sorted_work _ _ _ _ s l.1 r.1 l.1 r.1
  have code (s : Bool) := sorted_work _ _ _ _ s l.1 r.1 l.2 r.2
  have mark (x : Expr) : (tagged reported x).work=2*x.work+3 := by dsimp [tagged,Expr.work];omega
  fin_cases j
  · exact (site false).trans (by omega)
  · exact (site true).trans (by omega)
  · change (tagged reported _).work≤_
    rw [mark]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (code false)) 3).trans (by omega)
  · change (tagged reported _).work≤_
    rw [mark]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (code true)) 3).trans (by omega)

private theorem sum_work (xs : List Expr) (n : ℕ) (ok : ∀x∈xs,x.work≤n) :
    (xs.map Expr.work).sum≤xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head:=ok x (List.mem_cons_self ..)
    have tail:=ih (fun a ha=>ok a (List.mem_cons_of_mem _ ha))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add head tail

theorem volume_bound (L : Chart) (v : Bool→Socket) {n : ℕ} (ok : ∀s,(v s).Work n) (out : Bool) :
    volume L v out≤4*(8*(4*n+18)+5) := by
  have each : ∀x∈List.ofFn (field L v out),x.work≤8*(4*n+18)+5 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact field_work L v ok out j
  simpa only [volume,List.length_ofFn] using sum_work _ _ each

theorem ticks_bound (L : Chart) (v : Bool→Socket) {n : ℕ} (ok : ∀s,(v s).Work n)
    (base rows : ℕ) (out : Bool) :
    ticks base rows L v out≤4+4*(4+rows*(8*(8*(4*n+18)+5)+4)) := by
  apply (tick_bound base rows L v out).trans
  have bound := volume_bound L v ok out
  have per : 2*volume L v out+4≤8*(8*(4*n+18)+5)+4 := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 4
    (Nat.add_le_add_left (Nat.mul_le_mul_left rows per) 4)) 4

end
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end OAI
