import OAI.ThreeFlat.RAM.HistoryCommandSweep

namespace OAI
/-! # The command interpreter as a relocatable native block -/

namespace ThreeFlat.RAM.HistoryCommandSweep

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan ContinuationLink
variable {w k P R K : ℕ}

theorem Pass.mapPublic {e : Term w k 1} (φ : Fin k → Fin K) (data : Fin K → Word w)
    {ctrl : Word w} {m out fuel} (p : Pass e (data∘φ) ctrl m out fuel) :
    Pass (e.mapPublic φ) data ctrl m out fuel := by
  induction p with
  | done _ stop => exact .done _ stop
  | next live count start finish lo hi len word read rest ih =>
    simpa only [Term.binds_mapPublic] using Pass.next (e:=e.mapPublic φ) live count start finish lo hi len word
      (fun a cur low high agree => (Term.eval_mapPublic φ e data cur (fun _ => a)).trans (read a cur low high agree)) ih

theorem advance_block (e : Term w k 1) (base : Fin k) (M : Machine w P R K)
    (pc : Fin (18+(e.labels+6)) ↪ Fin P) (reg : Fin (4+e.binds) ↪ Fin R) (φ : Fin k → Fin K)
    (exit : Fin P) (installed : (block e base).Installed M pc reg φ exit)
    {m out fuel} (pass : Pass e (M.publicData∘φ) (M.publicData (φ base)) m out fuel)
    (c : Config w P R) (start : c.pc=pc (block e base).first) :
    ∃ t≤fuel, ∃ z : Config w P R, z.pc=exit ∧ advance M.program t c m=some (z,out) := by
  let a := e.mapPublic φ
  let head (i : Fin 18) := pc (i.castAdd _)
  let mid (j : Fin (a.labels+6)) := pc (Fin.natAdd 18 (j.cast (by simp [a])))
  let reg' := (Fin.castLEEmb (show 4+a.binds≤4+e.binds by simp [a])).trans reg
  let L := TickGenerateTable.labels a mid (head 13)
  have ctrl (i : Fin 18) : M.code (head i)=HistoryJoinController.code head (TickGenerateTable.regs a reg') (φ base) L.guard exit i := by
    simpa only [head,block,Fin.append_left] using installed (i.castAdd _)
  have rom (i : Fin (a.labels+6)) : M.code (mid i)=TickGenerateTable.emit a 0 0 mid reg' (head 13) i := by
    simpa [mid,head,block,a,reg'] using installed (Fin.natAdd 18 (i.cast (by simp [a])))
  have scan := TickGenerateTable.installed a M 0 0 mid reg' (head 13) rom
  have expr := TickGenerateTable.installed_desc a M 0 0 mid reg' (head 13) rom
  exact advance_pass M head (TickGenerateTable.regs a reg') (φ base) exit L rfl a (TickGenerateTable.desc a mid)
    (TickGenerateTable.temp a reg') (TickGenerateTable.fresh a reg') rfl ctrl scan expr
    (pass.mapPublic φ M.publicData) c start

end ThreeFlat.RAM.HistoryCommandSweep

end OAI
