import OAI.ThreeFlat.RAM.HistoryJoinController
import OAI.ThreeFlat.RAM.PhysicalScanLink
import OAI.ThreeFlat.RAM.TickGenerateTable

namespace OAI
/-! # Execution of the selected scratch command tape -/

namespace ThreeFlat.RAM.HistoryCommandSweep

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan ContinuationLink HistoryJoinController
variable {w k p r : ℕ}

/-- Each command may read the image produced by preceding commands. Only
words outside its own destination are used to compute the present outputs. -/
inductive Pass (e : Term w k 1) (pub : Fin k → Word w) (ctrl : Word w) : Memory w → Memory w → ℕ → Prop where
  | done (m : Memory w) (stop : ¬ m ctrl.val<m (ctrl+1).val) : Pass e pub ctrl m m 6
  | next {m out fuel} (live : m ctrl.val<m (ctrl+1).val) (count : ℕ) (start finish : ℕ)
      (lo : (m (m ctrl.val+1).val).val=start) (hi : (m (m ctrl.val+6).val).val=finish)
      (length : start+count=finish) (word : ℕ → Word w)
      (read : ∀ (a : Word w) (cur : Memory w), start≤a.val → a.val<finish →
        agreesOutside start finish cur m → e.eval pub cur (fun _ => a)=word a.val)
      (rest : Pass e pub ctrl (bumpMemory ctrl (fillSegment start count word m)) out fuel) :
      Pass e pub ctrl m out (19+count*(2*e.binds+4)+fuel)

theorem advance_pass (M : Machine w p r k) (P : Fin 18 → Fin p) (R : Fin 4 ↪ Fin r)
    (base : Fin k) (exit : Fin p) (L : Labels p) (back : L.exit=P 13) (e : Term w k 1)
    (loc : Fin e.labels → Fin p) (tmp : Fin e.binds ↪ Fin r) (fresh : ∀ i j,R i≠tmp j)
    (entry : loc e.first=L.describe)
    (control : ∀ i, M.code (P i)=HistoryJoinController.code P R base L.guard exit i)
    (scan : Installed M R L)
    (rom : ∀ i,M.code (loc i)=e.emit loc (fun _ => R 0) tmp (R 2) L.store i)
    {m out fuel} (pass : Pass e M.publicData (M.publicData base) m out fuel)
    (c : Config w p r) (hc : c.pc=P 0) :
    ∃ t≤fuel, ∃ z : Config w p r, z.pc=exit ∧ advance M.program t c m=some (z,out) := by
  induction pass generalizing c with
  | done m stop =>
    exact ⟨6,le_rfl,_,rfl,by simpa only [ite_eq_right stop] using go_dispatch M P R base L.guard exit control c m hc⟩
  | @next m out fuel live count lo hi lower upper len word read rest ih =>
    let v := M.publicData base
    let d := dispatch M P R base (P 6) c m
    let z := loadBounds P R L.guard d m
    have hd : advance M.program 6 c m=some (d,m) := by
      simpa only [d,ite_eq_left live] using go_dispatch M P R base L.guard exit control c m hc
    have hz := go_bounds M P R base L.guard exit control d m rfl
    have regs : z.reg (R 0)=m (m v.val+1).val ∧ z.reg (R 1)=m (m v.val+6).val ∧ z.reg (R 3)=1 := by
      simp [z,d,loadBounds,dispatch,Config.put,Function.update,R.injective.eq_iff,v]
    have low : (z.reg (R 0)).val=lo := by rw [regs.1]; exact lower
    have high : (z.reg (R 1)).val=hi := by rw [regs.2.1]; exact upper
    have inv : scanInvariant R lo hi m z m := ⟨regs.2.2,low.ge,high,fun _ _ => rfl⟩
    have desc := describes_expression M R L e loc tmp fresh entry rom lo hi m word read
    obtain ⟨t,ht,o,opc,adv⟩ := generate M R L scan e.steps word _ desc count z m rfl inv (by rw [low,high,len])
    rw [low] at adv
    rw [Term.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at ht
    let mem := fillSegment lo count word m
    have inc := go_bump M P R base L.guard exit control o mem (opc.trans back)
    obtain ⟨t',ht',q,hq,qr⟩ := ih (bumped M P R base o mem) rfl
    exact ⟨6+7+t+5+t',by omega,q,hq,
      advance_trans (advance_trans (advance_trans (advance_trans hd hz) adv) inc) qr⟩

/-- The same eighteen control rows operate every command. Their feeder is one
fixed finite expression and three guard/store/increment rows. -/
def block (e : Term w k 1) (base : Fin k) : Block w (18+(e.labels+6)) (4+e.binds) k where
  first := (0 : Fin 18).castAdd _
  emit pc reg φ exit i :=
    let a := e.mapPublic φ
    let head j := pc ((j : Fin 18).castAdd _)
    let mid (j : Fin (a.labels+6)) := pc (Fin.natAdd 18 (j.cast (by simp [a])))
    let reg' := (Fin.castLEEmb (show 4+a.binds≤4+e.binds by simp [a])).trans reg
    let inL := TickGenerateTable.labels a mid (head 13)
    Fin.append (HistoryJoinController.code head (TickGenerateTable.regs a reg') (φ base) inL.guard exit)
      (fun j => TickGenerateTable.emit a 0 0 mid reg' (head 13) (j.cast (by simp [a]))) i

end ThreeFlat.RAM.HistoryCommandSweep

end OAI
