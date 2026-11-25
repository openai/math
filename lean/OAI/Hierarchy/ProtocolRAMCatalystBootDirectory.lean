import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDirectory
import OAI.Hierarchy.ProtocolRAMCalendarBootStart
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Retention of the original permutation and the historical reserve directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive

open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing Classical BigOperators

private theorem mount_cast {w n m : ℕ} (eq : n=m) (a : ReserveUse.Archive) (raw : Memory w)
    (id amt : Fin n→ℕ) (id' amt' : Fin m→ℕ)
    (idEq : ∀i,id i=id' (Fin.cast eq i)) (amtEq : ∀i,amt i=amt' (Fin.cast eq i)) :
    mount a id amt raw=mount a id' amt' raw := by
  subst m
  have hi : id=id' := funext idEq
  have ha : amt=amt' := funext amtEq
  rw [hi,ha]

/-- The entire physically mounted tape can be built before the issued entries
exist, using only the two public event columns and the prescribed arities. -/
theorem mount_eq_rowOnly {count payload w : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀a,(issued a).rows=rows a) (owner amount : Event→ℕ)
    (a : ReserveUse.Archive) (raw : Memory w) :
    mount a (sourceAt c issued owner) (sourceAt c issued amount) raw =
      mount a (rowOnly c rows owner) (rowOnly c rows amount) raw :=
  mount_cast (recordCount_rowOnly c issued rows same) a raw _ _ _ _
    (sourceAt_eq_rowOnly c issued rows same owner) (sourceAt_eq_rowOnly c issued rows same amount)

variable {z d k jobs n size : ℕ}

/-- The actual finite permutation is mounted on top of both static pointer tables. -/
def header (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw : Boot.Tape z d) : Boot.Tape z d :=
  Boot.permutationWords π (mount a id amt raw)

theorem header_permutation (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw : Boot.Tape z d) (i : Fin (2^z)) :
    header π a id amt raw i.val=((π i).val:Word _) := Boot.permutationWords_get π _ i

structure BootRoom (v : Fin jobs→Market z d k) (size : ℕ) (a : ReserveUse.Archive)
    (n first flag : ℕ) : Prop where
  heap : heapEnd z d copies≤a.kind.base
  ordered : a.kind.base+2*n≤a.pointer.base
  tape : a.pointer.base+2*n≤ size
  market : ∀i,a.pointer.base+2*n≤Boot.low (v i)
  calendar : a.pointer.base+2*n ≤ first
  flagAway : flag<a.kind.base ∨ a.pointer.base+2*n ≤ flag

/-- Use the first free word after the CT heap and the other immutable input. -/
theorem banks_room (v : Fin jobs→Market z d k) (n reserved first flag : ℕ) (hist : Bank) (scratch : ℕ) :
    let base:=max (heapEnd z d copies) reserved
    let stop:=base+2*2^((2*n).log2+1)
    stop≤ size → (∀i,stop≤Boot.low (v i)) → stop ≤ first → (flag<base ∨ stop ≤ flag) →
    BootRoom v size (banks base n hist scratch) n first flag := by
  intro base stop fits markets early flagAway
  have hs := (Nat.lt_log2_self (n:=2*n)).le
  have endBound : base+2^((2*n).log2+1)+2*n≤ stop := by dsimp only [stop];omega
  exact ⟨le_max_left ..,Nat.add_le_add_left hs base,endBound.trans fits,
    fun i=>endBound.trans (markets i),endBound.trans early,flagAway.imp id endBound.trans⟩

/-- Both directory columns survive the genuine boot, every chronological
calendar event, and the final one-word verdict scan. -/
theorem checked_tape {q goods : ℕ} (v : Fin jobs→Market z d k) (layout : Boot.Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw words : Boot.Tape z d)
    (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word _))
    (origin : ∀x,a.kind.base≤x → x<a.pointer.base+2*n → words x=mount a id amt raw x)
    (C : Chart (wordBits z d copies) q goods)
    (arena : Arena) (flag : ℕ) (room : BootRoom v size a n arena.first flag)
    (floor : ∀ e x,x<arena.base C.mesh e→protected C x e)
    (active : mounted C (events C.mesh) (Boot.booted v size words)) :
    let mem:=checkedOut C flag (Boot.booted v size words)
    ∀ u,u<2*n → mem (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      mem (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u) := by
  intro mem
  obtain ⟨_,boot⟩:=Boot.start v layout hd π words auth
  have ordered:=room.ordered
  have seen (x : ℕ) (lo : a.kind.base≤x) (hi : x<a.pointer.base+2*n) :
      mem x=mount a id amt raw x := by
    have top : x < size := hi.trans_le room.tape
    have ct : heapEnd z d copies≤x := room.heap.trans lo
    have old:=boot.kept x ct (fun i inside=>(hi.trans_le (room.market i)).not_ge inside.1)
    have init : Boot.booted v size words x=mount a id amt raw x := by
      rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left top] at old
      exact old.trans (origin x lo hi)
    have off : x<flag ∨ flag+1≤x := by rcases room.flagAway with left|right <;> omega
    change checkedOut C flag (Boot.booted v size words) x=_
    rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off]
    exact (run_frame C _ _ x active (fun e _ => floor e x
      ((hi.trans_le room.calendar).trans_le (Nat.le_add_right ..)))).trans init
  intro u hu
  exact ⟨seen _ (by omega) (by omega),seen _ (by omega) (by omega)⟩

/-- Standalone permutation boot with the static archive mounted on its high tape. -/
theorem checked_kept {q goods : ℕ} (v : Fin jobs→Market z d k) (layout : Boot.Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw : Boot.Tape z d) (C : Chart (wordBits z d copies) q goods)
    (arena : Arena) (flag : ℕ) (room : BootRoom v size a n arena.first flag)
    (floor : ∀ e x,x<arena.base C.mesh e→protected C x e)
    (active : mounted C (events C.mesh) (Boot.booted v size (header π a id amt raw))) :
    let mem:=checkedOut C flag (Boot.booted v size (header π a id amt raw))
    ∀ u,u<2*n → mem (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      mem (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u) := by
  refine checked_tape v layout hd π a id amt raw (header π a id amt raw)
    (header_permutation π a id amt raw) ?_ C arena flag room floor active
  intro x lo _
  have beyond : ¬x<2^z := not_lt.mpr ((Boot.root_extent.trans room.heap).trans lo)
  simp only [header,Boot.permutationWords,dite_eq_right beyond]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
