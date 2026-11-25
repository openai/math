import OAI.Hierarchy.DescentDatedActorSetup
import OAI.Hierarchy.DescentRawFieldOps
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! Issuing the six physical scalar columns used by the successor actor classifier. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open ProtocolRAM DescentOrdinaryDestRAM DescentSIMDLookup DescentActorRaster
open DescentIssuedTerminalId DescentPackedColony.Phase.Arena
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ} (v : ActorSetup)

def depthExpr (raw : Bank) : Expr := .lookup raw (times (v.oldWidth+1) .row)

def constants (base : ℕ) : Image w :=
  let s:=v.starts base
  let l:=v.levels base
  let h:=v.heights base
  ⟨s.base,next h,fun p=>
    if p<l.base then (((p-s.base)*v.arity : ℕ):Word w)
    else if p<h.base then (((p-l.base)-v.common+1 : ℕ):Word w)
    else ((Nat.clog 2 (p-h.base)+1 : ℕ):Word w)⟩

def headers (base : ℕ) (raw : Bank) (book : Expr) (w : ℕ) :=
  ((scan w base v.hosts (v.depthExpr raw)).seq
    (scan w (v.counts base).base (v.hosts*v.arity) book)).seq ((v.constants base (w:=w)).program)

def headerTime (base : ℕ) (raw : Bank) (book : Expr) (w : ℕ) :=
  ((4+v.hosts*(2*(v.depthExpr raw).work+4))+(4+v.hosts*v.arity*(2*book.work+4)))+
    (4+10*(v.constants base (w:=w)).length)

def headerImage (base : ℕ) (raw : Bank) (book : Expr) (m : Memory w) :=
  (v.constants base).output
    (image (v.counts base).base (v.hosts*v.arity) book (image base v.hosts (v.depthExpr raw) m))

private theorem mul_fits (a : ℕ) (w base : ℕ) : (times a .row).Fits w base := by
  induction a with
  | zero=>trivial
  | succ a ih=>exact ⟨trivial,ih⟩

theorem monotone (base : ℕ) :
    base+v.hosts≤(v.counts base).base ∧
    (v.counts base).base+v.hosts*v.arity≤(v.starts base).base ∧
    (v.starts base).base+v.hosts≤(v.levels base).base ∧
    (v.levels base).base+(v.levels base).size=(v.heights base).base ∧
    (v.heights base).base+(v.heights base).size=(v.gate base).scalar := by
  obtain ⟨d,c,s,_,_⟩:=v.extent_input base
  exact ⟨Nat.add_le_add_left d _,Nat.add_le_add_left c _,Nat.add_le_add_left s _,rfl,rfl⟩

private theorem exec_three (A B C : Procedure w) (m₀ m₁ m₂ m₃ : Memory w) (ta tb tc : ℕ)
    (first : A.Exec m₀ m₁ ta) (second : B.Exec m₁ m₂ tb) (third : C.Exec m₂ m₃ tc) :
    ((A.seq B).seq C).Exec m₀ m₃ ((ta+tb)+tc) := by
  have prefixRun : (A.seq B).Exec m₀ m₂ (ta+tb) := by
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=A) (B:=B) (a:=m₀) (b:=m₁) (c:=m₂) first second machine
  intro labels regs keys machine
  exact Procedure.Exec.then (A:=A.seq B) (B:=C) (a:=m₀) (b:=m₂) (c:=m₃) prefixRun third machine

set_option maxHeartbeats 600000 in
theorem headers_any (base : ℕ) (raw : Bank) (book : Expr) (m : Memory w)
    (input : raw.Fits w base) (refs : book.Fits w base) (room : (v.gate base).scalar<2^w) :
    (v.headers base raw book w).Exec m (v.headerImage base raw book m) (v.headerTime base raw book w) ∧
    CheapCode (v.headers base raw book w) ∧
    ∀z,z<base ∨ (v.gate base).scalar≤z→v.headerImage base raw book m z=m z := by
  obtain ⟨bd,bc,bs,bl,bh⟩:=v.monotone base
  have stop:(v.constants (w:=w) base).stop=(v.gate base).scalar:=rfl
  have start:(v.constants (w:=w) base).low=(v.starts base).base:=rfl
  have lit:(v.constants (w:=w) base).low+(v.constants (w:=w) base).length<2^w:=by unfold Image.length;omega
  let m₁:=image base v.hosts (v.depthExpr raw) m
  let m₂:=image (v.counts base).base (v.hosts*v.arity) book m₁
  obtain ⟨stamp,_,hold⟩:=(v.constants base).issue m₂ lit
  have one : (scan w base v.hosts (v.depthExpr raw)).Exec m m₁
      (4+v.hosts*(2*(v.depthExpr raw).work+4)) :=
    @scan_exec w base v.hosts (v.depthExpr raw) m ⟨input,mul_fits ..⟩ (by omega)
  have two : (scan w (v.counts base).base (v.hosts*v.arity) book).Exec m₁ m₂
      (4+v.hosts*v.arity*(2*book.work+4)) :=
    @scan_exec w (v.counts base).base (v.hosts*v.arity) book m₁
      (ProtocolRAMGeneratedWrite.fits_mono _ (by omega) refs) (by omega)
  let depthScan:=scan w base v.hosts (v.depthExpr raw)
  let countScan:=scan w (v.counts base).base (v.hosts*v.arity) book
  let literals:=v.constants base (w:=w)
  have litCheap : CheapCode literals.program := literals.hardware.1
  refine ⟨exec_three depthScan countScan literals.program m m₁ m₂ (literals.output m₂)
    (4+v.hosts*(2*(v.depthExpr raw).work+4)) (4+v.hosts*v.arity*(2*book.work+4))
    (4+10*literals.length) one two stamp,
    @cheap_seq w (depthScan.seq countScan) literals.program
      (@cheap_seq w depthScan countScan (scan_cheap w base v.hosts (v.depthExpr raw))
        (scan_cheap w (v.counts base).base (v.hosts*v.arity) book)) litCheap,?_⟩
  intro z away
  exact (hold z (by omega)).trans
    ((ProtocolRAMGeneratedWrite.frame_image (v.counts base).base (v.hosts*v.arity) book m₁ z
      (by omega)).trans (ProtocolRAMGeneratedWrite.frame_image base v.hosts (v.depthExpr raw) m z (by omega)))

theorem headers_read (base : ℕ) (raw : Bank) (book : Expr) (m : Memory w)
    (input : raw.Fits w base) (refs : book.Fits w base) (room : (v.gate base).scalar<2^w)
    (extent : v.hosts*(v.oldWidth+1)≤raw.size) :
    let dst:=v.headerImage base raw book m
    (∀h:Fin v.hosts,dst ((v.depths base).base+h.val)=m (raw.base+h.val*(v.oldWidth+1))) ∧
    (∀i:Fin (v.hosts*v.arity),dst ((v.counts base).base+i.val)=book.eval m (i.val:Word w)) ∧
    (∀h:Fin v.hosts,dst ((v.starts base).base+h.val)=((h.val*v.arity:ℕ):Word w)) ∧
    (∀j,j<(v.levels base).size→dst ((v.levels base).base+j)=((j-v.common+1:ℕ):Word w)) ∧
    (∀j,j<(v.heights base).size→dst ((v.heights base).base+j)=((Nat.clog 2 j+1:ℕ):Word w)) := by
  obtain ⟨bd,bc,bs,bl,bh⟩:=v.monotone base
  have stop:(v.constants (w:=w) base).stop=(v.gate base).scalar:=rfl
  have start:(v.constants (w:=w) base).low=(v.starts base).base:=rfl
  let m₁:=image base v.hosts (v.depthExpr raw) m
  let m₂:=image (v.counts base).base (v.hosts*v.arity) book m₁
  obtain ⟨_,stored,hold⟩:=(v.constants base).issue m₂ (by unfold Image.length;omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro h
    have live:=h.isLt
    have roomIdx:=Nat.mul_le_mul_right (v.oldWidth+1) h.isLt
    rw [Nat.succ_mul] at roomIdx
    change (v.constants base).output m₂ (base+h.val)=_
    calc
      _ = m₂ (base+h.val) := hold _ (.inl (by omega))
      _ = m₁ (base+h.val) := ProtocolRAMGeneratedWrite.frame_image (v.counts base).base
        (v.hosts*v.arity) book m₁ _ (.inl (by omega))
      _ = (v.depthExpr raw).eval m (h.val:Word w) :=
        ProtocolRAMGeneratedWrite.read_image base v.hosts (v.depthExpr raw) m h
      _ = _ := lookup_nat raw m _ (times (v.oldWidth+1) .row) (h.val*(v.oldWidth+1))
        (by simp [times_eval,Expr.eval,Nat.cast_mul,mul_comm]) (by omega) input.2.1
  · intro i
    have live:=i.isLt
    let addr:=(v.counts base).base+i.val
    change (v.constants base).output m₂ addr=_
    calc
      _ = m₂ addr := hold _ (.inl (by dsimp [addr];omega))
      _ = book.eval m₁ (i.val:Word w) := ProtocolRAMGeneratedWrite.read_image _ _ book m₁ i
      _ = _ := eval_below book _ m m₁ refs (fun z hz=>
        ProtocolRAMGeneratedWrite.frame_image base v.hosts (v.depthExpr raw) m z (.inl hz))
  · intro h
    have live:=h.isLt
    let addr:=(v.starts base).base+h.val
    exact (stored addr (by dsimp [addr];omega) (by dsimp [addr];omega)).trans (by
      simp [addr,constants,show (v.starts base).base+h.val<(v.levels base).base by omega])
  · intro j hj
    let addr:=(v.levels base).base+j
    exact (stored addr (by dsimp [addr];omega) (by dsimp [addr];omega)).trans (by
      simp [addr,constants,show (v.levels base).base+j<(v.heights base).base by omega])
  · intro j hj
    let addr:=(v.heights base).base+j
    exact (stored addr (by dsimp [addr];omega) (by dsimp [addr];omega)).trans (by
      simp [addr,constants,show ¬(v.heights base).base+j<(v.levels base).base by omega])

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
