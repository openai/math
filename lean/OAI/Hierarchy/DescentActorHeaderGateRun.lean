import OAI.Hierarchy.DescentActorHeaderBroadcast
import OAI.Hierarchy.DescentActorGateImage

namespace OAI
/-! # Issuing the physical local scalar headers and the packed reset actor gates -/
namespace Hierarchy.DescentActorRaster
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentSharedLeafLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace HeaderGate

structure Layout where
  scalar : ℕ
  repeatBase : ℕ
  gateBase : ℕ
  output : ℕ

variable {Q : ℕ}

def ranks (L : Layout) (H : ℕ) (j : Fin Q) : Bank :=⟨L.scalar+j.val*H,Nat.clog 2 H⟩
def header (L : Layout) (H G M a : ℕ) (j : Fin Q) :=Public.header L.repeatBase H G M a (ranks L H j)
def heads (L : Layout) (H G M a : ℕ) (j : Fin Q) :=source (header L H G M a j) (0:Fin 1)

variable {H G M r t a w : ℕ} (L : Layout)
    (b : Headers.Banks) (ctrl : Fin Q→Headers.Control) (q : Fin Q→CPU.Query) (st : Expr)
local notation "init" => Headers.passes b ctrl L.scalar H
local notation "image_" => Public.literals L.repeatBase 1 H G M a w
local notation "unit" => t*2^r+a
local notation "qbook" => CPU.menu r t a q
local notation "tables" => Book.tables qbook unit M L.gateBase
local notation "opcode" => CPU.passes tables st (heads L H G M a) L.output H G M
local notation "endScalar" => L.scalar+Q*H
local notation "endRepeat" => Public.stop L.repeatBase H G M a
local notation "endGate" => L.gateBase+Q*(2*2^(unit*M))
local notation "endOut" => L.output+Q*(H*chunks G M)

def program := ((ProtocolRAM.program w init).seq (image_).program).seq
    ((Book.install qbook unit M w L.gateBase).seq (ProtocolRAM.program w opcode))
def cost := (clock init+(4+10*(image_).length))+((4+10*(Q*(2*2^(unit*M))))+clock opcode)
def result (m : Memory w) :=
  ProtocolRAM.result opcode (Book.image qbook unit M L.gateBase ((image_).output (ProtocolRAM.result init m)))

theorem run (m : Memory w) (rows : Fin H→Fin G→Cell (t*2^r)) (tag : Fin Q→Fin H→Cell a)
    (fits : ∀j,(Headers.expression b (ctrl j)).Fits w L.scalar) (earlier : st.Fits w L.scalar)
    (physical : ∀j(h:Fin H),(Headers.expression b (ctrl j)).eval m (h.val:Word w)=((tag j h).val:Word w))
    (sheet : Source st rows M m)
    (tableRoom : (image_).low+(image_).length<2^w)
    (before : endScalar≤L.repeatBase ∧ endRepeat≤L.gateBase ∧ endGate≤L.output)
    (stop : endOut<2^w)
    (accessible : ∀ j : Fin Q, Readable (header L H G M a j) 1 H G M a w L.gateBase) :
    (program (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) (w:=w) L b ctrl q st).Exec m
      (result (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) L b ctrl q st m)
      (cost (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) (w:=w) L b ctrl q st) ∧
    (∀(j : Fin Q)(p : Row H G M),result (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) L b ctrl q st m
        (L.output+j.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>CPU.gate r t a (q j) (rows h g) (tag j h)) p).val:Word w)) ∧
    (∀u,u<L.scalar ∨ endOut≤u → result (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) L b ctrl q st m u=m u) ∧
    CheapCode (program (H:=H) (G:=G) (M:=M) (r:=r) (t:=t) (a:=a) (w:=w) L b ctrl q st) := by
  let initial:=ProtocolRAM.result init m
  let src:=(image_).output initial
  have lo : L.repeatBase ≤ endRepeat := by
    unfold Public.stop
    exact (Nat.le_add_right L.repeatBase _).trans (Nat.le_add_right _ _)
  have scalarEnd:endScalar<2^w:=by omega
  obtain ⟨issued,numeric,survives,cpu⟩:=Headers.issue b ctrl m L.scalar H fits scalarEnd
  obtain ⟨mounted,lit,protectedMem⟩:=(image_).issue initial tableRoom
  have reads (j:Fin Q)(h:Fin H): src ((ranks L H j).base+h.val)=((tag j h).val:Word w):=by
    have len : j.val*H+h.val<Q*H := (Nat.add_lt_add_left h.isLt _).trans_le (by
      rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ j.isLt)
    have kept:=protectedMem (L.scalar+j.val*H+h.val) (Or.inl (by change _<L.repeatBase;omega))
    exact kept.trans ((numeric j h).trans (physical j h))
  have previous (j : Fin Q) : Source (heads L H G M a j) (fun h (_:Fin G)=>tag j h) M src :=
    Headers.broadcast_header L.gateBase (header L H G M a j) src _ (accessible j)
      (Public.mounted L.repeatBase 1 H G M a (ranks L H j) src lit) (reads j)
  have headAccess (j : Fin Q) : (heads L H G M a j).Fits w L.gateBase :=by
    let B:=header L H G M a j
    have ff b (p : b∈[B.ranks,B.start,B.cut,B.broadcast]):b.Fits w L.gateBase :=(accessible j).fit b p
    exact ⟨ff B.broadcast (by simp),⟨ff B.cut (by simp),trivial⟩,
      ff B.ranks (by simp),⟨ff B.start (by simp),trivial⟩,trivial⟩
  have keep (u:ℕ)(hu:u<L.scalar):src u=m u:=(protectedMem u (Or.inl (by change _<L.repeatBase;omega))).trans
    (survives u (Or.inl hu))
  have low:L.scalar≤L.gateBase:=by omega
  have srcSheet : Source st rows M src := fun p=>(eval_below st _ m src earlier keep).trans (sheet p)
  obtain ⟨gates,done,frame,cheap⟩:=CPU.installed q st (heads L H G M a) L.gateBase L.output src rows
    (fun j h _=>tag j h) (ProtocolRAMGeneratedWrite.fits_mono _ low earlier) headAccess srcSheet previous before.2.2 stop
  refine ⟨Procedure.Exec.then (Procedure.Exec.then issued mounted) gates,done,?_,
    cheap_seq (cheap_seq cpu (image_).hardware.1) cheap⟩
  intro u outside
  exact (frame u (by omega)).trans ((protectedMem u (by change u<L.repeatBase ∨ endRepeat≤u;omega)).trans (survives u (by omega)))

end HeaderGate
end
end Hierarchy.DescentActorRaster

end OAI
