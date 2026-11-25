import OAI.Hierarchy.DescentDatedActorHeaders

namespace OAI
/-! The measured actor machine runs at its declared clock on arbitrary input RAM. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentSIMDLookup DescentPackedZip DescentActorRaster
open DescentSharedLeafLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ} (v : ActorSetup) (base : ℕ) (pop : Bank)
    (ctrl : Fin v.shapes→Headers.Control) (qs : Fin v.shapes→CPU.Query) (st : Expr)
def operator :=
  HeaderGate.program (w:=w) (H:=v.hosts) (G:=v.groups) (M:=v.lanes)
    (r:=v.localDepth) (t:=v.stencilBits) (a:=v.headerBits) (v.gate base) (v.sources pop base) ctrl qs st

def operatorTime (w : ℕ) :=
  HeaderGate.cost (w:=w) (H:=v.hosts) (G:=v.groups) (M:=v.lanes)
    (r:=v.localDepth) (t:=v.stencilBits) (a:=v.headerBits) (v.gate base) (v.sources pop base) ctrl qs st

def operatorImage (m : Memory w) :=
  HeaderGate.result (H:=v.hosts) (G:=v.groups) (M:=v.lanes) (r:=v.localDepth) (t:=v.stencilBits)
    (a:=v.headerBits) (v.gate base) (v.sources pop base) ctrl qs st m

/-- All entries are static address bounds on the program named by the public actor roster. -/
structure GateFits (v : ActorSetup) (base : ℕ) (pop : Bank)
    (ctrl : Fin v.shapes→Headers.Control) (st : Expr) (w : ℕ) : Prop where
  control : ∀j,(Headers.expression (v.sources pop base) (ctrl j)).Fits w (v.gate base).scalar
  stencil : st.Fits w (v.gate base).scalar
  header : ∀j : Fin v.shapes,(HeaderGate.heads (v.gate base) v.hosts v.groups v.lanes v.headerBits j).Fits w (v.gate base).gateBase
  endFit : v.endAddress base<2^w

private theorem exec_four (A B C D : Procedure w) (m₀ m₁ m₂ m₃ m₄ : Memory w) (ta tb tc td : ℕ)
    (a : A.Exec m₀ m₁ ta) (b : B.Exec m₁ m₂ tb) (c : C.Exec m₂ m₃ tc) (d : D.Exec m₃ m₄ td) :
    ((A.seq B).seq (C.seq D)).Exec m₀ m₄ ((ta+tb)+(tc+td)) := by
  have first : (A.seq B).Exec m₀ m₂ (ta+tb) := by
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=A) (B:=B) (a:=m₀) (b:=m₁) (c:=m₂) a b machine
  have second : (C.seq D).Exec m₂ m₄ (tc+td) := by
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=C) (B:=D) (a:=m₂) (b:=m₃) (c:=m₄) c d machine
  intro labels regs keys machine
  exact Procedure.Exec.then (A:=A.seq B) (B:=C.seq D) (a:=m₀) (b:=m₂) (c:=m₄) first second machine

set_option maxHeartbeats 600000 in
theorem operator_any (m : Memory w) (safe : v.GateFits base pop ctrl st w) :
    (v.operator base pop ctrl qs st (w:=w)).Exec m (v.operatorImage base pop ctrl qs st m)
      (v.operatorTime base pop ctrl qs st w) ∧ CheapCode (v.operator base pop ctrl qs st (w:=w)) ∧
    ∀z,z<(v.gate base).scalar ∨ v.endAddress base≤z→v.operatorImage base pop ctrl qs st m z=m z := by
  let layout:=v.gate base
  let jobs:=Headers.passes (v.sources pop base) ctrl layout.scalar v.hosts
  let literals:=Public.literals layout.repeatBase 1 v.hosts v.groups v.lanes v.headerBits w
  let menu:=CPU.menu v.localDepth v.stencilBits v.headerBits qs
  let tables:=Book.tables menu v.unitBits v.lanes layout.gateBase
  let heads:=HeaderGate.heads (Q:=v.shapes) layout v.hosts v.groups v.lanes v.headerBits
  let expressions:=List.ofFn (CPU.expression tables st heads)
  let gates:=CPU.passes tables st heads layout.output v.hosts v.groups v.lanes
  let m₁:=ProtocolRAM.result jobs m
  let m₂:=literals.output m₁
  let m₃:=Book.image menu v.unitBits v.lanes layout.gateBase m₂
  obtain ⟨scalarEnd,repeatEnd,gateEnd⟩:=v.gate_order base
  change layout.scalar+v.shapes*v.hosts=layout.repeatBase at scalarEnd
  change Public.stop layout.repeatBase v.hosts v.groups v.lanes v.headerBits=layout.gateBase at repeatEnd
  change layout.gateBase+v.shapes*(2*2^(v.unitBits*v.lanes))=layout.output at gateEnd
  have slots:=v.extent_scene base
  have edge : layout.output+(v.scene base).size=v.endAddress base := rfl
  have total:=safe.endFit
  have repeatLower : layout.repeatBase≤Public.stop layout.repeatBase v.hosts v.groups v.lanes v.headerBits := by
    unfold Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have lower : layout.gateBase≤layout.output := by omega
  have sceneRoom : layout.output+v.shapes*(v.hosts*chunks v.groups v.lanes)<2^w := by
    change layout.output+v.shapes*(v.hosts*v.chunksPerHost)<2^w
    omega
  obtain ⟨one,_,frame₁,ch₁⟩:=Headers.issue (v.sources pop base) ctrl m layout.scalar v.hosts safe.control (by omega)
  obtain ⟨two,_,frame₂⟩:=literals.issue m₁ (by
    change layout.repeatBase+(Public.stop layout.repeatBase v.hosts v.groups v.lanes v.headerBits-layout.repeatBase)<2^w
    omega)
  obtain ⟨three,_,frame₃,ch₃⟩:=Book.mount menu v.unitBits v.lanes layout.gateBase m₂ (fun _=>le_rfl) (by omega)
  have access (i : Fin v.shapes) :
      DescentPackedZip.Fits (tables i) st (heads i) (v.stencilBits*2^v.localDepth) v.headerBits v.lanes layout.output w := by
    have hw:=Book.geometry menu v.unitBits v.lanes layout.gateBase i gateEnd.le (by omega : layout.output<2^w) le_rfl
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (by omega : layout.scalar≤layout.output) safe.stencil,
      ProtocolRAMGeneratedWrite.fits_mono _ lower (safe.header i),hw.1,hw.2,rfl,rfl⟩
  have fs : ∀e∈expressions,e.Fits w layout.output := by
    intro e member
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member
    simp [CPU.expression,Tables.read,Expr.Fits,(access j).left,(access j).right,(access j).shift,(access j).apply]
  have len : expressions.length=v.shapes := List.length_ofFn
  have four : (ProtocolRAM.program w gates).Exec m₃ (ProtocolRAM.result gates m₃) (ProtocolRAM.clock gates) :=
    @ProbeStage.Native.columns_exec w (v.hosts*chunks v.groups v.lanes) layout.output expressions m₃
      (ProbeStage.Native.columns_safe expressions le_rfl fs (by simpa only [len] using sceneRoom))
  let scalarCode:=ProtocolRAM.program w jobs
  let installCode:=Book.install menu v.unitBits v.lanes w layout.gateBase
  let gateCode:=ProtocolRAM.program w gates
  have litCheap : CheapCode literals.program := literals.hardware.1
  refine ⟨exec_four scalarCode literals.program installCode gateCode m m₁ m₂ m₃ (ProtocolRAM.result gates m₃)
    (ProtocolRAM.clock jobs) (4+10*literals.length) (4+10*(v.shapes*(2*2^(v.unitBits*v.lanes))))
    (ProtocolRAM.clock gates) one two three four,
    @cheap_seq w (scalarCode.seq literals.program) (installCode.seq gateCode)
      (@cheap_seq w scalarCode literals.program ch₁ litCheap)
      (@cheap_seq w installCode gateCode ch₃ (@ProtocolRAM.program_cheap w gates)),?_⟩
  intro z away
  change z<layout.scalar ∨ v.endAddress base≤z at away
  have active : z<layout.output ∨ layout.output+expressions.length*(v.hosts*chunks v.groups v.lanes)≤z := by
    rw [len]
    change z<layout.output ∨ layout.output+v.shapes*(v.hosts*v.chunksPerHost)≤z
    omega
  exact (ProbeStage.Native.columns_frame expressions m₃ active).trans
    ((frame₃ z (by omega)).trans ((frame₂ z (by
      change z<layout.repeatBase ∨ Public.stop layout.repeatBase v.hosts v.groups v.lanes v.headerBits≤z
      omega)).trans (frame₁ z (by omega))))

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
