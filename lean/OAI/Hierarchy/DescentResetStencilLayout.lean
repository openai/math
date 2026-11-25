import OAI.Hierarchy.DescentResetReaderInstall

namespace OAI
/-! # The dated final stencil decoder and its two physical working columns -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local
open DescentPackedColony.Phase ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

structure Chart where
  base : ℕ
  r : ℕ
  q : ℕ
  n : ℕ
  t : ℕ
  H : ℕ
  groups : ℕ
  M : ℕ

namespace Chart
variable (C : Chart)

def N := count C.r C.q
def a := C.n*C.N
def b := C.t*2^C.r
def rows := C.H*chunks C.groups C.M
def bits := Nat.clog 2 C.rows
def rowRoom := 2^C.bits
def table := StencilTables.start C.base C.n C.N C.M (C.N+1)
def mask := C.table+2^(C.a*C.M)
def scratch := C.mask+C.rowRoom
def out := C.scratch+C.rowRoom
def endAddress := C.out+C.rows
def banks : Banks := DescentPackedFallbackTree.Image.banks C.a ⟨C.scratch,C.bits⟩ C.table C.bits C.M
def tabs := StencilTables.tabs C.base C.n C.N C.M
def gathers : Arena.Image w := StencilTables.image C.base C.n C.N C.M

def literals (f B Y : ℕ) : Arena.Image w :=
  ⟨C.table,C.scratch,DescentPackedFallbackTree.Image.header (Stencil.lookup C.r C.q C.n C.t f B Y) C.H C.groups C.M w C.table (fun _=>0)⟩

theorem rowRoom_le : C.rows≤C.rowRoom:=Nat.le_pow_clog (by decide) _

theorem fit {w : ℕ} (room : C.endAddress<2^w) (short : C.M*max C.a C.b≤w/2) :
    DescentSIMDLookup.Fits C.banks C.a C.b C.M C.H C.groups w C.out ∧
    C.banks.source.base+C.rows<2^w ∧ C.banks.dictionary.base+C.banks.dictionary.size≤C.scratch ∧
    C.banks.mask.base+C.banks.mask.size≤C.scratch := by
  have rows:=C.rowRoom_le
  have lookupPos:0<2^(C.a*C.M):=Nat.two_pow_pos _
  have rowPos:0<C.rowRoom:=Nat.two_pow_pos _
  dsimp only [endAddress,out,scratch,mask] at room ⊢
  refine ⟨⟨?_,?_,?_,rows,rfl,rows,room,short⟩,?_,?_,?_⟩
  · exact ⟨rowPos,by change C.rowRoom<2^w;omega,le_rfl⟩
  · exact ⟨lookupPos,by change 2^(C.a*C.M)<2^w;omega,by change C.table+2^(C.a*C.M)≤C.table+2^(C.a*C.M)+C.rowRoom+C.rowRoom;omega⟩
  · exact ⟨rowPos,by change C.rowRoom<2^w;omega,by change C.table+_+C.rowRoom≤_;omega⟩
  · change C.table+_+C.rowRoom+C.rows<2^w;omega
  · change C.table+2^(C.a*C.M)≤C.table+2^(C.a*C.M)+C.rowRoom;exact Nat.le_add_right ..
  · rfl

theorem gather_bounds (field : Slot C.r C.q→Expr) (live : ∀s,(field s).Fits w C.scratch)
    (room : C.endAddress<2^w) :
    Gather.Bounds (w:=w) (d:=C.n) (M:=C.M) C.tabs (fun i=>field (slotName C.r C.q i)) C.scratch := by
  intro i
  let p:=2^((C.n*C.N+C.n)*C.M)
  have ppos:0<p:=Nat.two_pow_pos _
  have sm : 2^(C.n*C.N*C.M)≤p:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have up:=Nat.mul_le_mul_right p (show i.val+2≤C.N+1 by omega)
  have top:C.base+(C.N+1)*p≤C.scratch:=by exact (Nat.le_add_right C.table _).trans (Nat.le_add_right _ _)
  have fit:C.scratch<2^w:=by dsimp [endAddress,out] at room;omega
  have dest : C.base+(i.val+1)*p+p≤C.scratch:=by
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact (Nat.add_le_add_left up C.base).trans top
  have app:(C.tabs i).apply.Fits w C.scratch:=
    ⟨ppos,(Nat.le_add_left ..).trans_lt (dest.trans_lt fit),dest⟩
  exact ⟨live _,⟨Nat.two_pow_pos _,by change 2^(C.n*C.N*C.M)<2^w;omega,
    by change C.base+2^(C.n*C.N*C.M)≤C.scratch;omega⟩,app,rfl,rfl⟩

theorem issued (f B Y : ℕ) (mem : Memory w) (room : C.endAddress<2^w) :
    let I:Arena.Image w:=C.gathers
    let J:Arena.Image w:=C.literals f B Y
    let dst:=J.output (I.output mem)
    (I.program.seq J.program).Exec mem dst (8+10*(C.scratch-C.base)) ∧
    (∀i,Static (C.tabs i) (Gather.setField (d:=C.n) i) C.M dst) ∧
    resident (Stencil.lookup C.r C.q C.n C.t f B Y) C.banks C.H C.groups C.M dst ∧
    (∀a,a<C.base ∨ C.scratch≤a→dst a=mem a) ∧ CheapCode (I.program.seq J.program) := by
  dsimp only
  have lt:C.scratch<2^w:=by dsimp only [endAddress,out] at room;omega
  have a:C.base≤C.table:=Nat.le_add_right ..
  have b:C.table≤C.scratch:=by exact (Nat.le_add_right C.table _).trans (Nat.le_add_right _ _)
  have aa:C.base+(C.table-C.base)<2^w:=by omega
  have bb:C.table+(C.scratch-C.table)<2^w:=by omega
  let I:Arena.Image w:=C.gathers
  let J:Arena.Image w:=C.literals f B Y
  obtain ⟨run,gt,tb,keep,cheap,_⟩:=I.pair J mem (Or.inl le_rfl) aa bb
  have orig:=resident_header (Stencil.lookup C.r C.q C.n C.t f B Y) C.banks.source C.table C.bits C.H C.groups
    C.M w (fun _=>0)
  have words : ∀z,C.table≤z→z<C.scratch→J.output (I.output mem) z=J.value z:=tb
  refine ⟨?_,StencilTables.reads C.base C.n C.N C.M _ gt,⟨?_,?_⟩,?_,cheap⟩
  · have len:I.length+J.length=C.scratch-C.base:=by change C.table-C.base+(C.scratch-C.table)=_;omega
    rw [← len]
    intro labels registers cells machine
    exact @run labels registers cells machine
  · intro i
    have below:i.val<2^(C.a*C.M):=i.isLt
    exact (words _ (Nat.le_add_right ..) (by change C.table+i.val<C.table+_+C.rowRoom;omega)).trans (orig.1 i)
  · intro j
    have below:=j.isLt.trans_le C.rowRoom_le
    exact (words _ ((Nat.le_add_right C.table _).trans (Nat.le_add_right _ j.val)) (Nat.add_lt_add_left below _)).trans (orig.2 j)
  · intro u ok
    exact keep u (by change u<C.base∨C.table≤u;omega) (by change u<C.table∨C.scratch≤u;omega)

end Chart
end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil.Layout

end OAI
