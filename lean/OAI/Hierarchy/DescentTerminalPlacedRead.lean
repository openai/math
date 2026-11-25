import OAI.Hierarchy.DescentTerminalPlacedAdmission

namespace OAI
/-! # Admission from the original incoming history at its two physical address bands -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentExteriorShelf DescentExterior DescentGL
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "b_" => afterMeter V S R start
local notation "orig" => takeOff S I b_
local notation "P" => S.terminal.plane
local notation "headBits_" => (P).headBits
local notation "restBits_" => (P).restBits
local notation "bitLanes_" => (P).bitLanes
local notation "exteriors_" => (P).exteriors
local notation "fl" => flagAt (j:=headBits_) (r:=restBits_) (t:=bitLanes_) (e:=exteriors_) orig
local notation "loaded" => input V S I R start header short literal
local notation "end_" => output V S I R start header short literal
local notation "cap_" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
  (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "sz" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)

theorem input_frame (m:Memory bw) {a:ℕ} (outside:a<start ∨ orig≤a) : loaded m a=m a := by
  let marked:=MaskAllocation.marks sz+cap_
  let mask : Memory bw → Memory bw := MaskAllocation.image (blocks:=blocks) (groups:=V.groups) short start
  let l:=DescentTerminalEmitter.Compact.loaded (pageEnd S I b_) I.sources literal m
  have meterBase : (C).base=start+marked:=rfl
  have rise : b_≤pageEnd S I b_:=((rowArena S I b_).start_le 22).trans (stages S I b_).1
  have later_:pageEnd S I b_≤orig:=(stages S I b_).2.1
  have hi:b_=(C).base+cap_+S.sites+S.sites+3:=rfl
  have tmp:(O).usedBits=(C).base+cap_+S.sites+S.sites+1:=rfl
  have dst:(O).deadBits=(C).base+cap_+S.sites+S.sites+2:=rfl
  have frame:=PrivateCounter.rawFinal_frame (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) C O (mask l) a
    (by rcases outside with h|h;exact .inl (by omega);exact .inr (by omega)) (by omega) (by omega)
  have f0:mask l a=l a:=DescentStaticWordColumn.frame start marked _ l a (by omega)
  have f1:l a=m a:=DescentStaticWordColumn.frame (pageEnd S I b_) _ _ m a (by
    change a<pageEnd S I b_ ∨ orig≤a;omega)
  exact frame.trans (f0.trans f1)

theorem history_flags {K T:Type} (m:Memory bw) (early:Earlier S I b_ (C).layout bw)
    (space:last V S I R start<2^bw) (pos:0<bw) (bits:2^headBits_*bitLanes_≤bw)
    (seed:ℕ) (low:seed<start) (x:Fin exteriors_→Plane headBits_ restBits_→Fin bitLanes_→Bool)
    (mix:T→Fin exteriors_→DescentGL.Layout (headBits_+(headBits_+restBits_))) (decode:(K→Bool)→Option T)
    (z:K⊕Hidden exteriors_ headBits_ restBits_ bitLanes_→Bool)
    (good:m seed=0 ↔ ∃c,decode (z∘Sum.inl)=some c)
    (bank_:∀c,decode (z∘Sum.inl)=some c→Loaded orig (mix c) x (z∘Sum.inr) m) :
    (end_ m seed=0 ∧ end_ m fl=0) ↔ ∃c,proposed decode mix x z=some c := by
  have b:start≤(C).base:=Nat.le_add_right ..
  have h:start≤b_:=by change _≤(C).base+cap_+S.sites+S.sites+3;omega
  apply actual_flags S I b_ (C).layout O (loaded m) early space pos bits seed (low.trans_le h) x mix decode z
  · rw [input_frame V S I R start header short literal m (.inl low)];exact good
  · intro c choice col i valid
    have high:orig≤(bank headBits_ restBits_ bitLanes_ exteriors_ orig col.val).base+i:=by
      change orig≤orig+_+_;omega
    rw [input_frame V S I R start header short literal m (.inr high)]
    exact bank_ c choice col i valid

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
