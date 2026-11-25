import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedSignedStencil
import OAI.Hierarchy.DescentSeedSignedBroadcast

namespace OAI
/-! One executable first-stage signed census shared by every copy, block and histogram reader. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentSharedCableNames
open DescentSIMDLookup DescentSignedCableCodec DescentPackedColony
open Computability.BorderVNP.Crossing Catalyst CorrectionBatch
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k n R s r : ℕ}
    (X : Approximation F k n)
local notation "N" => X.network.copyGraph
local notation "sockets" => 2*256
local notation "C" => Fintype.card (Vertex X)*(2*3)+1
local notation "b" => DescentSignedCableCodec.width 3 256

def book : Fin C→Cell b := Fin.cases (DescentSignedCableCodec.encode (none : Option (Stage.Live 3 256))) fun a=>
  let z:=(socket X).symm a
  DescentSignedCableCodec.encode (panel X z.1 (finTwoEquiv z.2.1) z.2.2.val)

def key (v : Vertex X) (s : Fin sockets) : Fin C :=
  let t : Fin 2×Fin 256:=finProdFinEquiv.symm s
  if h : t.2.val<3 then (socket X (v,t.1,⟨t.2.val,h⟩)).succ else 0

theorem lookup (v : Vertex X) (s : Fin sockets) :
    book X (key X v s)=DescentSignedCableCodec.encode (panelAt X v s) := by
  unfold key
  dsimp only
  split
  · simp [book,panelAt]
  · rename_i large
    simp [book,panelAt,out_of_range X _ _ (Nat.le_of_not_gt large)]

def rowKey {H : ℕ} (v : Fin H→Vertex X) (a : Fin (sockets*H)) : Fin C :=
  let z : Fin sockets×Fin H:=finProdFinEquiv.symm a
  key X (v z.2) z.1

def paddedKey {H : ℕ} (rack : Fin H→Option (Vertex X)) (a : Fin (sockets*H)) : Fin C :=
  let z : Fin sockets×Fin H:=finProdFinEquiv.symm a
  (rack z.2).elim 0 (fun v=>key X v z.1)


private theorem row_address {G M H : ℕ} (s : Fin sockets) (p : Row H G M) :
    (row (sockets*H) G M (finProdFinEquiv (s,p.1),p.2)).val=
      s.val*(H*chunks G M)+(row H G M p).val := by
  change p.2.val+chunks G M*(p.1.val+H*s.val)=s.val*(H*chunks G M)+(p.2.val+chunks G M*p.1.val)
  ring

def setupFor {H groups M w : ℕ} (base : ℕ) (address : Fin (sockets*H)→Fin C) :=
  let n:=(sockets*H)*chunks groups M
  let B:=DescentSeedSignedBroadcast.RAM base C n
  let table:=DescentSeedSignedBroadcast.literals groups M (book X) address
  (DescentStaticWordColumn.program w base table (DescentSeedSignedBroadcast.size C (sockets*H) groups M)).seq
    (scan w (output X base H groups M) n (DescentSeedSignedBroadcast.body B))

def memoryFor {H groups M w : ℕ} (base : ℕ) (address : Fin (sockets*H)→Fin C) (m : Memory w) :=
  let n:=(sockets*H)*chunks groups M
  let B:=DescentSeedSignedBroadcast.RAM base C n
  let table:=DescentSeedSignedBroadcast.literals groups M (book X) address
  let before:=DescentStaticWordColumn.image base table m (DescentSeedSignedBroadcast.size C (sockets*H) groups M)
  ProtocolRAM.image (output X base H groups M) n (DescentSeedSignedBroadcast.body B) before

def setup {H groups M w : ℕ} (base : ℕ) (v : Fin H→Vertex X) :=
  setupFor X (H:=H) (groups:=groups) (M:=M) (w:=w) base (rowKey X v)
def memory {H groups M w : ℕ} (base : ℕ) (v : Fin H→Vertex X) (m : Memory w) :=
  memoryFor X (H:=H) (groups:=groups) (M:=M) base (rowKey X v) m

def clock (base H groups M : ℕ) :=
  let n:=(sockets*H)*chunks groups M
  let B:=DescentSeedSignedBroadcast.RAM base C n
  (4+10*DescentSeedSignedBroadcast.size C (sockets*H) groups M)+(4+n*(2*(DescentSeedSignedBroadcast.body B).work+4))

theorem run {H groups M w : ℕ} (base : ℕ) (v : Fin H→Vertex X) (m : Memory w)
    (bits : b*M≤w) (space : output X base H groups M+(sockets*H)*chunks groups M<2^w) :
    let result:=memory X (groups:=groups) (M:=M) base v m
    (setup X (groups:=groups) (M:=M) base v).Exec m result (clock X base H groups M) ∧
    (∀s,Reads (page X base H groups M s) (fun h (_ : Fin groups)=>DescentSignedCableCodec.encode (panelAt X (v h) s)) M result) ∧
    ∀a,a<base ∨ output X base H groups M+(sockets*H)*chunks groups M≤a→ result a=m a := by
  intro result
  have done:=DescentSeedSignedBroadcast.fresh groups M base (book X) (rowKey X v) m bits space
  refine ⟨done.1,?_,done.2.2⟩
  intro s p
  have reading:=done.2.1 (finProdFinEquiv (s,p.1),p.2)
  rw [row_address] at reading
  change result ((output X base H groups M+s.val*(H*chunks groups M))+(row H groups M p).val)=_
  rw [Nat.add_assoc]
  change result (output X base H groups M+(s.val*(H*chunks groups M)+(row H groups M p).val))=_ at reading
  rw [reading]
  congr 1
  simp [data,rowKey,lookup]

def paddedSetup {H groups M w : ℕ} (base : ℕ) (v : Fin H→Option (Vertex X)) :=
  setupFor X (H:=H) (groups:=groups) (M:=M) (w:=w) base (paddedKey X v)
def paddedMemory {H groups M w : ℕ} (base : ℕ) (v : Fin H→Option (Vertex X)) (m : Memory w) :=
  memoryFor X (H:=H) (groups:=groups) (M:=M) base (paddedKey X v) m


omit [Field F] in
theorem clock_eq (base H groups M : ℕ) :
    clock X base H groups M=8+10*(DescentSeedSignedBroadcast.size C (sockets*H) groups M)+44*((sockets*H)*chunks groups M) :=by
  let B:=DescentSeedSignedBroadcast.RAM base C ((sockets*H)*chunks groups M)
  have work : (DescentSeedSignedBroadcast.body B).work=20:=rfl
  change (4+10*_)+(4+((sockets*H)*chunks groups M)*(2*(DescentSeedSignedBroadcast.body B).work+4))=_
  rw [work];ring

theorem control {H groups M w : ℕ} (base : ℕ) (v : Fin H→Option (Vertex X)) :
    DescentStaticWordColumn.names (paddedSetup X (groups:=groups) (M:=M) (w:=w) base v)=
      15*(DescentSeedSignedBroadcast.size C (sockets*H) groups M+1)+91 ∧
      CheapCode (paddedSetup X (groups:=groups) (M:=M) (w:=w) base v) :=by
  let size:=DescentSeedSignedBroadcast.size C (sockets*H) groups M
  let n:=(sockets*H)*chunks groups M
  let B:=DescentSeedSignedBroadcast.RAM base C n
  let tab:=DescentSeedSignedBroadcast.literals groups M (book X) (paddedKey X v)
  have cheap (t : ℕ) : CheapCode (DescentStaticWordColumn.program w base tab t):=by
    induction t with
    | zero=>apply scan_cheap
    | succ t ih=>exact cheap_seq ih (scan_cheap w _ 1 _)
  change DescentStaticWordColumn.names ((DescentStaticWordColumn.program w base tab size).seq
    (scan w (output X base H groups M) n (DescentSeedSignedBroadcast.body B)))=_ ∧ _
  constructor
  · rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan]
    rfl
  · exact cheap_seq (cheap size) (scan_cheap w _ n _)

theorem padded_run {H groups M w : ℕ} (base : ℕ) (v : Fin H→Option (Vertex X)) (m : Memory w)
    (bits : b*M≤w) (space : output X base H groups M+(sockets*H)*chunks groups M<2^w) :
    let result:=paddedMemory X (groups:=groups) (M:=M) base v m
    (paddedSetup X (groups:=groups) (M:=M) base v).Exec m result (clock X base H groups M) ∧
    (∀s,Reads (page X base H groups M s) (fun h (_ : Fin groups)=>DescentSignedCableCodec.encode ((v h).bind (fun vertex=>panelAt X vertex s))) M result) ∧
    ∀a,a<base ∨ output X base H groups M+(sockets*H)*chunks groups M≤a→ result a=m a := by
  intro result
  have done:=DescentSeedSignedBroadcast.fresh groups M base (book X) (paddedKey X v) m bits space
  refine ⟨done.1,?_,done.2.2⟩
  intro s p
  have reading:=done.2.1 (finProdFinEquiv (s,p.1),p.2)
  rw [row_address] at reading
  change result ((output X base H groups M+s.val*(H*chunks groups M))+(row H groups M p).val)=_
  rw [Nat.add_assoc]
  change result (output X base H groups M+(s.val*(H*chunks groups M)+(row H groups M p).val))=_ at reading
  rw [reading]
  congr 1
  cases h:v p.1 with
  | none=>simp [data,paddedKey,h,book]
  | some vertex=>simp [data,paddedKey,h,lookup]

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
