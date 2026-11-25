import OAI.Hierarchy.DescentCalendarPrivatePages
import OAI.Hierarchy.DescentResetPreparedPeerOrigins
import OAI.Hierarchy.DescentPreparedRootArrays

namespace OAI
/-! # Measured private-root words at the publicly chosen calendar precision -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentGL DescentSIMDLookup DescentPaidResidentCount.Reset
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentFallbackPeriod.Projected.Receiver
open DescentResetHostSize DescentPackedPrivateMenu DescentDenseHostOrder
open DescentDatedAddressBook CandidateFront DescentResetPeerUnionRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "r" => (Z).k-c
local notation "height" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans id_
local notation "cap" => (A).cap
local notation "realWidth" => fieldBits (Z).graph r height (2^r*(2*cap)) (DescentRecordedRotorLayers.width f cap) C (Z).width
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "coords" => B.frame.enough.trans (Nat.sub_le ..)
variable {field t : ℕ} (x : OriginalArrays B pad field)

def originalColumn (v : Fin H) (hi : Block c) (lo : Block r) : Cell t :=
  (x.stencil v hi (Fin.cast (congrArg (fun z=>2^(z-c)) B.keyWidth) lo):ℕ)
def originalCable (v : Fin H) (hi : Block c) (lo : Block r) :=
  x.marks v hi (Fin.cast (congrArg (fun z=>2^(z-c)) B.keyWidth) lo)

private theorem panel_at {nbits t u : ℕ} (dim : u=m) (μ : Layout u) (won : HEq μ B.frame.basis)
    (v : input.V) (hi : Block c) (lo : Block (u-c)) :
    Recorded.realPanel (reset:=B) dim μ nbits t v hi lo=
      Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t v hi (Fin.cast (congrArg (fun z=>2^(z-c)) dim) lo) := by
  subst u
  cases eq_of_heq won
  rfl

theorem original_column_stamp {nbits : ℕ} (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis)
    (source : x.word=originalWord B nbits t) (v : input.V) (hi : Block c) (lo : Block r) :
    originalColumn (t:=t) B x (id_ v) hi lo=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi lo := by
  apply Fin.ext
  rw [panel_at B B.keyWidth μ won]
  unfold originalColumn
  rw [x.localRead,source,original_donor,Fin.cast_val_eq_self]

variable (M nextM metaBits : ℕ) (calendar : List ℕ)
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar
variable (paid : cap=(calendar.take i).prod*256)
variable {w N K Rep hm l tiny : ℕ}
  (a : Receiver (A).degree cap N (Z).n r c H (S.groupCount i) K Rep M hm l tiny field height w)
  (book : RootBook (Z).n r (A).degree (2^r) cap field) (space : a.PreparedFits book)
  (mem : Memory w) (levels : Fin H→ℕ)
local notation "rank_" => fun h j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=(A).degree)
    (book.common a.projectionEnd H) (2^height) (height+2) (a.preparedMid book space mem) h j).val
local notation "headers" => goodInput c field cap (Fintype.card input.V) levels
    (fun v h j=>(((originalColumn (t:=t) B x v h j).val:ℕ):Cell field))
local notation "packet_" => fun (_:Bool) (_:Code r×Option (Fin (2^(Z).n))) v hi=>
  (inputs (fun v h j=>(originalColumn (t:=t) B x v h j).val) x.peers (originalCable B x) rank_ v hi :
    Packet (A).degree (2^r) cap (Z).n r field)
local notation "word_" => privatePageValue (Ht:=height) (board:=(Z).graph) (packet:=(Z).width) (C:=C)
  (layerBits:=DescentRecordedRotorLayers.width f cap) (f:=f) headers packet_

/-- Only a cast along equality of the printed field widths is involved. -/
def calendarRootWord (s : Bool) (ticket : (Z).RootTicket T) (v : Fin H) (hi : Block c) :
    Cell ((phys).privateBits*(capacity*5)) :=
  Fin.cast (congrArg (fun z=>2^(z*(capacity*5))) (calendar_private_width B M nextM field metaBits calendar paid).symm)
    (word_ s ticket v hi)

local notation "vals" => calendarRootWord (t:=t) B x M nextM metaBits calendar paid a book space mem levels
open DescentPackedColony ProtocolRAM

private theorem with_precision {u v host groups lanes w : ℕ} (same : u=v)
    (bank : Bank) (cells : Fin host→Fin groups→Cell u) (ram : Memory w)
    (original : Reads bank cells lanes ram) :
    Reads bank (fun h g=>Fin.cast (congrArg (fun n=>2^n) same) (cells h g)) lanes ram := by
  subst v
  exact original

private theorem frame_cast {a b slots : ℕ} (width : a = b) (j : Fin slots)
    (value : Cell (a*(slots*5))) :
    PrivateEvidence.frame b slots j (Fin.cast (congrArg (fun n => 2^(n*(slots*5))) width) value) =
      PrivateEvidence.frame a slots j value := by
  subst b
  rfl

/-- The addresses before the actor directory hold the already-issued root values
at the calendar precision. This includes the entire last partial batch. -/
theorem calendar_private_readback (before : Memory w)
    (wide : a.preparedEnd book < 2^w)
    (keep : ∀address,address < a.preparedEnd book → before address=a.preparedImage book space mem address)
    (issued : ∀s root,Reads (a.privatePageBank book s root) (word_ s root) M (a.preparedImage book space mem)) :
    ∀s root,Reads (a.privatePageBank book s root) (vals s root) M before := by
  intro s root
  let b:=a.privatePageBank book s root
  have spec:=a.privatePage_room book s root (a.preparedEnd book) le_rfl wide
  have widthEq := congrArg (fun z=>z*(capacity*5)) (calendar_private_width B M nextM field metaBits calendar paid).symm
  have converted : Reads b (vals s root) M (a.preparedImage book space mem) :=
    with_precision widthEq b (word_ s root) (a.preparedImage book space mem) (issued s root)
  intro j
  rw [keep _ ((Nat.add_lt_add_left ((row H (2^c) M j).isLt.trans_le spec.2) _).trans_le spec.1.2.2)]
  exact converted j

local notation "actor" => (Z).sparseActor T tall
local notation "arr" => privatePanelAt B (private_count_eq B)
local notation "host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "slot_" => Fin (2^(m-c))×Fin (2*cap)

theorem calendar_root_origins {nbits p : ℕ} (recorded : B.Recorded p) (hdr : OriginalHeader B pad a book mem)
    (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis) (source : x.word=originalWord B nbits t)
    (short : ∀v hi lo,x.stencil v hi lo < 2^t)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (mass : 2^r*full < 2^nbits) (codes : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*(A).degree))
    (levelRead : ∀v,levels (id_ v)=(Z).placement.b (B.frame.host v))
    (precision : t ≤ field) (depth : r+1 < 2^field) (capFit : cap < 2^field) (unit : 0 < (Z).unit)
    (keys : Fin (stemsCount B)→Fin H→Block c→Cell (field+2))
    (keysRead : ∀(u : host) s (j : slot_),(keys (stemAxis B (s,j)) (((Z).hostFields T tall u.1.2).1) (peerLane B u)).val=
      DescentResetStemKey.code ((oldStemAt B u s j).map (stemTicket B s))) :
    PeerOrigins B pad (⟨keys,actor,vals⟩ : PriorPeerWords B H (phys).privateBits (field+2)) unit arr := by
  have found:=prepared_peer_origins B pad a book space mem hdr x recorded μ levels (originalColumn (t:=t) B x)
    (originalCable B x) unit keys keysRead won level one mass codes active quotaPos degreePos levelRead
    (original_column_stamp B x μ won source) precision depth capFit
    (fun v hi j=>by simp only [originalColumn,Fin.cast_cast,Fin.cast_refl,id_eq,Fin.val_cast_of_lt (short v hi j)])
    (fun v hi j s=>by simp only [originalCable,Fin.cast_cast,Fin.cast_refl,id_eq])
  have rowAt (side : Bool) (root : (Z).RootTicket T) (v : Fin H) (hi : Block c) (j : Fin capacity) :
      PrivateEvidence.frame (phys).privateBits capacity j (vals side root v hi) =
      PrivateEvidence.frame realWidth capacity j (word_ side root v hi) :=
    frame_cast (calendar_private_width B M nextM field metaBits calendar paid).symm j _
  refine ⟨found.stem,found.actors,?_,?_⟩
  · intro old hi side root j
    exact (rowAt side root (old.castLE pad) hi j).trans (found.numbers old hi side root j)
  · intro old hi side root j p seen
    exact (congrArg ((Z).expand T (B.frame.host.symm.toEmbedding.trans input.vertex) p.1.2) (rowAt side root (old.castLE pad) hi j)).trans
      (found.installed old hi side root j p seen)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
