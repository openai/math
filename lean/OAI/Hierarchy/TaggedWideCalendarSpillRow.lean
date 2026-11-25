import OAI.Hierarchy.TaggedWidePooledSpill
import OAI.Hierarchy.TaggedWideCalendarSpillGather

namespace OAI
/-! # The full fixed dated spill row on the two actual history words -/
noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles HistoryRoles.Terminal ReportSockets RoleProgram
open scoped Classical BigOperators
set_option quotPrecheck false

private abbrev rowControl {T deg w : ℕ} (P : Dated T) (work : ℕ) (j : Fin T)
    (s : Fin P.sites) (out : Memory w) (f : SiteControls.Field deg) : ℕ :=
  (out (controlAddress P work j s f)).val

variable {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D] (G : Gate)
local notation "V" => SitePins Ex Sel D G
variable {T deg width bits h wr k attempts p e slots : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (inside : ∀f : SiteControls.Field deg,controlAddress P work j s f<G.u)
    (words : Bool→Fin deg→Fin width→SitePins Ex Sel D G⊕Bool) (small : bits≤G.W+1)
    (S : PurchaseSampler) (vtx : Site h (2^wr) k)
local notation "Fib" => Fiber (attempts:=attempts) S vtx
variable (base : ℕ) (roleRoom : ∀a:(Fiber (attempts:=attempts) S vtx),∀t,RoleProgram.labelled S t a.val<2^p) (seat : (Fiber (attempts:=attempts) S vtx)→Fin deg)
local notation "HS" => Fin deg×Fin width

private def spillComparator : BitNetwork F (Fintype.card ((SitePins Ex Sel D G ⊕ (Fin deg × Fin width)) ⊕ (Fin deg × Fin width))) :=
  TurnShelf.physical (r:=slots) base s
    (fun key=>Sum.map (fun a=>Sum.inl (Sum.inl a)) id (G.shelfBit key : V⊕Bool))
    (spillAperture S vtx roleRoom seat (e:=e))

local notation "cmp" => spillComparator (Ex:=Ex) (Sel:=Sel) (D:=D) (F:=F) (slots:=slots) (e:=e) (width:=width)
    G P s S vtx base roleRoom seat
local notation "pas" => passiveNet (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s words
local notation "gath" => spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside words small cmp

/-- One fixed product circuit. The comparator consumes two hidden, uniquely
determined gathers; both the passive and active gates share the same two
externally bound words and the same installed dated control page. -/
def spillRow : BitNetwork F (Fintype.card (SitePins Ex Sel D G)) :=
  WideHost.localFamily (A:=fun _:Bool=>V) (fun b:Bool=>if b then pas else gath) (fun _=>Sum.inl)

theorem spillRow_bill :
    let b:=spillRow (F:=F) (slots:=slots) (e:=e) G P work j s inside words small S vtx base roleRoom seat
    b.cells+b.internal≤deg*deg*(2308*width*(width.log2+2))+
      2*(deg*width+deg*(width*(200*bits+65))+deg*deg*(2308*width*(width.log2+2)))+
      slots*(2308*TurnShelf.width p e*(e+p+2)) := by
  dsimp only [spillRow]
  rw [WideHost.localFamily_size]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
  have pass:=passiveNet_cost (F:=F) G P work j s words
  have turn:=TurnShelf.physical_bill (F:=F) (r:=slots) base s
    (fun key=>Sum.map (fun a:V=>Sum.inl (Sum.inl a)) id (G.shelfBit key))
    (spillAperture («V»:=SitePins Ex Sel D G) (width:=width) S vtx roleRoom seat (e:=e))
  change (cmp).cells+(cmp).internal≤_ at turn
  have h:=spillGather_cost G P work j s inside words small cmp
  omega

private theorem spillRow_product (v : V→Bool) :
    TypedWiring.value (spillRow (F:=F) (slots:=slots) (e:=e) G P work j s inside words small S vtx base roleRoom seat) v=
      TypedWiring.value pas v*TypedWiring.value gath v := by
  rw [spillRow,WideHost.localFamily_eval,Fintype.prod_bool]
  rfl


variable {d edges n r : ℕ} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin P.sites}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord P.sites)
    (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
local notation "L" => B.datedLayout inj pad
local notation "cnt" => (L).bits spill
local notation "mass" => routeLoad (L).routes cnt
local notation "rank" => (L).nativeOrder enum
local notation "old" => (commodityGraph π place).chordWidths spill
local notation "new" => B.actual.chordWidths (routeLoad B.ordinary spill)
local notation "active" => fun b : Bool=>cond b new old
local notation "Port" => (portGraph P.sites).Port s
variable (rest : Widths P.sites) (z : ∀b,State (rest+(cond b (B.actual.chordWidths (routeLoad B.ordinary spill)) ((commodityGraph π place).chordWidths spill))) s)
    (parts : ∀b,PassiveWindow.Parts ((portGraph P.sites).Port s) (Fin deg) width (fun q=>(rest+(cond b (B.actual.chordWidths (routeLoad B.ordinary spill)) ((commodityGraph π place).chordWidths spill))) q.val.1))
    (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val)
local notation "v" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))


include dense in
/-- Exact local carried matrix entry of the installed sparse turn page. -/
theorem spillRow_carry
    (fits : ∀b (q:Port),(rest+active b) q.val.1≤width)
    (columns : width≤2^bits) (room : ∀b q,ChordAperture.room (parts b) q<2^bits)
    (lengthRead : ∀b i q,rowControl (deg:=deg) P work j s out (.inl (b,.inl (i,q)))=(ChordAperture.sizeAt (parts b) i q).val)
    (headRead : ∀b i q,rowControl (deg:=deg) P work j s out (.inl (b,.inr (.inl (i,q))))=(ChordAperture.head (parts b) i q).val)
    (roomRead : ∀b q,rowControl (deg:=deg) P work j s out (.inl (b,.inr (.inr q)))=ChordAperture.room (parts b) q)
    (overlap : ∀i q,rowControl (deg:=deg) P work j s out (.inr ((i,q),0))=(PassiveWindow.header width
      ((parts false).view (fun u:Port=>old u.val.1) i) ((parts true).view (fun u:Port=>new u.val.1) q) (PassiveWindow.linked
        (fun u : Port => rest u.val.1) (fun u : Port => old u.val.1) (fun u : Port => new u.val.1)
        (parts false) (parts true) i q)).val)
    (offset : ∀i q b,rowControl (deg:=deg) P work j s out (.inr ((i,q),if b then 2 else 1))=(PassiveWindow.heads width
      ((parts false).view (fun u:Port=>old u.val.1) i) ((parts true).view (fun u:Port=>new u.val.1) q) b).val)
    (reads : ∀b i q,(parts b).owner i=some q→∀u:Fin ((parts b).width i),
      Sum.elim v id (words b i (u.castLE ((parts b).within i)))=((z b) q).val.testBit ((parts b).base i+u.val))
    (sp : ∀i,Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2)
    (pos : Fin n≃TurnShelf.Positions (L).routes) (col : Fin n→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin P.sites×Fin slots)
    (widths : ∀i,col i 4=cnt (pos i).1)
    (site : ∀u : ProtocolRAMTurnShelf.Live col,(put u).1=(sp (pos u.val).1).visit (pos u.val).2)
    (before : _→Bool→ℕ) (after : Fin edges→Bool→ℕ)
    (role : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)=
      refRole (L).routes before after (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b))
    (start : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)=
      datedStart (L).family (L).edge (L).routes cnt rank (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b))
    (written : ∀f : Fin 5,∀a : Fin P.sites×Fin slots,out (TurnShelf.addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
    (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^G.W)
    (roleFit : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e)
    (shelf : ∀t : Fin slots,∀c : TurnShelf.Control p e,TurnShelf.addr base s t (TurnShelf.projection c).1<G.u)
    (atOld : ∀i (digit:Fin (cnt i)) b (loc : (rowGraph (L).family).vertex i b=s),
      ∃a : Fib,before i b=RoleProgram.labelled S false a.val ∧ (parts false).owner (seat a)=some (sourcePort (L).family cnt
        («v»:=s) ⟨(⟨i,digit⟩,b),by cases b <;>exact loc⟩))
    (atNew : ∀i (u : Fin ((L).routes i).length) (digit : Fin (cnt i)) b
      (loc : (rowGraph (L).edge).vertex (((L).routes i).get u) b=s),
      ∃a : Fib,after (((L).routes i).get u) b=RoleProgram.labelled S true a.val ∧
        (parts true).owner (seat a)=some (sourcePort (L).edge mass
          (datedHopPort (L).edge (L).routes cnt rank i u digit b s loc))) :
    TypedWiring.value (spillRow (F:=F) (slots:=slots) (e:=e) G P work j s inside words small S vtx base roleRoom seat) v=
    LedgerStep.carry (B.onlySpill inj pad spill enum) rest s (z false) (z true) := by
  rw [spillRow_product]
  rw [passiveNet_value G P work j s out ext sel data dense inside rest old new (z false) (z true)
    (parts false) (parts true) words (reads false) (reads true) overlap offset]
  rw [spillGather_value G P work j s out ext sel data dense inside words small cmp parts
    (fun b q=>Nat.testBit (z b q).val) fits columns room lengthRead headRead roomRead reads]
  let bankAt (b : Bool) := Function.uncurry (ChordAperture.canonical (parts b)
    (fun q => Nat.testBit (z b q).val))
  have activeValue : TypedWiring.value (P:=(V⊕HS)⊕HS) cmp (Sum.elim (Sum.elim v (bankAt false)) (bankAt true)) =
      B.onlySpill inj pad spill enum s (splitPortState rest old s (z false)).2
        (splitPortState rest new s (z true)).2 := by
    apply B.physical_onlySpill inj pad spill enum sp pos col put widths site before after role start s
      _ _ base out _ _ _ written fieldFit roleFit extent
    · intro t c
      have peel (pin : V⊕Bool) :
          Sum.elim (Sum.elim (Sum.elim v (bankAt false)) (bankAt true)) id
            (Sum.map (fun a=>Sum.inl (Sum.inl a)) id pin)=Sum.elim v id pin := by cases pin <;> rfl
      exact (peel _).trans (G.shelfBit_read dense out ext sel data _ _ (shelf t c))
    · intro i digit b loc q code off
      obtain ⟨a,roleId,owner⟩ := atOld i digit b loc
      let port : (bitGraph (rowGraph (L).family) cnt).Port s :=
        ⟨(⟨i,digit⟩,b),by cases b <;> exact loc⟩
      exact spillAperture_row S vtx roleRoom seat s (fun _ => rest) active z (L).family cnt false
        (B.spill_input_width inj pad spill) port parts a q v (code.trans roleId) owner
        (fits false (sourcePort (L).family cnt port)) off
    · intro i t digit b loc q code off
      obtain ⟨a,roleId,owner⟩ := atNew i t digit b loc
      let port := datedHopPort (L).edge (L).routes cnt rank i t digit b s loc
      apply spillAperture_row S vtx roleRoom seat s (fun _ => rest) active z (L).edge mass true
        (B.spill_output_width inj pad spill) port parts a q v (code.trans roleId) owner
        (fits true (sourcePort (L).edge mass port))
      simpa only [port,datedHopPort_edge,datedHopPort_offset,←Nat.add_assoc] using off
  rw [activeValue]
  unfold LedgerStep.carry productTable SiteMatrix.identity
  by_cases same : (splitPortState rest new s (z true)).1 = (splitPortState rest old s (z false)).1
  · simp only [ite_eq_left same]
  · simp only [ite_eq_right same]

end Hierarchy.WireTelescope.PassMatrix
end

end OAI
