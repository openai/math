import OAI.Hierarchy.DescentTerminalAcquiredControls
import OAI.Hierarchy.DescentTerminalPlacedRead

namespace OAI
/-! # The original control acquisition remains readable after the fixed terminal startup -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalRowArena DescentTerminalBinPack DescentTerminalSpanBook DescentTerminalVertexFields
open DescentTerminalSiteShelves ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w W q G V M K a B t hN nN aN wid verts blocks count:ℕ}
variable (venue:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:count*span venue.publicArity venue.roles venue.privateWords
  venue.nodes venue.addresses venue.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources) (origin:ℕ)
local notation "C" => meter venue R start
local notation "base" => afterMeter venue S R start
local notation "O" => registers venue S R start header
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "loaded" => input venue S I R start header short literal
local notation "A₀" => rowArena S I origin
local notation "X" => DescentTerminalControlProgram.layout origin S.sites G V M K a verts W B
local notation "values" => portTable (G:=G) (V:=V) (M:=M) («A»:=K) (a:=a) q
local notation "expr" => Book.expression I.parts

theorem placed_acquired_banks (m:Memory w) (source:(A₀).Lower w)
    (early:Earlier S I base (C).layout w) (wordRoom:last venue S I R start<2^w)
    (sites:Fin S.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels:∀i,(sites i).Name→Word a) (refs:∀i,(sites i).Arg→Word a)
    (wp:0<W) (perSite:∀i,(sites i).rows q≤W)
    (paid:purchased W (counts (q:=q) sites)≤S.terminal.rows)
    (boundaryRoom:(A).boundaries+((A).rows+1)≤origin)
    (issued:Book.Issued I.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM:∀j:Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val:Word w)=countTable q j)
    (boundaryROM:∀j:Fin ((A).rows+1),m ((A).boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val])
    (poolRows:S.terminal.pool≤S.terminal.rows)
    (assign:I.directory=DescentTerminalControlProgram.earlyBanks X I.parts)
    (inside:(X).finish≤ start)
    (data:Fin S.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) (V:=verts))
    (population:∀i,(data i).1.val=(sites i).nodes)
    (between:Memory w)
    (partReads:∀(j:Fin 6) (u:Word w),
      (I.parts j).source.read between u=(I.parts j).source.read ((X).after values expr m) u ∧
      (I.parts j).weights.read between u=(I.parts j).weights.read ((X).after values expr m) u)
    (directoryReads:∀(j:Fin 8) (u:Word w),
      (I.directory j).read between u=(I.directory j).read ((X).after values expr m) u)
    (countReads:∀u:Word w,(A).countTable.read between u=(A).countTable.read ((X).after values expr m) u)
    (boundaryReads:∀i:Fin ((A).rows+1),between ((A).boundaries+i.val)=(X).after values expr m ((A).boundaries+i.val)) :
    let prep:=(X).after values expr m
    ((X).program w values expr).Exec m prep ((X).time expr) ∧ CheapCode ((X).program w values expr) ∧
      Controls (B:=B) (n:=S.terminal.pool) (L).directory (Suffix.sockets S L ((A).mount (loaded between))) sites perSite data ∧
      ∀j,j<origin ∨ (X).finish≤j→prep j=m j := by
  intro prep
  have layers:=stages S I base
  have room:(A).finish<2^w := (layers.1.trans (layers.2.1.trans (layers.2.2.1.trans
    (layers.2.2.2.1.trans layers.2.2.2.2)))).trans_lt wordRoom
  have inputs:start≤base:=by change start≤ start+_+_+_+_+_;omega
  have pre:origin≤(X).finish:=by change origin≤origin+_+_+_+_;omega
  have before:origin≤ start:=pre.trans inside
  have space:(X).finish<2^w:=(inside.trans (inputs.trans ((A).start_le 22))).trans_lt room
  have small (j:Fin 6):(I.parts j).fetch.Fits w origin:=⟨source.weights j,source.source j,trivial⟩
  have fits:(expr).Fits w origin:=⟨small 0,small 1,small 2,small 3,small 4,small 5⟩
  obtain ⟨go,cheap,reads,keep⟩:=DescentTerminalControlProgram.acquire (verts:=verts) (W:=W) (B:=B) (q:=q)
    origin I.parts sites f labels refs m fits (source.source 1) issued space
  have same (b:Bank) (stop:b.base+b.size≤(X).finish) (u:Word w):
      b.read (loaded between) u=b.read between u :=
    input_frame venue S I R start header short literal between (.inl
      ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (stop.trans inside)))
  have original (b:Bank) (lo:b.Fits w origin) (u:Word w)
      (readback:b.read between u=b.read prep u):b.read (loaded between) u=b.read m u :=
    (same b (lo.2.2.trans pre) u).trans (readback.trans
      (keep _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ lo.1) _).trans_le lo.2.2))))
  have receipt:Book.Issued I.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) (loaded between) :=
    ⟨fun i j=>(original _ (source.source j) _ (partReads j _).1).trans (issued.source i j),
     fun j u=>(original _ (source.weights j) _ (partReads j _).2).trans (issued.values j u)⟩
  have beforeBoundary (j:Fin ((A).rows+1)) :
      (loaded between) ((A).boundaries+j.val)=m ((A).boundaries+j.val) := by
    have hi: (A).boundaries+j.val<origin := (Nat.add_lt_add_left j.isLt _).trans_le boundaryRoom
    exact (input_frame venue S I R start header short literal between (.inl (hi.trans_le before))).trans
      ((boundaryReads j).trans (keep _ (.inl hi)))
  have directory (j:Fin 8):(I.directory j).base+(I.directory j).size≤(X).finish:=by
    rw [assign]
    exact DescentTerminalControlProgram.early_before X I.parts (source.source 1).2.2 j
  have deposited:DescentTerminalControlProgram.Reads q W B verts sites I.directory prep:=assign.symm ▸ reads
  have actual:=deposited.transfer (n:=loaded between) (fun j u=>(same _ (directory j) u).trans (directoryReads j u))
  refine ⟨go,cheap,?_,keep⟩
  exact site_controls S I base O (loaded between) early.old room sites f labels refs wp perSite paid
    (boundaryRoom.trans (before.trans inputs)) receipt
    (fun j=>(original _ source.counts _ (countReads _)).trans (countsROM j))
    (fun j=>(beforeBoundary j).trans (boundaryROM j))
    poolRows (C).layout (suffix_room S I base (C).layout O early wordRoom)
    (fun j=>(directory j).trans (inside.trans inputs)) actual data population

/-- A low-address frame provides the individual bank equalities as a sufficient condition. -/
theorem placed_acquired_after (m:Memory w) (source:(A₀).Lower w)
    (early:Earlier S I base (C).layout w) (wordRoom:last venue S I R start<2^w)
    (sites:Fin S.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels:∀i,(sites i).Name→Word a) (refs:∀i,(sites i).Arg→Word a)
    (wp:0<W) (perSite:∀i,(sites i).rows q≤W)
    (paid:purchased W (counts (q:=q) sites)≤S.terminal.rows)
    (boundaryRoom:(A).boundaries+((A).rows+1)≤origin)
    (issued:Book.Issued I.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM:∀j:Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val:Word w)=countTable q j)
    (boundaryROM:∀j:Fin ((A).rows+1),m ((A).boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val])
    (poolRows:S.terminal.pool≤S.terminal.rows)
    (assign:I.directory=DescentTerminalControlProgram.earlyBanks X I.parts)
    (inside:(X).finish≤ start)
    (data:Fin S.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) (V:=verts))
    (population:∀i,(data i).1.val=(sites i).nodes)
    (between:Memory w) (retained:∀x,x<(X).finish→between x=(X).after values expr m x) :
    let prep:=(X).after values expr m
    ((X).program w values expr).Exec m prep ((X).time expr) ∧ CheapCode ((X).program w values expr) ∧
      Controls (B:=B) (n:=S.terminal.pool) (L).directory (Suffix.sockets S L ((A).mount (loaded between))) sites perSite data ∧
      ∀j,j<origin ∨ (X).finish≤j→prep j=m j := by
  have pre:origin≤(X).finish:=by change origin≤origin+_+_+_+_;omega
  have fixed (b:Bank) (end_:b.base+b.size≤(X).finish) (u:Word w):
      b.read between u=b.read ((X).after values expr m) u :=
    retained _ ((Nat.add_lt_add_left (Nat.mod_lt u.val (Nat.two_pow_pos _)) _).trans_le end_)
  apply placed_acquired_banks venue S I R start header short literal origin m source early wordRoom
    sites f labels refs wp perSite paid boundaryRoom issued countsROM boundaryROM poolRows assign
    inside data population between
  · exact fun j u=>⟨fixed _ ((source.source j).2.2.trans pre) u,fixed _ ((source.weights j).2.2.trans pre) u⟩
  · intro j u
    apply fixed
    rw [assign]
    exact DescentTerminalControlProgram.early_before X I.parts (source.source 1).2.2 j
  · exact fixed _ (source.counts.2.2.trans pre)
  · exact fun i=>retained _ ((Nat.add_lt_add_left i.isLt _).trans_le (boundaryRoom.trans pre))

/-- The placement without intervening writes specializes to the end of the acquisition itself. -/
theorem placed_acquired_controls (m:Memory w) (source:(A₀).Lower w)
    (early:Earlier S I base (C).layout w) (wordRoom:last venue S I R start<2^w)
    (sites:Fin S.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels:∀i,(sites i).Name→Word a) (refs:∀i,(sites i).Arg→Word a)
    (wp:0<W) (perSite:∀i,(sites i).rows q≤W)
    (paid:purchased W (counts (q:=q) sites)≤S.terminal.rows)
    (boundaryRoom:(A).boundaries+((A).rows+1)≤origin)
    (issued:Book.Issued I.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM:∀j:Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val:Word w)=countTable q j)
    (boundaryROM:∀j:Fin ((A).rows+1),m ((A).boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val])
    (poolRows:S.terminal.pool≤S.terminal.rows)
    (assign:I.directory=DescentTerminalControlProgram.earlyBanks X I.parts)
    (inside:(X).finish≤ start)
    (data:Fin S.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) (V:=verts))
    (population:∀i,(data i).1.val=(sites i).nodes) :
    let prep:=(X).after values expr m
    ((X).program w values expr).Exec m prep ((X).time expr) ∧ CheapCode ((X).program w values expr) ∧
      Controls (B:=B) (n:=S.terminal.pool) (L).directory (Suffix.sockets S L ((A).mount (loaded prep))) sites perSite data ∧
      ∀j,j<origin ∨ (X).finish≤j→prep j=m j :=
  placed_acquired_after venue S I R start header short literal origin m source early wordRoom
    sites f labels refs wp perSite paid boundaryRoom issued countsROM boundaryROM poolRows assign
    inside data population ((X).after values expr m) (fun _ _=>rfl)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
