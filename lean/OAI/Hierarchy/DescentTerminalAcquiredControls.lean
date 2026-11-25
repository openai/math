import OAI.Hierarchy.DescentTerminalSiteControls

namespace OAI
/-! # The original primitive book acquires the terminal decoder's controls -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalRowArena DescentTerminalBinPack DescentTerminalSpanBook DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable (S : Shape) (I : Input) (base : ℕ) (O : DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
variable {w W q G V M K a : ℕ}

open DescentTerminalSiteShelves
variable {blocks B t hN nN aN wid verts : ℕ}


variable (origin : ℕ)
local notation "X" => DescentTerminalControlProgram.layout origin S.sites G V M K a verts W B
local notation "A₀" => rowArena S I origin
local notation "values" => portTable (G:=G) (V:=V) (M:=M) («A»:=K) (a:=a) q
local notation "expr" => Book.expression I.parts
theorem acquired_site_controls (m : Memory w) (source : (A₀).Lower w) (low : (A).Lower w) (fit : (A).finish < 2^w)
    (sites : Fin S.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0 < W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ S.terminal.rows)
    (boundaryRoom : (A).boundaries+((A).rows+1) ≤ origin)
    (issued : Book.Issued (A).parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val : Word w) = countTable q j)
    (boundaryROM : ∀ j : Fin ((A).rows+1),m ((A).boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val])
    (poolRows : S.terminal.pool ≤ S.terminal.rows)
    (F : MaskedShelf blocks) (bounds : Suffix.Fits S L F w)
    (assign : I.directory=DescentTerminalControlProgram.earlyBanks X I.parts)
    (inside : (X).finish ≤ base) (space : (X).finish<2^w)
    (data : Fin S.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) (V:=verts))
    (population : ∀i,(data i).1.val=(sites i).nodes) :
    let prep:=(X).after values expr m
    ((X).program w values expr).Exec m prep ((X).time expr) ∧ CheapCode ((X).program w values expr) ∧
      Controls (B:=B) (n:=S.terminal.pool) (L).directory (Suffix.sockets S L ((A).mount prep)) sites perSite data ∧
      ∀j,j < origin ∨ (X).finish ≤ j→prep j=m j := by
  intro prep
  have piece (f : Fin 6) : (I.parts f).fetch.Fits w origin := ⟨source.weights f,source.source f,trivial⟩
  have exprFits : (expr).Fits w origin:=⟨piece 0,piece 1,piece 2,piece 3,piece 4,piece 5⟩
  obtain ⟨go,cheap,reads,keep⟩:=DescentTerminalControlProgram.acquire (verts:=verts) (W:=W) (B:=B) (q:=q)
    origin I.parts sites f labels refs m exprFits (source.source 1) issued space
  have oldBank (b : Bank) (small : b.Fits w origin) (x : Word w) : b.read prep x=b.read m x:=by
    apply keep
    exact .inl ((Nat.add_lt_add_left (Nat.mod_lt _ small.1) _).trans_le small.2.2)
  have issued' : Book.Issued I.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) prep :=
    ⟨fun i f=>(oldBank _ (source.source f) _).trans (issued.source i f),
      fun f d=>(oldBank _ (source.weights f) _).trans (issued.values f d)⟩
  have lo : origin ≤ base := by
    have : origin ≤ (X).finish := by change origin ≤ origin+_+_+_+_;omega
    exact this.trans inside
  have saved:=site_controls S I base O prep low fit sites f labels refs wp perSite paid
    (boundaryRoom.trans lo) issued'
    (fun j=>(oldBank _ source.counts _).trans (countsROM j))
    (fun j=>(keep _ (.inl (by have:=j.isLt;omega))).trans (boundaryROM j))
    poolRows F bounds
    (fun j=>by rw [assign];exact (DescentTerminalControlProgram.early_before X I.parts (source.source 1).2.2 j).trans inside)
    (assign.symm ▸ reads) data population
  exact ⟨go,cheap,saved,keep⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
