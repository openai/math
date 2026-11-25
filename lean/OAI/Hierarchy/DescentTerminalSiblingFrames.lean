import OAI.Hierarchy.DescentTerminalReachedPanels
import OAI.Hierarchy.DescentTerminalSiblingRAM

namespace OAI
/-! # Running the variable population prefix and clipped sibling lookup in physical memory -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalDenseWindow DescentTerminalDenseHeader DescentTerminalSiteShelves DescentTerminalRecipeRows
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V M B S bits W n stop : ℕ}
local notation "width" => span q t H N A w
local notation "Group" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) M
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def active (L : PackedShelf) (b : Bank) := b=L.residue ∨ b=L.table ∨ ∃f : Fin 8,b=L.columns f ∨ b=L.low f ∨ b=L.high f
def prefixMem (L : PackedShelf) (S : ℕ) (mem : Memory bits) := DescentTerminalDenseHeaderRAM.finalMem L.prefix S mem
def siblingMem (L : PackedShelf) (D : Directory) (S : ℕ) (mem : Memory bits) :=
  image D.texture.base (S+1) (framedExpr L S) (prefixMem L S mem)
def siblingProgram (L : PackedShelf) (D : Directory) (S bits : ℕ) :=
  (DescentTerminalDenseHeaderRAM.program bits S L.prefix).seq (scan bits D.texture.base (S+1) (framedExpr L S))

theorem prefix_field (books : Fin S→Raw) (wide : V≤M) (i : Fin S) :
    (encode 1 M (popProfile books wide i)).val=(books i).1.val := by
  calc
    _ = ∑ j : Fin 1, (popProfile books wide i j).val * (M+1)^j.val :=
      @finFunctionFinEquiv_apply (M+1) 1 (popProfile books wide i)
    _ = _ := by simp [popProfile]

theorem prior_panel (L : PackedShelf) (m : Memory bits) (fit : DescentTerminalDenseHeaderRAM.Fits L.prefix bits S)
    (b : Bank) (before : b.Fits bits L.prefix.rem.base) (j : Word bits) :
    b.read (prefixMem L S m) j=b.read m j := by
  exact DescentTerminalDenseHeaderRAM.before_inputs L.prefix m fit
    ((Nat.add_lt_add_left (Nat.mod_lt j.val before.1) b.base).trans_le before.2.2)

theorem prefix_reads (L : PackedShelf) (m : Memory bits) (books : Fin S→Raw) (enough : V≤M) (mp : 0<M)
    (fit : DescentTerminalDenseHeaderRAM.Fits L.prefix bits S) (reads : DescentTerminalDenseHeaderRAM.Reads L.prefix (popProfile books enough) m)
    (i : Fin S) :
    L.prefix.index.read (prefixMem L S m) (i.val:Word bits)=((population books i.val/M:ℕ):Word bits) ∧
    (DescentTerminalDenseHeaderRAM.previous L.prefix.rem).eval (prefixMem L S m) (i.val:Word bits)=((population books i.val%M:ℕ):Word bits) := by
  have pos : 0<1*M:=by simpa using mp
  obtain ⟨after,run,written,out⟩ := DescentTerminalDenseHeaderRAM.exec_state L.prefix
    (popProfile books enough) pos m fit reads
  have actual : prefixMem L S m = after := DescentTerminalDenseHeaderRAM.physical L.prefix m fit
    (budget:=DescentTerminalDenseHeaderRAM.cost S L.prefix) (post:=fun μ => μ=after) ⟨after,run,rfl⟩
  rw [← actual] at written out
  constructor
  · rw [DescentTerminalDenseHeaderRAM.bank_nat (prefixMem L S m) fit.index (i.isLt.trans_le fit.indexRoom)]
    simpa [DescentTerminalDenseHeaderRAM.wholeVal,pop_prefix] using (out i).1
  · have rem:=DescentTerminalDenseHeaderRAM.previous_reads (prefixMem L S m)
      (DescentTerminalDenseHeaderRAM.remVal (bits:=bits) (popProfile books enough)) fit.rem fit.remRoom
      (by simp [DescentTerminalDenseHeaderRAM.remVal,prior_zero]) (fun j=>(written j).1) i
    simpa [DescentTerminalDenseHeaderRAM.remVal,pop_prefix] using rem

theorem resident_after (L : PackedShelf) (m : Memory bits) (books : Fin S→Raw) (stream : ℕ→Group)
    (enough : V≤M) (short : V*width≤B) (fit : DescentTerminalDenseHeaderRAM.Fits L.prefix bits S)
    (source : Resident L m books stream enough short) (low : ∀b,active L b→b.Fits bits L.prefix.rem.base) :
    Resident L (prefixMem L S m) books stream enough short := by
  constructor
  · intro i d f
    exact (prior_panel L m fit (L.columns f) (low _ (Or.inr (Or.inr ⟨f,Or.inl rfl⟩))) _).trans
      (source.columns i d f)
  · intro f z
    exact (prior_panel L m fit (L.low f) (low _ (Or.inr (Or.inr ⟨f,Or.inr (Or.inl rfl)⟩))) _).trans
      (source.low f z)
  · intro f z
    exact (prior_panel L m fit (L.high f) (low _ (Or.inr (Or.inr ⟨f,Or.inr (Or.inr rfl)⟩))) _).trans
      (source.high f z)
  · intro r
    exact (prior_panel L m fit L.residue (low _ (Or.inl rfl)) _).trans (source.residue r)
  · intro k
    exact (prior_panel L m fit L.table (low _ (Or.inr (Or.inl rfl))) _).trans (source.dictionary k)

private theorem then_scan_priced (A : Procedure bits) (e : Expr) (out n a b : ℕ)
    (m₀ m₁ : Memory bits) (run : A.Exec m₀ m₁ a ∧ CheapCode A)
    (fits : e.Fits bits out) (ends : out+n<2^bits) (price : 4+n*(2*e.work+4)=b) :
    (A.seq (scan bits out n e)).Exec m₀ (image out n e m₁) (a+b) ∧
      CheapCode (A.seq (scan bits out n e)) := by
  obtain ⟨ra,ca⟩ := run
  have rb := @scan_exec bits out n e m₁ fits ends
  rw [←price]
  exact ⟨@Procedure.Exec.then bits A (scan bits out n e) m₀ m₁ (image out n e m₁)
      a (4+n*(2*e.work+4)) (@ra) (@rb),
    @cheap_seq bits A (scan bits out n e) (@ca) (@scan_cheap bits out n e)⟩

theorem sibling_run (L : PackedShelf) (D : Directory) (m : Memory bits)
    (fit : DescentTerminalDenseHeaderRAM.Fits L.prefix bits S) (sources : (framedExpr L S).Fits bits D.texture.base)
    (endAt : D.texture.base+(S+1)<2^bits) :
    (siblingProgram L D S bits).Exec m (siblingMem L D S m) (DescentTerminalDenseHeaderRAM.cost S L.prefix+(4+678*(S+1))) ∧
    CheapCode (siblingProgram L D S bits) := by
  have price : 4+(S+1)*(2*(framedExpr L S).work+4)=4+678*(S+1) := by
    rw [frame_work]
    exact congrArg (fun cost => 4+cost) (Nat.mul_comm (S+1) 678)
  exact then_scan_priced (DescentTerminalDenseHeaderRAM.program bits S L.prefix)
    (framedExpr L S) D.texture.base (S+1) (DescentTerminalDenseHeaderRAM.cost S L.prefix)
    (4+678*(S+1)) m (prefixMem L S m) (DescentTerminalDenseHeaderRAM.exec_any L.prefix m fit)
    sources endAt price

theorem sibling_reached (L : PackedShelf) (D : Directory) (m : Memory bits) (sites : Fin S→Site) (owns : ∀i,(sites i).rows q≤W)
    (books : Fin S→Raw) (stream : ℕ→Group) (enough : V≤M) (mp : 0<M) (short : V*width≤B) (bp : 0<B)
    (fit : DescentTerminalDenseHeaderRAM.Fits L.prefix bits S) (reads : DescentTerminalDenseHeaderRAM.Reads L.prefix (popProfile books enough) m)
    (source : Resident L m books stream enough short) (low : ∀b,active L b→b.Fits bits L.prefix.rem.base)
    (header : Controls (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (n:=n) D (prefixMem L S m) sites owns books)
    (endAt : D.texture.base+(S+1)<2^bits) (stored : D.texture.Fits bits stop) (room : S+1≤D.texture.size)
    (keep : ∀b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift],b.Fits bits D.texture.base) :
    Reached (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (bits:=bits) (S:=S) (pool:=n) D (siblingMem L D S m) sites owns books (fun i=>i.val*B)
      (bitsAt (fun a=>clippedPage (siblings books enough mp stream a) short) bp) bp := by
  let pages : Fin S → Word B := fun i => clippedPage (siblings books enough mp stream i) short
  have words (i : Fin S) : (assemble L).eval (prefixMem L S m) (i.val:Word bits)=
      ((pages i).val:Word bits) := by
    obtain ⟨idx,rem⟩ := prefix_reads L m books enough mp fit reads i
    exact assemble_read L (prefixMem L S m) books stream enough mp short
      (resident_after L m books stream enough short fit source low) i idx rem
  exact reached_expr (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
    (B:=B) (n:=n) (assemble L) D (prefixMem L S m) sites owns books pages bp words header endAt stored room keep

end
end Hierarchy.DescentTerminalVertexFields

end OAI
