import OAI.Hierarchy.DescentTerminalPositionGather
import OAI.Hierarchy.DescentTerminalVertexPanelRAM

namespace OAI
/-! # Actual native collection and framing of the primitive scalar field shelves -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalSpanBook DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W S B n bits stop : ℕ}
local notation "width" => span q t H N A w
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def pageRow (S : ℕ) (L : Shelf) : Expr := .branch .lt .row (.lit S) (row L) (.lit 0)
def rendered (S : ℕ) (L : Shelf) (D : Directory) (m : Memory bits) := image D.texture.base (S+1) (pageRow S L) m

theorem render (L : Shelf) (D : Directory) (m : Memory bits)
    (fit : (pageRow S L).Fits bits D.texture.base) (endAt : D.texture.base+(S+1)<2^bits) :
    (scan bits D.texture.base (S+1) (pageRow S L)).Exec m (rendered S L D m) (4+234*(S+1)) ∧
      CheapCode (scan bits D.texture.base (S+1) (pageRow S L)) := by
  have tariff : 4+(S+1)*(2*(pageRow S L).work+4) = 4+234*(S+1) := by
    change 4+(S+1)*234 = 4+234*(S+1)
    rw [Nat.mul_comm (S+1) 234]
  refine ⟨?_,@scan_cheap bits D.texture.base (S+1) (pageRow S L)⟩
  rw [← tariff]
  exact @scan_exec bits D.texture.base (S+1) (pageRow S L) m fit endAt

theorem written_expr (e : Expr) (D : Directory) (m : Memory bits) (pages : Fin S→Word B)
    (words : ∀i:Fin S,e.eval m (i.val:Word bits)=((pages i).val:Word bits)) (endAt : D.texture.base+(S+1)<2^bits) (j : Fin (S+1)) :
    image D.texture.base (S+1) (.branch .lt .row (.lit S) e (.lit 0)) m (D.texture.base+j.val)=((aligned pages j.val).val:Word bits) := by
  rw [DescentTerminalDenseHeaderRAM.at_image D.texture.base (.branch .lt .row (.lit S) e (.lit 0)) m j]
  have jr : j.val<2^bits:=by have:=j.isLt;omega
  have sr : S<2^bits:=by omega
  have cmp : ((j.val:Word bits) < (S:Word bits)) ↔ j.val<S := by
    rw [Fin.lt_def,Fin.val_cast_of_lt jr,Fin.val_cast_of_lt sr]
  by_cases live : j.val<S
  · simpa only [Expr.eval,Comparison.test,decide_eq_true_eq,cmp,ite_eq_left live,aligned,dite_eq_left live]
      using words ⟨j.val,live⟩
  · simp [Expr.eval,Comparison.test,cmp,live,aligned]

theorem written_by (L : Shelf) (D : Directory) (m : Memory bits) (pages : Fin S→Word B)
    (words : ∀i:Fin S,(row L).eval m (i.val:Word bits)=((pages i).val:Word bits)) (endAt : D.texture.base+(S+1)<2^bits) (j : Fin (S+1)) :
    rendered S L D m (D.texture.base+j.val)=((aligned pages j.val).val:Word bits) :=
  written_expr (row L) D m pages words endAt j

theorem written (L : Shelf) (D : Directory) (m : Memory bits) (rows : Fin S→Rows) (fit : V*width≤B)
    (shelves : Mounted L m rows fit) (endAt : D.texture.base+(S+1)<2^bits) (j : Fin (S+1)) :
    rendered S L D m (D.texture.base+j.val)=((aligned (fun i=>weave (rows i) fit) j.val).val:Word bits) :=
  written_by L D m _ (row_read L m rows fit shelves) endAt j

structure Controls (L : Directory) (m : Memory bits) (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
    (z : Fin S→Raw) : Prop where
  span : ∀i : Fin n,L.span.Facts sites i fit m
  ports : ∀i,L.ports.read m (i.val:Word bits)=((sites i).portRows q:Word bits)
  count : ∀i,L.count.read m (i.val:Word bits)=((z i).1.val:Word bits)
  first : ∀i : Fin S,L.firstWord.read m (i.val:Word bits)=(i.val:Word bits)
  skip : ∀i : Fin S,L.skip.read m (i.val:Word bits)=0
  countROM : ∀j : Fin (V+1),L.countShift.read m (j.val:Word bits)=((j.val*((W+1)*(B*(2^B*2^B))):ℕ):Word bits)
  modeROM : ∀j : Fin (W+1),L.modeShift.read m (j.val:Word bits)=((j.val*(B*(2^B*2^B)):ℕ):Word bits)
  skipROM : ∀j : Fin B,L.skipShift.read m (j.val:Word bits)=((j.val*(2^B*2^B):ℕ):Word bits)
  wordROM : ∀j : Word B,L.wordShift.read m (j.val:Word bits)=((j.val*2^B:ℕ):Word bits)


theorem reached_expr (e : Expr) (D : Directory) (m : Memory bits) (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
    (books : Fin S→Raw) (pages : Fin S→Word B) (bp : 0<B)
    (words : ∀i:Fin S,e.eval m (i.val:Word bits)=((pages i).val:Word bits)) (header : Controls (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (n:=n) D m sites fit books)
    (endAt : D.texture.base+(S+1)<2^bits) (stored : D.texture.Fits bits stop) (room : S+1≤D.texture.size)
    (keep : ∀b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift],b.Fits bits D.texture.base) :
    Reached (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (bits:=bits) (B:=B) (S:=S) (pool:=n) D (image D.texture.base (S+1) (.branch .lt .row (.lit S) e (.lit 0)) m) sites fit books (fun i=>i.val*B) (bitsAt pages bp) bp := by
  have early (b : Bank) (mem : b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift]) (j : Word bits) : b.read (image D.texture.base (S+1) (.branch .lt .row (.lit S) e (.lit 0)) m) j=b.read m j := by
    have first:=(keep b mem).1;have last:=(keep b mem).2.2
    have:=Nat.mod_lt j.val first
    unfold Bank.read
    have below : b.base+j.val%b.size<D.texture.base := by omega
    simp [image,fillSegment,not_le.mpr below]
  have word (j : Fin (S+1)) : D.texture.read (image D.texture.base (S+1) (.branch .lt .row (.lit S) e (.lit 0)) m) (j.val:Word bits)=
      ((aligned pages j.val).val:Word bits) := by
    rw [DescentTerminalDenseHeaderRAM.bank_nat _ stored (j.isLt.trans_le room)]
    exact written_expr e D m pages words endAt j
  constructor
  · intro i
    obtain ⟨a,b⟩:=header.span i
    exact ⟨(early _ (by simp) _).trans a,fun v u h=>⟨(early _ (by simp) _).trans (b v u h).1,(early _ (by simp) _).trans (b v u h).2⟩⟩
  · exact fun i=>(early _ (by simp) _).trans (header.ports i)
  · exact fun i=>(early _ (by simp) _).trans (header.count i)
  · intro i;simpa [Nat.mul_div_cancel _ bp] using (early _ (by simp) _).trans (header.first i)
  · intro i;simpa using (early _ (by simp) _).trans (header.skip i)
  · intro i;simpa [Nat.mul_div_cancel _ bp,dense_page] using word i.castSucc
  · intro i;simpa [Nat.mul_div_cancel _ bp,dense_page] using word i.succ
  · exact fun j=>(early _ (by simp) _).trans (header.countROM j)
  · exact fun j=>(early _ (by simp) _).trans (header.modeROM j)
  · exact fun j=>(early _ (by simp) _).trans (header.skipROM j)
  · exact fun j=>(early _ (by simp) _).trans (header.wordROM j)

theorem reached_by (L : Shelf) (D : Directory) (m : Memory bits) (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
    (books : Fin S→Raw) (pages : Fin S→Word B) (bp : 0<B)
    (words : ∀i:Fin S,(row L).eval m (i.val:Word bits)=((pages i).val:Word bits)) (header : Controls (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (n:=n) D m sites fit books)
    (endAt : D.texture.base+(S+1)<2^bits) (stored : D.texture.Fits bits stop) (room : S+1≤D.texture.size)
    (keep : ∀b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift],b.Fits bits D.texture.base) :
    Reached (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (bits:=bits) (B:=B) (S:=S) (pool:=n) D (rendered S L D m) sites fit books (fun i=>i.val*B) (bitsAt pages bp) bp :=
  reached_expr (row L) D m sites fit books pages bp words header endAt stored room keep

theorem reached (L : Shelf) (D : Directory) (m : Memory bits) (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
    (books : Fin S→Raw) (rows : Fin S→Rows) (localFit : V*width≤B) (bp : 0<B)
    (actual : Mounted L m rows localFit) (header : Controls (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (n:=n) D m sites fit books)
    (endAt : D.texture.base+(S+1)<2^bits) (stored : D.texture.Fits bits stop) (room : S+1≤D.texture.size)
    (keep : ∀b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift],b.Fits bits D.texture.base) :
    Reached (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (bits:=bits) (B:=B) (S:=S) (pool:=n) D (rendered S L D m) sites fit books (fun i=>i.val*B) (bitsAt (fun i=>weave (rows i) localFit) bp) bp :=
  reached_by L D m sites fit books _ bp (row_read L m rows localFit actual) header endAt stored room keep

end
end Hierarchy.DescentTerminalVertexFields

end OAI
