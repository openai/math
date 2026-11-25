import OAI.Hierarchy.DescentResetOriginalBooks

namespace OAI
/-! # One fixed execution publishing the public original chronology on an arbitrary memory -/
namespace Hierarchy.DescentResetMixedWordRAM.OriginalDate
open DescentPackedZip DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM DescentResetFieldAssembler OriginalBooks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {b z u t o M w X J K H G : ℕ}

structure Fields (X J : ℕ) where
  «meta» : Fin (X*J)→Expr
  zero : Fin (X*J)→Expr
  halo : Fin (X*J)→Expr
  arg : Fin (X*J)→Expr

structure Date (X J K : ℕ) where
  shelf : Fin J↪Fin K
  kind : Fin J→Fin 2
  header : ℕ
  original : ℕ
  rows : ℕ
  lanes : ℕ
  metaBits : ℕ
  zeroBits : ℕ
  haloBits : ℕ
  argBits : ℕ
  wordBits : ℕ
  fn : Fin 2→WordFn
  fields : Fields X J

namespace Date
variable (L : Date X J K)
def width:=Book.unit L.metaBits L.zeroBits L.haloBits L.argBits*L.lanes
def pages:=OriginalBooks.pages L.metaBits L.zeroBits L.haloBits L.argBits L.wordBits L.lanes L.fn
def tables (p : Fin (X*J)):=OriginalBooks.chart L.metaBits L.zeroBits L.haloBits L.argBits L.wordBits L.lanes L.header L.fn (L.kind (finProdFinEquiv.symm p).2)
def expr (p : Fin (X*J)):=operation (L.tables p) (L.fields.meta p) (L.fields.zero p) (L.fields.halo p) (L.fields.arg p)
def passes:=DescentResetOriginalSlots.passes L.shelf L.original L.rows L.expr
def stop:=DescentResetOriginalSlots.finish L.original L.rows X K
def firstEnd:=OriginalBooks.afterHeader L.metaBits L.zeroBits L.haloBits L.argBits L.lanes L.header
def code (w : ℕ):=(mount L.pages L.width w L.header).seq (ProtocolRAM.program w L.passes)
def ticks:=4+10*(12*2^L.width)+ProtocolRAM.clock L.passes
def mounted (m : Memory w):=after L.pages L.width L.header m
def dst (m : Memory w):=ProtocolRAM.result L.passes (L.mounted m)
structure Room (w : ℕ) : Prop where
  separate : L.firstEnd≤L.original
  endFits : L.stop<2^w
  «meta» : ∀p,(L.fields.meta p).Fits w L.header
  zero : ∀p,(L.fields.zero p).Fits w L.header
  halo : ∀p,(L.fields.halo p).Fits w L.header
  arg : ∀p,(L.fields.arg p).Fits w L.header

theorem space (r : L.Room w) : L.original<2^w:=(Nat.le_add_right ..).trans_lt r.endFits
theorem earlier (r : L.Room w) : L.header≤L.original:=(Nat.le_add_right ..).trans r.separate
theorem gate_room (r : L.Room w) (p : Fin (X*J)) :
    let C:=L.tables p
    let E:=L.fields
    Fits C.mask (E.meta p) (E.zero p) (L.metaBits*7) L.zeroBits L.lanes L.original w ∧
    Fits C.args (E.halo p) (E.arg p) L.haloBits L.argBits L.lanes L.original w ∧
    Fits C.word (C.mask.read (E.meta p) (E.zero p)) (C.args.read (E.halo p) (E.arg p)) 2 (L.haloBits+L.argBits) L.lanes L.original w:=
  OriginalBooks.fits L.fn L.header L.original r.separate (L.space r) _ _ _ _ _
    (ProtocolRAMGeneratedWrite.fits_mono _ (L.earlier r) (r.meta p))
    (ProtocolRAMGeneratedWrite.fits_mono _ (L.earlier r) (r.zero p))
    (ProtocolRAMGeneratedWrite.fits_mono _ (L.earlier r) (r.halo p))
    (ProtocolRAMGeneratedWrite.fits_mono _ (L.earlier r) (r.arg p))

theorem expr_fits (r : L.Room w) (p : Fin (X*J)) : (L.expr p).Fits w L.original:=by
  have final:=(L.gate_room r p).2.2
  exact ⟨final.apply, final.right, final.shift, final.left⟩

theorem any (r : L.Room w) (m : Memory w) :
    (L.code w).Exec m (L.dst m) L.ticks ∧ CheapCode (L.code w) ∧
    ∀a,(a<L.header ∨ L.firstEnd≤a)→
      (∀p : Fin (X*J),a<L.original+(DescentResetOriginalSlots.cell L.shelf p).val*DescentResetOriginalSlots.stride L.rows ∨
        L.original+(DescentResetOriginalSlots.cell L.shelf p).val*DescentResetOriginalSlots.stride L.rows+L.rows≤a)→L.dst m a=m a:=by
  obtain ⟨setup,_,keep,cheap₀,_⟩:=OriginalBooks.installed (b:=L.metaBits) (z:=L.zeroBits) (u:=L.haloBits) (t:=L.argBits)
    (o:=L.wordBits) (M:=L.lanes) L.fn L.header m (r.separate.trans_lt (L.space r))
  have swept : (ProtocolRAM.program w L.passes).Exec (L.mounted m) (L.dst m) (ProtocolRAM.clock L.passes) :=
    @ProtocolRAM.program_exec w L.passes (L.mounted m)
      (DescentResetOriginalSlots.safe L.shelf L.original L.rows L.expr (L.expr_fits r) r.endFits)
  refine ⟨@Procedure.Exec.then w (mount L.pages L.width w L.header) (ProtocolRAM.program w L.passes)
      m (L.mounted m) (L.dst m) (4+10*(12*2^L.width)) (ProtocolRAM.clock L.passes) (@setup) (@swept),
    @cheap_seq w _ _ (@cheap₀) (@program_cheap w L.passes), ?_⟩
  intro a outside rows
  exact (DescentResetOriginalSlots.frame L.shelf L.original L.rows L.expr (L.mounted m) a rows).trans (keep a outside)

theorem frame_slot (r : L.Room w) (m : Memory w) (x : Fin X) (j : Fin K) (absent : ∀s,L.shelf s≠j) (i : Fin L.rows) :
    let addr:=DescentResetOriginalSlots.offset L.original L.rows K x.val j.val+i.val
    L.dst m addr=m addr:=by
  intro a
  have keep:=DescentResetOriginalSlots.frame_slot L.shelf L.original L.rows L.expr (L.mounted m) x j absent i
  have above : L.original ≤ a :=
    (Nat.le_add_right L.original ((x.val*K+j.val)*DescentResetOriginalSlots.stride L.rows)).trans
      (Nat.le_add_right _ i.val)
  exact keep.trans (DescentOrdinaryAtomFieldRAM.ROM.frame L.pages L.width L.header m a (.inr (r.separate.trans above)))

theorem invoice (_r : L.Room w) (bound : ℕ) (price : ∀p,(L.fields.meta p).work+(L.fields.zero p).work+(L.fields.halo p).work+(L.fields.arg p).work+33≤bound) :
    L.ticks≤4+10*(12*2^L.width)+(4+(X*J)*(4+L.rows*(2*bound+4))) ∧
    DescentStaticWordColumn.names (L.code w)≤15*(12*2^L.width+1)+(15+X*J*(11+4*bound)):=by
  have ex (p : Fin (X*J)) : (L.expr p).work≤bound:=(Book.work ..).le.trans (price p)
  have each (p : Pass) (seen : p∈L.passes) : p.rows≤L.rows ∧ p.term.work≤bound:=by
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp seen
    exact ⟨le_rfl,ex i⟩
  have len : L.passes.length=X*J:=by simp [passes,DescentResetOriginalSlots.passes]
  have time:=ProtocolRAM.clock_le L.passes L.rows bound each
  rw [len] at time
  have names (ps : List Pass) (lim : ∀p∈ps,p.term.work≤bound) :
      DescentStaticWordColumn.names (ProtocolRAM.program w ps)≤15+ps.length*(11+4*bound):=by
    induction ps with
    | nil=>simp [ProtocolRAM.program,DescentStaticWordColumn.names_scan,Expr.work]
    | cons a ps ih=>
      have ha:=lim a (.head _)
      have bound' :=ih (fun p hp=>lim p (.tail _ hp))
      rw [ProtocolRAM.program,DescentStaticWordColumn.names_seq,Pass.procedure,DescentStaticWordColumn.names_scan,
        List.length_cons,Nat.succ_mul ps.length (11+4*bound)]
      omega
  have bill:=names L.passes (fun p seen=>(each p seen).2)
  rw [len] at bill
  have tableCost : DescentStaticWordColumn.names (mount L.pages L.width w L.header)=15*(12*2^L.width+1) :=
    DescentStaticWordColumn.names_mount w L.header (contents L.pages L.width) (12*2^L.width)
  refine ⟨Nat.add_le_add_left time _, ?_⟩
  rw [code,DescentStaticWordColumn.names_seq,tableCost]
  exact Nat.add_le_add_left bill _

end Date
end
end Hierarchy.DescentResetMixedWordRAM.OriginalDate

end OAI
