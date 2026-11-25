import OAI.Hierarchy.DescentResetStemProjectGather
import OAI.Hierarchy.DescentResetStemProjectBank
import OAI.Hierarchy.DescentOverlapRAM
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Project the previous packed receiver rows onto each low block at the new pitch -/
namespace Hierarchy.DescentResetStemProject
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {N H G X a A M w : ℕ}

def gathered (base N H G X A : ℕ) := dense base (N*(H*chunks (G*X) A))
def overlapBase (base N H G X A : ℕ) :=base+(gathered base N H G X A).size
def converted (base N H G X a A M : ℕ) :=
  dense (Overlap.dest (overlapBase base N H G X A) (N*H) (G*X) A (M*X) a)
    ((N*H)*chunks (G*X) (M*X))
def reshapeBase (base N H G X a A M : ℕ) :=
  let src:=converted base N H G X a A M
  src.base+src.size
def out (base N H G X a A M : ℕ) :=
  DescentVectorBookReshape.output (reshapeBase base N H G X a A M) N H 1 G X a M
def endAddress (base N H G X a A M : ℕ) :=pageEnd (out base N H G X a A M) N H G M X
def bank (base N H G X a A M : ℕ) (q : Fin N) (x : Fin X) :=
  page (out base N H G X a A M) H G M X q x

theorem extent (base N H G X a A M : ℕ) :
    endAddress base N H G X a A M=base+endAddress 0 N H G X a A M := by
  simp only [endAddress,pageEnd,out,DescentVectorBookReshape.output,reshapeBase,converted,
    Overlap.dest,Overlap.dictBase,overlapBase,gathered,dense,Bank.size,Nat.zero_add,Nat.add_assoc]

section
variable (base H G X a A M : ℕ) (src : Fin N→Bank)
local notation "copy" => gathered base N H G X A
local notation "middle" => overlapBase base N H G X A
local notation "packed" => converted base N H G X a A M
local notation "books" => reshapeBase base N H G X a A M
local notation "dst" => out base N H G X a A M
local notation "overSize" => Overlap.finish middle (N*H) (G*X) A (M*X) a
local notation "finish" => endAddress base N H G X a A M

def postProgram (w : ℕ) :=
  (Overlap.program middle (N*H) (G*X) A (M*X) a w copy).seq
    (DescentVectorBookReshape.program N H 1 G X a M books dst w packed)

def postTicks :=
  Overlap.ticks middle (N*H) (G*X) A (M*X) a copy+DescentVectorBookReshape.ticks N H 1 G X a M

def postImage (m : Memory w) :=
  DescentVectorBookReshape.result N H 1 G X a M books dst packed
    (Overlap.result middle (N*H) (G*X) A (M*X) a copy m)

def program (w : ℕ) :=
  (ProtocolRAM.program w (gatherPasses src H (G*X) A base)).seq
    ((Overlap.program middle (N*H) (G*X) A (M*X) a w copy).seq
      (DescentVectorBookReshape.program N H 1 G X a M books dst w packed))

def ticks :=
  clock (gatherPasses src H (G*X) A base)+
    (Overlap.ticks middle (N*H) (G*X) A (M*X) a copy+DescentVectorBookReshape.ticks N H 1 G X a M)

def image (m : Memory w) :=
  DescentVectorBookReshape.result N H 1 G X a M books dst packed
    (Overlap.result middle (N*H) (G*X) A (M*X) a copy (gatherImage src H (G*X) A base m))

theorem regions :
    base+N*(H*chunks (G*X) A)≤ middle ∧ middle≤(packed).base ∧
    overSize≤books ∧ books≤dst ∧ dst+N*DescentVectorBookReshape.rows H 1 G X M≤finish := by
  refine ⟨Nat.add_le_add_left (dense_capacity ..) base,?_,?_,?_,Nat.le_add_right ..⟩
  · change middle≤ middle+_+_
    omega
  · exact Nat.add_le_add_left (dense_capacity ..) _
  · exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)

private theorem vector_cheap (w : ℕ) :
    CheapCode (DescentVectorBookReshape.program N H 1 G X a M books dst w packed) :=
  @cheap_seq w _ _
    (@DescentStaticWordColumn.cheap w books (DescentVectorBookReshape.words N H 1 G X a M)
      (DescentVectorBookReshape.cells N H 1 G X a M))
    (@scan_cheap w dst (N*DescentVectorBookReshape.rows H 1 G X M)
      (DescentScalarBookReshape.expression (DescentVectorBookReshape.layout N H 1 G X a M books packed)))

theorem post_any (om : Memory w) (hm : 0<M) (hx : 0<X) (room : finish<2^w) :
    let final:=postImage (N:=N) base H G X a A M om
    (postProgram (N:=N) base H G X a A M w).Exec om final (postTicks (N:=N) base H G X a A M) ∧
      (∀u,u< middle ∨ finish≤u→final u=om u) ∧ CheapCode (postProgram (N:=N) base H G X a A M w) := by
  obtain ⟨_,r₂,r₃,r₄,r₅⟩:=regions (N:=N) base H G X a A M
  have chain : middle≤books:=r₂.trans ((Nat.le_add_right ..).trans r₃)
  have bookInside : books<2^w:=r₄.trans_lt ((Nat.le_add_right ..).trans_lt (r₅.trans_lt room))
  obtain ⟨runOld,fr,cheap⟩:=Overlap.any middle (N*H) (G*X) A (M*X) a copy om
    (dense_fits _ _ (chain.trans_lt bookInside)) (r₃.trans_lt bookInside)
  have counts:=chunks_group G M X hm hx
  have capacity : N*DescentVectorBookReshape.sourceWords H 1 G M≤(packed).size := by
    have size : (N*H)*chunks (G*X) (M*X) ≤ (packed).size := dense_capacity _ _
    simpa only [DescentVectorBookReshape.sourceWords,one_mul,counts,Nat.mul_assoc] using size
  have fit:=DescentVectorBookReshape.arranged books packed (dense_fits _ _ bookInside) capacity (r₅.trans_lt room)
  let pm:=Overlap.result middle (N*H) (G*X) A (M*X) a copy om
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then runOld (DescentVectorBookReshape.exec books dst packed pm fit) machine pc reg pub exit rom advice cfg raw enter same,?_,
    @cheap_seq w _ _ (@cheap) (@vector_cheap N base H G X a A M w)⟩
  rintro u (h|h)
  · exact (DescentVectorBookReshape.frame pm u (.inl (h.trans_le chain)) (.inl (h.trans_le (chain.trans r₄)))).trans
      (fr u (.inl h))
  · have written:=r₅.trans h
    have after : dst≤u:=(Nat.le_add_right ..).trans written
    exact (DescentVectorBookReshape.frame pm u (.inr (fit.early.trans after)) (.inr written)).trans
      (fr u (.inr (r₃.trans (r₄.trans after))))

theorem post_run (om : Memory w) (Y : Fin N→Fin H→Fin (G*X)→Cell a)
    (ha : 0<A) (hm : 0<M) (hx : 0<X)
    (rows : ∀p : Row (N*H) (G*X) A,
      om (base+(row (N*H) (G*X) A p).val)=((data (together Y) p).val:Word w))
    (room : finish<2^w) :
    let final:=postImage (N:=N) base H G X a A M om
    (postProgram (N:=N) base H G X a A M w).Exec om final (postTicks (N:=N) base H G X a A M) ∧
      (∀q x,Source (.lookup (bank base N H G X a A M q x) .row)
        (fun h g=>Y q h (finProdFinEquiv (g,x))) M final) ∧
      (∀q x,(bank base N H G X a A M q x).Fits w finish) ∧
      (∀u,u< middle ∨ finish≤u→final u=om u) ∧ CheapCode (postProgram (N:=N) base H G X a A M w) := by
  let pm:=Overlap.result middle (N*H) (G*X) A (M*X) a copy om
  obtain ⟨r₁,r₂,r₃,r₄,r₅⟩:=regions (N:=N) base H G X a A M
  have afterPacked : (packed).base≤overSize:=Nat.le_add_right ..
  have afterSrc : middle≤books:=(r₂.trans afterPacked).trans r₃
  have before : base≤ middle:=(Nat.le_add_right ..).trans r₁
  have bookInside : books<2^w:=r₄.trans_lt ((Nat.le_add_right ..).trans_lt (r₅.trans_lt room))
  have midInside : middle<2^w:=afterSrc.trans_lt bookInside
  have safeCopy : (copy).Fits w middle:=dense_fits _ _ midInside
  have area : Overlap.rows (N*H) (G*X) A≤(copy).size:=by
    have size : N*(H*chunks (G*X) A) ≤ (copy).size := dense_capacity _ _
    simpa only [Overlap.rows,Nat.mul_assoc] using size
  obtain ⟨re,fr,cheap⟩:=Overlap.any middle (N*H) (G*X) A (M*X) a copy om safeCopy (r₃.trans_lt bookInside)
  have repack (p : Row (N*H) (G*X) (M*X)) :
      pm ((packed).base+(row (N*H) (G*X) (M*X) p).val)=((data (together Y) p).val:Word w) :=
    Overlap.read middle copy om (together Y) ha safeCopy area rows (r₃.trans_lt bookInside) p
  have counts:=chunks_group G M X hm hx
  have capacity : N*DescentVectorBookReshape.sourceWords H 1 G M≤(packed).size := by
    have size : (N*H)*chunks (G*X) (M*X) ≤ (packed).size := dense_capacity _ _
    simpa only [DescentVectorBookReshape.sourceWords,one_mul,counts,Nat.mul_assoc] using size
  have safeVector:=DescentVectorBookReshape.arranged books packed (dense_fits _ _ bookInside)
    capacity (r₅.trans_lt room)
  have pageRead (q : Fin N) (l : Fin 1) (p : Row H (G*X) (M*X)) :
      pm (DescentVectorBookReshape.sourceBase packed H 1 G M q+l.val*(H*chunks G M)+
        (row H (G*X) (M*X) p).val)=((data (Y q) p).val:Word w) := by
    have lr : l.val=0:=by have := l.isLt;omega
    have get:=repack (finProdFinEquiv (q,p.1),p.2)
    rw [combine_row q p] at get
    simpa only [DescentVectorBookReshape.sourceBase,DescentVectorBookReshape.sourceWords,
      lr,zero_mul,Nat.add_zero,one_mul,counts,together,data,Equiv.symm_apply_apply,Nat.add_assoc] using get
  obtain ⟨runV,dataV,frameV⟩:=DescentVectorBookReshape.run books dst packed pm (fun q _=>Y q)
    hm hx safeVector pageRead
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then re runV machine pc reg pub exit rom advice cfg raw enter same,?_,?_,?_,?_⟩
  · exact page_source Y _ dataV room
  · exact fun q x=>page_fits q x room
  · intro u hu
    rcases hu with low|high
    · exact (frameV u (.inl (low.trans_le afterSrc))).trans (fr u (.inl low))
    · exact (frameV u (.inr (r₅.trans high))).trans
        (fr u (.inr (((r₃.trans r₄).trans (Nat.le_add_right ..)).trans (r₅.trans high))))
  · exact @cheap_seq w _ _ (@cheap) (@vector_cheap N base H G X a A M w)

theorem run (m : Memory w) (Y : Fin N→Fin H→Fin (G*X)→Cell a)
    (ha : 0<A) (hm : 0<M) (hx : 0<X) (early : ∀q,(src q).Fits w base)
    (observed : ∀q,Source (.lookup (src q) .row) (Y q) A m)
    (room : finish<2^w) :
    let final:=image base H G X a A M src m
    (program base H G X a A M src w).Exec m final (ticks base H G X a A M src) ∧
      (∀q x,Source (.lookup (bank base N H G X a A M q x) .row)
        (fun h g=>Y q h (finProdFinEquiv (g,x))) M final) ∧
      (∀q x,(bank base N H G X a A M q x).Fits w finish) ∧
      (∀u,u<base ∨ finish≤u→final u=m u) ∧ CheapCode (program base H G X a A M src w) := by
  obtain ⟨r₁,r₂,r₃,r₄,r₅⟩:=regions (N:=N) base H G X a A M
  have middleBefore : middle≤finish:=r₂.trans ((Nat.le_add_right ..).trans
    (r₃.trans (r₄.trans ((Nat.le_add_right ..).trans r₅))))
  have front : base≤ middle:=(Nat.le_add_right ..).trans r₁
  obtain ⟨cp,rows,cpframe⟩:=gather_run base src Y m early observed ((r₁.trans middleBefore).trans_lt room)
  obtain ⟨tail,read,fit,frame,cheap⟩:=post_run base H G X a A M _ Y ha hm hx rows room
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then cp tail machine pc reg pub exit rom advice cfg raw enter same,read,fit,?_,@cheap_seq w _ _ (@program_cheap w (gatherPasses src H (G*X) A base)) (@cheap)⟩
  intro u hu
  rcases hu with lo|hi
  · exact (frame u (.inl (lo.trans_le front))).trans (cpframe u (.inl lo))
  · exact (frame u (.inr hi)).trans (cpframe u (.inr ((r₁.trans middleBefore).trans hi)))

theorem clock_bound :
    ticks base H G X a A M src≤
      (4+N*(4+(H*chunks (G*X) A)*18))+
      (Overlap.ticks middle (N*H) (G*X) A (M*X) a copy+
        (8+10*DescentVectorBookReshape.dictionaryWords X a M+74*(N*DescentVectorBookReshape.rows H 1 G X M))) := by
  rw [←DescentVectorBookReshape.ticks_eq]
  exact Nat.add_le_add_right (gather_clock src H (G*X) A base) _

end
end
end Hierarchy.DescentResetStemProject

end OAI
