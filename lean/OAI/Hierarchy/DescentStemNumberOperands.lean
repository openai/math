import OAI.Hierarchy.DescentStemCoordinateBook
import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentStaticUnary

namespace OAI
/-! # The six numbered-stem operands at one physical memory snapshot -/
namespace Hierarchy.DescentStemNumberOperands
open DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Plan where
  coord : DescentStemCoordinateBook.Shape
  signedBits : ℕ
  selfBits : ℕ
  metaBits : ℕ

namespace Plan
variable (P : Plan)
def rawWidth : Fin 3→ℕ:=![P.signedBits,P.selfBits,P.metaBits*7]
def convert (j : Fin 3) (v : Cell (P.rawWidth j)) : Cell P.coord.width :=
  ((if j=2 then digit P.metaBits 0 v.val else v.val):ℕ)
def gate (j : Fin 3) : Book.Gate:=⟨P.rawWidth j,0,P.coord.width,fun x _=>P.convert j x⟩
def width:=max P.signedBits (max P.selfBits (P.metaBits*7))
def pages:=3*(2*2^(P.width*P.coord.lanes))
def convertBase (base : ℕ):=P.coord.endAddress base
def endAddress (base : ℕ):=P.convertBase base+P.pages
def program (base w : ℕ) :=(P.coord.program base w).seq
  (Book.install P.gate P.width P.coord.lanes w (P.convertBase base))
def ticks:=P.coord.ticks+(4+10*P.pages)
def image {w : ℕ} (base : ℕ) (m : Memory w) :=Book.image P.gate P.width P.coord.lanes
  (P.convertBase base) (P.coord.image base m)
def converted (base : ℕ) (j : Fin 3) (src : Expr) :=
  (Book.tables P.gate P.width P.coord.lanes (P.convertBase base) j).read src (.lit 0)
def stem (base : ℕ) (key : Bank) (x : Fin (2^P.coord.fine)) (lo : Fin (2^P.coord.residual))
    (signed self «meta» : Expr) : Fin 6→Expr :=
  ![P.converted base 0 signed,P.coord.src base key 0 x lo,P.converted base 1 self,P.coord.src base key 1 x lo,
    P.converted base 2 «meta»,P.coord.src base key 2 x lo]

private theorem base_le_convertBase (base : ℕ) : base≤P.convertBase base := by
  rw [convertBase,P.coord.extent base]
  exact Nat.le_add_right _ _

theorem width_bound (j : Fin 3) : (P.gate j).left+(P.gate j).right≤P.width :=by
  fin_cases j <;> simp [gate,rawWidth,width]

theorem any {w : ℕ} (base : ℕ) (m : Memory w) (room : P.endAddress base<2^w) :
    (P.program base w).Exec m (P.image base m) P.ticks ∧ CheapCode (P.program base w) ∧
    ∀u,u<base ∨ P.endAddress base≤u→P.image base m u=m u :=by
  have a := P.base_le_convertBase base
  have b : P.convertBase base≤P.endAddress base:=Nat.le_add_right ..
  obtain ⟨r,cheap,keep⟩:=P.coord.any base m (b.trans_lt room)
  obtain ⟨s,_,stable,cheap'⟩:=Book.mount P.gate P.width P.coord.lanes (P.convertBase base) (P.coord.image base m) P.width_bound room
  refine ⟨?_,cheap_seq cheap cheap',?_⟩
  · intro n R K machine pc reg slots exit rom advice cfg mem entry match_
    exact Procedure.Exec.then r s machine pc reg slots exit rom advice cfg mem entry match_
  · intro u hu
    rcases hu with h|h
    · exact (stable _ (.inl (h.trans_le a))).trans (keep _ (.inl h))
    · exact (stable _ (.inr h)).trans (keep _ (.inr (b.trans h)))

theorem read {w : ℕ} (base : ℕ) (m : Memory w) (room : P.endAddress base<2^w)
    (j : Fin 3) (src : Expr) (v : Fin P.coord.hosts→Fin P.coord.groups→Cell (P.rawWidth j))
    (fit : src.Fits w base) (old : Source src v P.coord.lanes m) :
    (P.converted base j src).Fits w (P.endAddress base) ∧
    Source (P.converted base j src) (fun h g=>P.convert j (v h g)) P.coord.lanes (P.image base m) :=by
  let banks:=Book.tables P.gate P.width P.coord.lanes (P.convertBase base) j
  have a : base≤P.endAddress base := (P.base_le_convertBase base).trans (Nat.le_add_right _ _)
  obtain ⟨_,fixed,_,_⟩:=Book.mount P.gate P.width P.coord.lanes (P.convertBase base) (P.coord.image base m) P.width_bound room
  obtain ⟨sb,ab⟩:=Book.geometry P.gate P.width P.coord.lanes (P.convertBase base) j le_rfl room (P.width_bound j)
  have fits : DescentPackedZip.Fits banks src (.lit 0) (P.rawWidth j) 0 P.coord.lanes (P.endAddress base) w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ a fit,trivial,sb,ab,rfl,rfl⟩
  have held : Source src v P.coord.lanes (P.image base m):=fun p=>
    (eval_below _ _ _ _ fit (fun u h=>(P.any base m room).2.2 u (.inl h))).trans (old p)
  have zero : Source (.lit 0) (fun (_:Fin P.coord.hosts) (_:Fin P.coord.groups)=>(0:Cell 0)) P.coord.lanes (P.image base m):=by
    intro p
    have hz:=(data (fun (_:Fin P.coord.hosts) (_:Fin P.coord.groups)=>(0:Cell 0)) p).isLt
    simp only [Nat.zero_mul,pow_zero] at hz
    have eqn : (data (fun (_:Fin P.coord.hosts) (_:Fin P.coord.groups)=>(0:Cell 0)) p).val=0:=by omega
    rw [eqn]; rfl
  have dead : P.convert j 0=0:=by
    by_cases metaLane : j=2 <;> simp [convert,metaLane,digit]
  exact ⟨⟨fits.apply,fits.right,fits.shift,fits.left⟩,
    read_data banks src (.lit 0) (P.endAddress base) fits (fun x (_:Cell 0)=>P.convert j x)
      dead (P.image base m) (fixed j) _ _ held zero⟩

theorem coordinates {w : ℕ} (base : ℕ) (saved : Bank) (m : Memory w) (μ : DescentGL.Layout P.coord.dim)
    (chosen : m saved.base=((DescentExterior.matrixCode μ).val:Word w)) (early : saved.Fits w base)
    (room : P.endAddress base<2^w) (j : Fin 3) (x : Fin (2^P.coord.fine)) (lo : Fin (2^P.coord.residual)) :
    (P.coord.src base saved j x lo).Fits w (P.endAddress base) ∧
      Source (P.coord.src base saved j x lo) (fun (_:Fin P.coord.hosts) g=>(P.coord.value μ j x lo g:Cell P.coord.width))
        P.coord.lanes (P.image base m) :=by
  have before : P.convertBase base≤P.endAddress base:=Nat.le_add_right ..
  obtain ⟨fit,source⟩:=P.coord.read base saved m μ chosen early (before.trans_lt room) j x lo
  have saved':=(Book.mount P.gate P.width P.coord.lanes (P.convertBase base) (P.coord.image base m) P.width_bound room).2.2.1
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ before fit,fun p=>
    (eval_below _ _ _ _ fit (fun z h=>saved' _ (.inl h))).trans (source p)⟩

theorem extent (base : ℕ) : P.endAddress base=base+P.endAddress 0 :=by
  simp only [endAddress,convertBase,P.coord.extent base,Nat.add_assoc]

end Plan
end
end Hierarchy.DescentStemNumberOperands

end OAI
