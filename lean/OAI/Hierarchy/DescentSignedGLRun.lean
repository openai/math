import OAI.Hierarchy.DescentSignedGLIngress
import OAI.Hierarchy.DescentDatedSignedArea
import OAI.Hierarchy.DescentZipBook

namespace OAI
/-! # One physical run from separated previous port banks to the remixed signed cube -/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentSIMDLookup DescentPackedZip DescentColonies
open DescentPacking.PackedMatch.Local DescentGLNielsen DescentSixParty
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {G H N D b M h l w : ℕ}

/-- The same fixed insertion page is shared by every signed slot. -/
def joinGate (b N : ℕ) (x : Fin N) : Book.Gate := ⟨b*N,b,b*N,Gather.setField x⟩
def joinWidth (b N : ℕ) := b*N+b
def joinStop (base b N M : ℕ) := base+N*(2*2^(joinWidth b N*M))
def joinOp (base b N M D : ℕ) (old : Fin D→Fin N→Expr) (j : ℕ) : Expr :=
  if hit : j<D then Gather.assembly (Book.tables (joinGate b N) (joinWidth b N) M base) (old ⟨j,hit⟩)
  else .lit 0

theorem from_slots (base : ℕ) (saved : Bank) (old : Fin D→Fin N→Expr)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (lanes : 2^l=M*N)
    (pos : 0<M) (blocks : 0<N)
    (X : Fin D→Fin H→Fin G→Fin N→Cell b) (mem : Memory w)
    (safe : ∀j x,(old j x).Fits w base)
    (signed : ∀j x,Source (old j x) (fun v g=>X j v g x) M mem)
    (keyFits : saved.Fits w base)
    (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (room : stop (joinStop base b N M) D H h l b<2^w) :
    let first:=joinStop base b N M
    let C:=chart first D H h l b
    let pre:=Book.install (joinGate b N) (joinWidth b N) M w base
    let field:=joinOp base b N M D old
    let run:=pre.seq (program first C saved field D H h l b w)
    ∃last,run.Exec mem last ((4+10*(N*(2*2^(joinWidth b N*M))))+
      duration first C saved field D H h l b w) ∧ CheapCode run ∧
      (∀j,Dense (h:=h) (l:=l) (slice (((C.chosen (h+l)).bank (schedule (h+l)).length).base) H (2^h) j)
        (fun v z=>let p:=finProdFinEquiv.symm (Fin.cast size ((rearrange μ).symm z))
                  X j v p.1 p.2) last) ∧
      ∀a,a<base ∨ stop first D H h l b≤a→last a=mem a := by
  let first:=joinStop base b N M
  let C:=chart first D H h l b
  let T:=Book.tables (joinGate b N) (joinWidth b N) M base
  let mid:=Book.image (joinGate b N) (joinWidth b N) M base mem
  let inputs:=joinOp base b N M D old
  let Y (j : Fin D) (v : Fin H) (z : Block (h+l)) :=
    let p:=finProdFinEquiv.symm (Fin.cast size z)
    X j v p.1 p.2
  have base_le : base≤first:=Nat.le_add_right ..
  have first_le : first≤ stop first D H h l b :=
    Dated.origin_le_endAddress first (D*H) h l b
  have fit : first<2^w:=first_le.trans_lt room
  have caps (x : Fin N) : (joinGate b N x).left+(joinGate b N x).right≤joinWidth b N:=le_rfl
  obtain ⟨printed,static,frame,literal⟩:=Book.mount (joinGate b N) (joinWidth b N) M base mem caps fit
  have low (a : ℕ) (lo : a<base) : mid a=mem a:=frame a (.inl lo)
  have built (j : Fin D) : (inputs j.val).Fits w first ∧ Source (inputs j.val) (Y j) (2^l) mid := by
    have bounds : Gather.Bounds (d:=b) (M:=M) (w:=w) T (old j) first := by
      intro x
      obtain ⟨shift,combine⟩:=Book.geometry (joinGate b N) (joinWidth b N) M base x le_rfl fit (caps x)
      exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ base_le (safe j x),shift,combine,rfl,rfl⟩
    have stays (x : Fin N) : Source (old j x) (fun v g=>X j v g x) M mid := by
      intro p
      exact (eval_below _ _ mem mid (safe j x) low).trans (signed j x p)
    simpa only [inputs,joinOp,dite_eq_left j.isLt] using
      (signed_source size lanes pos blocks T (old j) first bounds (X j) mid static stays)
  obtain ⟨valid,extent,offsets,switches,gap⟩:=allocation first D H h l b w room
  have selected : mid saved.base=((DescentExterior.matrixCode μ).val:Word w):=
    (low saved.base (by have:=keyFits.2.2;have : 0<saved.size:=Nat.two_pow_pos _;omega)).trans savedWord
  obtain ⟨last,permuted,hardware,out,keep⟩:=issue first C saved inputs μ Y mid valid
    ⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans base_le⟩ selected (fun j hj=>(built ⟨j,hj⟩).1)
    (fun j=>(built j).2) extent offsets switches gap
  refine ⟨last,printed.then permuted,cheap_seq literal hardware,out,?_⟩
  intro a ha
  rcases ha with lo|hi
  · exact (keep a (.inl (lo.trans_le base_le))).trans (low a lo)
  · exact (keep a (.inr ((after_data ..).trans hi))).trans (frame a (.inr (first_le.trans hi)))

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
