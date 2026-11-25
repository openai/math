import OAI.Hierarchy.DescentTerminalControlROM
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The two dynamic site-control columns and four public decoding multipliers -/
namespace Hierarchy.DescentTerminalControlProgram
open DescentDyadicSpan DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Plan where
  base : ℕ
  sites : ℕ
  codeWords : ℕ
  shape : DescentTerminalControlROM.Shape

namespace Plan
variable (x : Plan)
def table : Bank := ⟨x.base,Nat.clog 2 x.codeWords⟩
def ports : Bank := ⟨x.base+span x.codeWords,Nat.clog 2 x.sites⟩
def first : Bank := ⟨x.ports.base+span x.sites,Nat.clog 2 x.sites⟩
def fixed := x.first.base+span x.sites
def finish := x.fixed+x.shape.size
def lookup (e : Expr) : Expr := .lookup x.table e
def program (w : ℕ) (values : ℕ→ℕ) (e : Expr) :=
  (((DescentStaticWordColumn.program w x.base values x.codeWords).seq
    (scan w x.ports.base x.sites (x.lookup e))).seq (scan w x.first.base x.sites .row)).seq
    (DescentStaticWordColumn.program w x.fixed x.shape.literal x.shape.size)
def time (e : Expr) := ((4+10*x.codeWords)+(4+x.sites*(2*(x.lookup e).work+4))+
    (4+x.sites*8))+(4+10*x.shape.size)
def after {w : ℕ} (values : ℕ→ℕ) (e : Expr) (m : Memory w) :=
  let rom:=DescentStaticWordColumn.image x.base values m x.codeWords
  let old:=ProtocolRAM.image x.ports.base x.sites (x.lookup e) rom
  let paired:=ProtocolRAM.image x.first.base x.sites .row old
  DescentStaticWordColumn.image x.fixed x.shape.literal paired x.shape.size

/-- All indirect reads are bounded on every input word. -/
theorem any {w : ℕ} (m : Memory w) (values : ℕ→ℕ) (e : Expr) (safe : e.Fits w x.base)
    (room : x.finish<2^w) :
    (x.program w values e).Exec m (x.after values e m) (x.time e) ∧ CheapCode (x.program w values e) ∧
    ∀j,j < x.base ∨ x.finish ≤ j→x.after values e m j=m j := by
  let rom:=DescentStaticWordColumn.image x.base values m x.codeWords
  let old:=ProtocolRAM.image x.ports.base x.sites (x.lookup e) rom
  let paired:=ProtocolRAM.image x.first.base x.sites .row old
  have sites:=span_ge x.sites
  have codes:=span_ge x.codeWords
  have start : x.base+x.codeWords ≤ x.ports.base := Nat.add_le_add_left codes _
  have step : x.ports.base+x.sites ≤ x.first.base := Nat.add_le_add_left sites _
  have step' : x.first.base+x.sites ≤ x.fixed := Nat.add_le_add_left sites _
  have stop : x.fixed ≤ x.finish := Nat.le_add_right ..
  have dataFit : x.table.Fits w x.ports.base := ⟨span_pos _,by
    have : x.ports.base=x.base+span x.codeWords := rfl
    change span x.codeWords < 2^w;omega,le_rfl⟩
  have fits : (x.lookup e).Fits w x.ports.base := ⟨dataFit,ProtocolRAMGeneratedWrite.fits_mono e (by omega) safe⟩
  have firstRun : (DescentStaticWordColumn.program w x.base values x.codeWords).Exec m rom (4+10*x.codeWords) := DescentStaticWordColumn.mount x.base x.codeWords values m (by omega)
  have portsRun : (scan w x.ports.base x.sites (x.lookup e)).Exec rom old (4+x.sites*(2*(x.lookup e).work+4)) := scan_exec x.ports.base x.sites (x.lookup e) rom fits (by omega)
  have idRun : (scan w x.first.base x.sites .row).Exec old paired (4+x.sites*8) := scan_exec x.first.base x.sites .row old trivial (by omega)
  obtain ⟨fixedRun,fixedCheap,zero,weights,high⟩:=x.shape.run x.fixed paired room
  refine ⟨?_,cheap_seq (cheap_seq (cheap_seq (DescentStaticWordColumn.cheap w x.base values x.codeWords)
    (scan_cheap w x.ports.base x.sites (x.lookup e))) (scan_cheap w x.first.base x.sites .row)) fixedCheap,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then firstRun portsRun) idRun) fixedRun machine
  · intro j off
    have endAddress : x.finish=x.fixed+x.shape.size := rfl
    exact (high j (by rcases off with h|h <;> omega)).trans
      ((ProtocolRAMGeneratedWrite.frame_image x.first.base x.sites .row old j (by rcases off with h|h <;> omega)).trans
      ((ProtocolRAMGeneratedWrite.frame_image x.ports.base x.sites (x.lookup e) rom j (by rcases off with h|h <;> omega)).trans
      (DescentStaticWordColumn.frame x.base x.codeWords values m j (by rcases off with h|h <;> omega))))

theorem run {w : ℕ} (m : Memory w) (values : ℕ→ℕ) (e : Expr) (code : Fin x.sites→Fin x.codeWords)
    (safe : e.Fits w x.base) (raw : ∀i,e.eval m (i.val:Word w)=((code i).val:Word w))
    (room : x.finish<2^w) :
    let out:=x.after values e m
    (x.program w values e).Exec m out (x.time e) ∧ CheapCode (x.program w values e) ∧
      (∀i : Fin x.sites,x.ports.read out (i.val:Word w)=(values (code i).val:Word w)) ∧
      (∀i : Fin x.sites,x.first.read out (i.val:Word w)=(i.val:Word w)) ∧
      (∀j : Word w,(DescentTerminalControlROM.Shape.zero x.fixed).read out j=0) ∧
      (∀(f : Fin 4) (j : ℕ),j< (![x.shape.vertices+1,x.shape.rowsPerBin+1,x.shape.pageBits,2^x.shape.pageBits] f) →
        (x.shape.bank x.fixed f).read out (j:Word w)=((j*x.shape.weight f:ℕ):Word w)) ∧
      ∀j,j < x.base ∨ x.finish ≤ j→ out j=m j := by
  intro out
  let rom:=DescentStaticWordColumn.image x.base values m x.codeWords
  let old:=ProtocolRAM.image x.ports.base x.sites (x.lookup e) rom
  let paired:=ProtocolRAM.image x.first.base x.sites .row old
  have sites:=span_ge x.sites
  have codes:=span_ge x.codeWords
  have start : x.base+x.codeWords ≤ x.ports.base := Nat.add_le_add_left codes _
  have step : x.ports.base+x.sites ≤ x.first.base := Nat.add_le_add_left sites _
  have step' : x.first.base+x.sites ≤ x.fixed := Nat.add_le_add_left sites _
  have stop : x.fixed ≤ x.finish := Nat.le_add_right ..
  have dataFit : x.table.Fits w x.ports.base := ⟨span_pos _,by
    have : x.ports.base=x.base+span x.codeWords := rfl
    change span x.codeWords < 2^w;omega,le_rfl⟩
  have ⟨go,cheap,frame⟩:=x.any m values e safe room
  obtain ⟨_,_,zero,weights,high⟩:=x.shape.run x.fixed paired room
  have wordBound : span x.sites<2^w := by
    have : x.first.base=x.ports.base+span x.sites := rfl
    omega
  have romKey (i : Fin x.sites) : (x.lookup e).eval rom (i.val:Word w)=(values (code i).val:Word w) := by
    apply Eq.trans (lookup_nat x.table rom _ e (code i).val
      ((eval_below e _ m rom safe (fun j hj=>DescentStaticWordColumn.frame _ _ _ _ j (.inl hj))).trans (raw i))
      ((code i).isLt.trans_le codes) dataFit.2.1)
    exact DescentStaticWordColumn.read _ _ _ _ (code i).isLt
  refine ⟨go,cheap,?_,?_,zero,weights,frame⟩
  · intro i
    have small:=i.isLt.trans_le sites
    change out (x.ports.base+(i.val:Word w).val%(span x.sites))=_
    rw [Fin.val_cast_of_lt (small.trans wordBound),Nat.mod_eq_of_lt small]
    exact (high _ (.inl (by have:=i.isLt;omega))).trans ((ProtocolRAMGeneratedWrite.frame_image
      x.first.base x.sites .row old _ (.inl (by have:=i.isLt;omega))).trans
      ((ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (romKey i)))
  · intro i
    have small:=i.isLt.trans_le sites
    change out (x.first.base+(i.val:Word w).val%(span x.sites))=_
    rw [Fin.val_cast_of_lt (small.trans wordBound),Nat.mod_eq_of_lt small]
    exact (high _ (.inl (by have:=i.isLt;omega))).trans (ProtocolRAMGeneratedWrite.read_image _ _ .row old i)

end Plan
end
end Hierarchy.DescentTerminalControlProgram

end OAI
