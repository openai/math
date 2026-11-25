import OAI.Hierarchy.DescentTerminalHeaderPublished
import OAI.Hierarchy.DescentTerminalHeaderDraftFrames

namespace OAI
/-! # Four shared literal columns for the two physically addressed header passes -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open ThreeFlat.RAM PhysicalProcedure DescentTerminalHeaderScatter
open scoped Fin.CommRing
noncomputable section
def span (n:ℕ) := 2^Nat.clog 2 (2*n+1)
def literalBank (base n k:ℕ) : Bank := ⟨base+k*span n,Nat.clog 2 (2*n+1)⟩
structure Fixed where
  half : Bank
  lane : Bank
  identity : Bank
  zero : Bank
def literals (base n:ℕ) : Fixed := ⟨literalBank base n 0,literalBank base n 1,literalBank base n 2,literalBank base n 3⟩
def literal (n j:ℕ) : ℕ :=
  if j<span n then j/2 else if j<2*span n then (j-span n)%2 else if j<3*span n then j-2*span n else 0
def litMem {w:ℕ} (base n:ℕ) (m:Memory w) := DescentStaticWordColumn.image base (literal n) m (4*span n)
def litProc (w base n:ℕ) := DescentStaticWordColumn.program w base (literal n) (4*span n)

structure Fixed.Reads (s:Fixed) {w:ℕ} (m:Memory w) (n:ℕ) : Prop where
  halfRead : ∀(i:Fin n) (j:Fin 2),s.half.read m ((field i j).val:Word w)=(i.val:Word w)
  laneRead : ∀(i:Fin n) (j:Fin 2),s.lane.read m ((field i j).val:Word w)=(j.val:Word w)
  direct : ∀i:Fin n,s.identity.read m (i.val:Word w)=(i.val:Word w)
  blank : ∀i:Fin n,s.zero.read m (i.val:Word w)=0

theorem lit_install {w:ℕ} (base n:ℕ) (m:Memory w) (room:base+4*span n<2^w) :
    (litProc w base n).Exec m (litMem base n m) (4+40*span n) ∧ CheapCode (litProc w base n) ∧
    (literals base n).Reads (litMem base n m) n ∧
    (∀j,j<base ∨ base+4*span n≤j→litMem base n m j=m j) := by
  have seats:2*n+1≤ span n:=Nat.le_pow_clog (by decide) _
  have take_ (k u:ℕ) (slot:k<4) (idx:u<span n) :
      (literalBank base n k).read (litMem base n m) (u:Word w)=(literal n (k*span n+u):Word w) := by
    have uFit:u<2^w:=by omega
    change litMem base n m (base+k*span n+(u:Word w).val%span n)=_
    rw [Fin.val_cast_of_lt uFit,Nat.mod_eq_of_lt idx,Nat.add_assoc]
    apply DescentStaticWordColumn.read
    have cap:=Nat.mul_le_mul_right (span n) (show k+1≤4 by omega)
    rw [Nat.succ_mul] at cap;omega
  refine ⟨?_,@DescentStaticWordColumn.cheap _ _ _ _,⟨?_,?_,?_,?_⟩,
    DescentStaticWordColumn.frame base (4*span n) (literal n) m⟩
  · rw [show 4+40*span n=4+10*(4*span n) by omega]
    exact @DescentStaticWordColumn.mount w base (4*span n) (literal n) m room
  · intro i j
    have a:=i.isLt;have b:=j.isLt
    have at_:=take_ 0 (field i j).val (by decide) ((field i j).isLt.trans_le (by omega))
    simpa [literals,literal,field,(show 2*i.val+j.val<span n by omega),
      (show (2*i.val+j.val)/2=i.val by omega)] using at_
  · intro i j
    have a:=i.isLt;have b:=j.isLt
    have at_:=take_ 1 (field i j).val (by decide) ((field i j).isLt.trans_le (by omega))
    simp only [literals,one_mul,field,literal,show ¬(span n+(2*i.val+j.val)<span n) by omega,
      show span n+(2*i.val+j.val)<2*span n by omega,ite_false,ite_true,Nat.add_sub_cancel_left,
      show (2*i.val+j.val)%2=j.val by omega] at at_ ⊢
    exact at_
  · intro i
    have a:=i.isLt
    simpa [literals,literal,show ¬ (2*span n+i.val<span n) by omega,show ¬(2*span n+i.val<2*span n) by omega,
      show 2*span n+i.val<3*span n by omega] using take_ 2 i.val (by decide) (by omega)
  · intro i
    have a:=i.isLt
    simpa [literals,literal,show ¬(3*span n+i.val<span n) by omega,show ¬(3*span n+i.val<2*span n) by omega,
      show ¬(3*span n+i.val<3*span n) by omega] using take_ 3 i.val (by decide) (by omega)

theorem span_price (n:ℕ) : span n≤4*n+2 := by
  cases h:Nat.clog 2 (2*n+1) with
  | zero=>simp [span,h]
  | succ k=>
    have small:=Nat.pow_lt_of_lt_clog (show k<Nat.clog 2 (2*n+1) by omega)
    simp only [span,h,pow_succ];omega

theorem literal_reads_window {w:ℕ} (base n:ℕ) (m later:Memory w) (room:base+4*span n<2^w)
    (frame:∀j,base≤j→j<base+4*span n→later j=litMem base n m j) :
    (literals base n).Reads later n := by
  have fixed:=(lit_install base n m room).2.2.1
  have project (k:ℕ) (lt:k<4) (j:Word w) :
      (literalBank base n k).read later j=(literalBank base n k).read (litMem base n m) j := by
    apply frame
    · change base≤base+k*span n+_;omega
    have rem:=Nat.mod_lt j.val (Nat.two_pow_pos (Nat.clog 2 (2*n+1)))
    have edge:=Nat.mul_le_mul_right (span n) (show k+1≤4 by omega)
    rw [Nat.succ_mul] at edge
    change base+k*span n+j.val%span n<base+4*span n
    change j.val%span n<span n at rem
    omega
  exact ⟨fun i j=>(project 0 (by decide) _).trans (fixed.halfRead i j),
    fun i j=>(project 1 (by decide) _).trans (fixed.laneRead i j),
    fun i=>(project 2 (by decide) _).trans (fixed.direct i),
    fun i=>(project 3 (by decide) _).trans (fixed.blank i)⟩

theorem literal_reads_later {w:ℕ} (base n:ℕ) (m later:Memory w) (room:base+4*span n<2^w)
    (frame:∀j,j<base+4*span n→later j=litMem base n m j) :
    (literals base n).Reads later n :=
  literal_reads_window base n m later room (fun j _ hj=>frame j hj)

/-- Index and format reuse the same six logical roles and the same physical records. -/
def wires (s:Fixed) (O:Output) (inner outer:Bank) : DescentTerminalScatterChip.Layout :=
  ⟨s.half,s.lane,O.active,s.identity,s.zero,O.mode,s.identity,s.identity,s.zero,O.source,inner,outer⟩

end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
