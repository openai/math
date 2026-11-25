import OAI.Hierarchy.DescentTerminalChipRuntime

namespace OAI
/-! # Observing both actual comparison flags and every issued scalar key -/
namespace Hierarchy.DescentTerminalChipRuntime
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w N slots : ℕ} (A : Layout) (L : Banks) (rm : Room A L w N slots)
  (m : Memory w)

theorem lower₂ {j : ℕ} (hj : j<A.first) : m₂ A L N m j=m j := by
  have h : j < A.xCheck := by change j < A.first+A.width; omega
  exact (DescentTerminalProposalCheck.frame (out:=A.xCheck) (n:=N) A.x L.xWords (m₁ A L N m) h).trans
    (image_low m A.x.base N (dense L) hj)

theorem lower₄ {j : ℕ} (hj : j<A.first) : m₄ A L N m j=m j := by
  have check : j < A.yCheck := by change j < A.first+3*A.width+1; omega
  have dest : j < A.y.base := by change j < A.first+2*A.width+1; omega
  calc
    _ = m₃ A L N m j := DescentTerminalProposalCheck.frame (out:=A.yCheck) (n:=N) A.y L.ySlices _ check
    _ = m₂ A L N m j := image_low _ A.y.base N (route L) dest
    _ = _ := lower₂ A L m hj

theorem lower {j : ℕ} (hj : j<A.first) : finalMem A L N slots m j=m j := by
  have h : j < A.keys := by change j < A.first+4*A.width+2; omega
  exact (image_low (m₄ A L N m) A.keys slots (key L) h).trans (lower₄ A L m hj)

include rm in
/-- The scalar expression always sees the original header, immutable pointer table
and the fixed row view of Y. -/
theorem key_read (i : Fin slots) : finalMem A L N slots m (A.keys+i.val)=(key L).eval m (i.val:Word w) := by
  exact (image_at (m₄ A L N m) A.keys slots (key L) i).trans
    (eval_below (key L) (i.val:Word w) m (m₄ A L N m) rm.inputKey (fun _ hj => lower₄ A L m hj))

def SourceOK (_A : Layout) (L : Banks) (N : ℕ) (m : Memory w) : Prop :=
  ∀i:Fin N,(dense L).eval m (i.val:Word w)=m (L.xWords.base+i.val)
def RouteOK (_A : Layout) (L : Banks) (N : ℕ) (m : Memory w) : Prop :=
  ∀i:Fin N,(route L).eval m (i.val:Word w)=m (L.ySlices.base+i.val)

include rm

theorem x_flag : finalMem A L N slots m (A.xCheck+N)=(if SourceOK A L N m then 0 else 1) := by
  have count := rm.count
  have keyLo : A.xCheck+N < A.keys := by change A.first+A.width+N < A.first+4*A.width+2; omega
  have checkLo : A.xCheck+N < A.yCheck := by change A.first+A.width+N < A.first+3*A.width+1; omega
  have rowLo : A.xCheck+N < A.y.base := by change A.first+A.width+N < A.first+2*A.width+1; omega
  have compare : DescentTerminalProposalCheck.same A.x L.xWords N (m₁ A L N m) ↔ SourceOK A L N m := by
    unfold DescentTerminalProposalCheck.same SourceOK
    apply forall_congr';intro i
    have lo : L.xWords.base+i.val < A.x.base :=
      (Nat.add_lt_add_left (i.isLt.trans_le rm.xCap) L.xWords.base).trans_le rm.x.2.2
    rw [m₁,image_at m A.x.base N (dense L) i,image_low m A.x.base N (dense L) lo]
  rw [finalMem,image_low _ A.keys slots (key L) keyLo,
    m₄,DescentTerminalProposalCheck.frame (out:=A.yCheck) (n:=N) A.y L.ySlices _ checkLo,
    m₃,image_low _ A.y.base N (route L) rowLo,
    m₂,DescentTerminalProposalCheck.flag]
  simp only [compare]

theorem y_flag : finalMem A L N slots m (A.yCheck+N)=(if RouteOK A L N m then 0 else 1) := by
  have count := rm.count
  have keyLo : A.yCheck+N < A.keys := by change A.first+3*A.width+1+N < A.first+4*A.width+2; omega
  have compare : DescentTerminalProposalCheck.same A.y L.ySlices N (m₃ A L N m) ↔ RouteOK A L N m := by
    unfold DescentTerminalProposalCheck.same RouteOK
    apply forall_congr';intro i
    have lo : L.ySlices.base+i.val < A.first :=
      (Nat.add_lt_add_left (i.isLt.trans_le rm.yCap) L.ySlices.base).trans_le rm.y.2.2
    have before : L.ySlices.base+i.val < A.y.base := by change _ < A.first+2*A.width+1; omega
    rw [m₃,image_at (m₂ A L N m) A.y.base N (route L) i,
      image_low (m₂ A L N m) A.y.base N (route L) before,lower₂ (N:=N) A L m lo,
      eval_below (route L) (i.val:Word w) m (m₂ A L N m) rm.inputRoute (fun _ hj => lower₂ A L m hj)]
  rw [finalMem,image_low _ A.keys slots (key L) keyLo,m₄,DescentTerminalProposalCheck.flag]
  simp only [compare]

theorem flags (_pos : 0<w) :
    (finalMem A L N slots m (A.xCheck+N)=0 ∧ finalMem A L N slots m (A.yCheck+N)=0) ↔
      SourceOK A L N m ∧ RouteOK A L N m := by
  rw [x_flag A L rm m,y_flag A L rm m]
  have one : (1:Word w)≠0 := by
    intro h
    have room : 1<2^w:=by have h:=rm.x.2.1;have p:=rm.x.1;omega
    have h':=congrArg Fin.val h
    simp [Nat.mod_eq_of_lt room] at h'
  by_cases x : SourceOK A L N m <;> by_cases y : RouteOK A L N m <;> simp [x,y,one]

end
end Hierarchy.DescentTerminalChipRuntime

end OAI
