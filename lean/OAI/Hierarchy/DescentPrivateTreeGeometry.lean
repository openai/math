import OAI.Hierarchy.DescentTreePrefixIntervals
import OAI.Hierarchy.DescentRosterOrder
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # The common height-indexed fallback shape and its complete physical cable slots -/

namespace Hierarchy.DescentPrivateTreeTemplate
open DescentTreePrefixIntervals Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

abbrev Site (h : ℕ) := Σ d : Fin (h+1),Bits d.val
abbrev Edge (h : ℕ) := Σ d : Fin h,Bits (d.val+1)

def wire (h : ℕ) : Edge h ↪ ℕ where
  toFun e:=Nat.pair e.1.val (DescentRotor.bitWord (e.1.val+1) e.2).val
  inj' := by
    rintro ⟨d,x⟩ ⟨e,y⟩ eqn
    obtain ⟨de,xy⟩:=Nat.pair_eq_pair.mp eqn
    have hde : d=e:=Fin.ext de
    subst e
    exact congrArg (Sigma.mk d) ((DescentRotor.bitWord _).injective (Fin.ext xy))

def order (h : ℕ) : Edge h≃Fin (Fintype.card (Edge h)) :=
  let code:=DescentRosterOrder.compact (wire h)
  Equiv.ofBijective code ((Fintype.bijective_iff_injective_and_card _).2 ⟨code.injective,by simp⟩)

def edgeAt (h slot : ℕ) : Option (Edge h) :=
  if live : slot<Fintype.card (Edge h) then some ((order h).symm ⟨slot,live⟩) else none

structure Template where
  active : ℕ
  source : ℕ
  target : ℕ
  lo : ℕ
  hi : ℕ

/-- The two spatial path names and the inclusive/exclusive leaf addresses
come entirely from the common static height, slot and site naming scheme. -/
def lookup (H h slot : ℕ) (site : Site h→ℕ) : Template :=
  match edgeAt h slot with
  | none=>⟨0,0,0,0,0⟩
  | some e=>⟨1,site ⟨e.1.castSucc,fun j=>e.2 j.castSucc⟩,site ⟨e.1.succ,e.2⟩,start H e.2,stop H e.2⟩

def read {w : ℕ} (u base : ℕ) (prefixes : ℕ→Word w) (t : Template) : Fin 5→Word w :=
  ![(t.active:Word w),(t.source:Word w),(t.target:Word w),(u:Word w)*(prefixes (base+t.hi)-prefixes (base+t.lo)),(t.active:Word w)]

theorem padding {w : ℕ} (u base H h slot : ℕ) (site : Site h→ℕ) (empty : Fintype.card (Edge h)≤ slot)
    (source : ℕ→Word w) :
    read u base source (lookup H h slot site)=0 := by
  have miss : edgeAt h slot=none := by
    unfold edgeAt
    rw [dite_eq_right (Nat.not_lt.mpr empty)]
  funext j
  fin_cases j <;> simp [read,lookup,miss]

end
end Hierarchy.DescentPrivateTreeTemplate

end OAI
