import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentPackedSeedLegs
import OAI.Hierarchy.DescentSeedWorld
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # The actual initial copy stamp for an exterior pin, shared by every original vertex -/
namespace Hierarchy.DescentPackedSeed.CopyOrdinal
open DescentColonies DescentSIMDLookup DescentPackedColony.Phase DescentInitialHost DescentSeedRoot
open Computability.BorderVNP.Crossing DescentSixParty ThreeFlat Routing Catalyst Diagonal
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {J : Type} {G R k b w M : ℕ} (name : J≃Fin G) (digits : Fin R≃J×Block k)

theorem size_bill (k G w unit : ℕ) (pos : 0<unit) (room : 2*unit≤w) :
    words k G (lanes w unit)*w≤2^k*w+4*(2^k)*G*unit :=
  volume (2^k) G w unit pos room

theorem digits_read (base : ℕ) (mem : Memory w) (hm : 0<M) (word : b*M≤w) (fits : R≤2^b)
    (read : ∀p:Row (2^k) G M,mem (base+(row _ _ _ p).val)=((data (field (b:=b) name digits) p).val:Word w))
    (x : Block k) (g : J) :
    digit b (lane (name g) hm).val (mem (base+(row _ _ _ (position x (name g) hm)).val)).val=
      (digits.symm (g,x)).val := by
  let p:=position x (name g) hm
  let v:=lane (name g) hm
  rw [read,Fin.val_cast_of_lt ((data (field (b:=b) name digits) p).isLt.trans_le (Nat.pow_le_pow_right (by decide) word))]
  change digit b v.val (data (field (b:=b) name digits) p).val=_
  unfold data
  rw [digit_encode]
  have idx : p.2.val*M+v.val=(name g).val:=by
    change (name g).val/M*M+(name g).val%M=(name g).val
    exact Nat.div_add_mod' _ _
  have live : p.2.val*M+v.val<G:=idx ▸ (name g).isLt
  simp only [dite_eq_left live,field]
  have ord:(⟨p.2.val*M+v.val,live⟩:Fin G)=name g:=Fin.ext idx
  simp only [ord,Equiv.symm_apply_apply]
  change (((digits.symm (g,x)).val : Cell b).val) = (digits.symm (g,x)).val
  exact Fin.val_cast_of_lt ((digits.symm (g,x)).isLt.trans_le fits)

section Seed
variable {F : Type} [Field F] [Fintype J] [DecidableEq J] {ℓ n s : ℕ} (X : Approximation F ℓ n)
  (c : (initialGroup X R s).Choice)
omit [Fintype J] [DecidableEq J] in
theorem seed_digits (base : ℕ) (mem : Memory w) (hm : 0<M) (word : b*M≤w) (fits : R≤2^b)
    (read : ∀p:Row (2^k) G M,mem (base+(row _ _ _ p).val)=((data (field (b:=b) name digits) p).val:Word w))
    (j : Fin R) (v : Vertex X) :
    let g:=(seedPos X c digits ⟨j,v⟩).1
    let x:=seedBlock X c digits ⟨j,v⟩
    digit b (lane (name g) hm).val (mem (base+(row _ _ _ (position x (name g) hm)).val)).val=j.val := by
  intro g x
  simpa only [g,x,seedPos,seedBlock,Prod.mk.eta,Equiv.symm_apply_apply] using
    digits_read name digits base mem hm word fits read x g
end Seed

end
end Hierarchy.DescentPackedSeed.CopyOrdinal

end OAI
