import OAI.Hierarchy.TaggedWirePacketMiddle
import OAI.Hierarchy.TaggedWidePadding

namespace OAI
/-! # Zero extension of the actual two-sided role words of a signed repair -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open ThreeFlat Routing Diagonal Diagonal.MotifOuterTerms TraceWords
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM
open NamedAperture CalendarTape AdaptiveProbe
open scoped Classical Fin.CommRing

variable {F V : Type} [Field F] [Fintype V] {S H copies N cap digits : ℕ}
    {row : Row F S H copies} {phys : Fin N → Chord S}
    (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "states" => middleRoom (Fintype.card R.Roles) cap
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "old" => Installs.starts (source:=R.source) R.order

def middleIndex (roles cap : ℕ) := (finProdFinEquiv : Fin (roles*2)×Fin cap ≃ Fin ((roles*2)*cap))
def middleHalf (roles : ℕ) := (((Equiv.refl (Fin roles)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv)

def guardMiddle (roles cap digits : ℕ) (fits : cap≤2^digits)
    (incident : Fin roles×Bool → V) (qty : Fin roles → Fin digits → V) :
    Tagged.WidePadding.Ports (V⊕Fin (middleRoom roles cap)) (middleRoom roles cap) digits where
  col p := ⟨((middleIndex roles cap).symm p).2.val,((middleIndex roles cap).symm p).2.isLt.trans_le fits⟩
  live p := .inl (incident ((middleHalf roles).symm ((middleIndex roles cap).symm p).1))
  width p b := .inl (qty ((middleHalf roles).symm ((middleIndex roles cap).symm p).1).1 b)
  payload p := .inr p

theorem guard_middle (fits : cap≤2^digits) (room : ∀i,w i ≤ cap)
    (incident : Fin (Fintype.card R.Roles)×Bool → V) (qty : Fin (Fintype.card R.Roles) → Fin digits → V)
    (v : V → Bool)
    (sides : ∀i b,v (incident (i,b))=decide ((rowGraph old).vertex i b=s))
    (strict : cap<2^digits)
    (read : ∀i j,v (qty i j)=TraceWords.bits (⟨w i,(room i).trans_lt strict⟩ : Word digits) j)
    (d : Fin states → Bool) :
    TypedWiring.value ((guardMiddle (Fintype.card R.Roles) cap digits fits incident qty).network (F:=F)) (Sum.elim v d)=
      if ∀q,d q=true → q∈Set.range (middlePlace R c s cap room) then 1 else 0 := by
  let low (q : Fin states) := (middleHalf (Fintype.card R.Roles)).symm ((middleIndex _ cap).symm q).1
  let wid (q : Fin states) : Word digits := ⟨w (low q).1,(room _).trans_lt strict⟩
  rw [Tagged.WidePadding.Ports.eval (guardMiddle (Fintype.card R.Roles) cap digits fits incident qty)
    (Sum.elim v d) wid (fun q j=>read (low q).1 j)]
  have one (q : Fin states) : (Sum.elim v d) ((guardMiddle _ _ _ fits incident qty).live q)=true ∧
      (guardMiddle _ _ _ fits incident qty).col q<wid q ↔ q∈Set.range (middlePlace R c s cap room) := by
    obtain ⟨⟨half,j⟩,rfl⟩ := (middleIndex (Fintype.card R.Roles) cap).surjective q
    obtain ⟨⟨i,b⟩,rfl⟩ := (middleHalf (Fintype.card R.Roles)).surjective half
    change _ ↔ finProdFinEquiv (halfCode i b,j)∈_
    rw [middle_range]
    have hi : (finProdFinEquiv (i, finTwoEquiv.symm b)).divNat = i :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, finTwoEquiv.symm b))
    have hb : (finProdFinEquiv (i, finTwoEquiv.symm b)).modNat = finTwoEquiv.symm b :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, finTwoEquiv.symm b))
    simp [guardMiddle,middleIndex,middleHalf,low,wid,sides,hi,hb,and_comm]
  simp only [one]
  rfl

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
