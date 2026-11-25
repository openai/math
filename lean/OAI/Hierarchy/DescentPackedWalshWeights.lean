import OAI.Hierarchy.DescentPackedWalshSquare
import OAI.Hierarchy.DescentWeightColumnRAM

namespace OAI
/-! # Weight true local correlations and select their measured depth in one native pass -/
namespace Hierarchy.DescentPackedWalsh.Weight
open DescentPackedWalsh DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b c g w : ℕ}

def pair (g bits : ℕ) : Cell g × Cell bits ≃ Cell (g+bits) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add]))

def table (m b c g l : ℕ) (key : Cell (g+b*2^l)) : Cell (c*2^l) :=
  let a:=(pair g (b*2^l)).symm key
  encode c (2^l) (fun j=>(a.1.val*(((encode b (2^l)).symm a.2 j).val/2^m):ℕ))

structure Header where
  owner : Bank
  depth : Bank
  gain : Bank
  shift : Bank
  numer : Bank
  results : Bank

def expr (S : Header) (j : ℕ) : Expr :=
  let h:=Expr.lookup S.owner .row
  .branch .eq (.lookup S.depth h) (.lit j)
    (.lookup S.results (.op .add (.lookup S.numer .row) (.lookup S.shift (.lookup S.gain h)))) (.lit 0)

structure Room (S : Header) (a H u l b g w : ℕ) : Prop where
  owner : S.owner.Fits w a
  depth : S.depth.Fits w a
  gain : S.gain.Fits w a
  shift : S.shift.Fits w a
  numer : S.numer.Fits w a
  results : S.results.Fits w a
  hosts : H≤S.depth.size ∧ H≤S.gain.size
  groups : H*2^u≤S.owner.size ∧ H*2^u≤S.numer.size
  gainKey : 2^g≤S.shift.size
  resultKey : 2^(g+b*2^l)≤S.results.size
  endBound : a+H*2^u<2^w

/-- All three literal banks depend only on bit widths and the common rectangle. -/
structure Fixed (S : Header) (u l b c g H : ℕ) (mem : Memory w) : Prop where
  owner : ∀(v : Fin H) (p : Cube u),mem (S.owner.base+(row v p).val)=(v.val:Word w)
  shift : ∀a : Cell g,mem (S.shift.base+a.val)=((2^(b*2^l)*a.val:ℕ):Word w)
  result : ∀i : Cell (g+b*2^l),mem (S.results.base+i.val)=((table (u+l) b c g l i).val:Word w)

private theorem chunk_zero : chunk (fun _ : Cube l=>(0:Cell c))=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin (2^l)=>(0:Cell c))).val=0
  simp

/-- A gain belongs to the input statistic; all its packed chunks read the very same gain and depth. -/
theorem run (S : Header) (a j : ℕ) (mem : Memory w) (lev : Fin H→ℕ) (gain : Fin H→Cell g)
    (x : Fin H→Cube u→Cube l→Cell b) (bound : ∀v,lev v<2^w) (target : j<2^w)
    (room : Room S a H u l b g w) (fixed : Fixed S u l b c g H mem)
    (levelRead : ∀v,mem (S.depth.base+v.val)=(lev v:Word w))
    (gainRead : ∀v,mem (S.gain.base+v.val)=((gain v).val:Word w)) (old : Installed S.numer.base x mem) :
    let dst:=image a (H*2^u) (expr S j) mem
    (scan w a (H*2^u) (expr S j)).Exec mem dst (4+(H*2^u)*(2*(expr S j).work+4)) ∧
      Installed a (fun v p q=>if lev v=j then (((gain v).val*((x v p q).val/2^(u+l)):ℕ):Cell c) else 0) dst ∧
      (∀z<a,dst z=mem z) ∧ ∀z,a+H*2^u≤z→dst z=mem z := by
  have safe : (expr S j).Fits w a :=
    ⟨⟨room.depth,room.owner,trivial⟩,trivial,⟨room.results,⟨room.numer,trivial⟩,room.shift,
       room.gain,room.owner,trivial⟩,trivial⟩
  refine ⟨(by intro P R K machine; exact scan_exec _ _ _ _ safe room.endBound machine),?_,fun z h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h),
    fun z h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr h)⟩
  intro v p
  rw [ProtocolRAMGeneratedWrite.read_image]
  have hostWord : S.owner.read mem ((row v p).val : Word w)=(v.val : Word w) :=
    (DescentPackedZip.bank_read S.owner mem ((row v p).isLt.trans_le room.groups.1)
      room.owner).trans (fixed.owner v p)
  have levelWord : S.depth.read mem (v.val : Word w)=(lev v : Word w) :=
    (DescentPackedZip.bank_read S.depth mem (v.isLt.trans_le room.hosts.1)
      room.depth).trans (levelRead v)
  have same : (lev v : Word w)=(j : Word w) ↔ lev v=j := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (bound v),Fin.val_cast_of_lt target]
  have tested : DescriptorExpr.Comparison.eq.test
      (S.depth.read mem (S.owner.read mem ((row v p).val : Word w))) (j : Word w)=true ↔ lev v=j := by
    simpa only [DescriptorExpr.Comparison.test,beq_iff_eq,hostWord,levelWord] using same
  by_cases hit : lev v=j
  · have branch : (expr S j).eval mem ((row v p).val : Word w) =
        S.results.read mem (S.numer.read mem ((row v p).val : Word w) +
          S.shift.read mem (S.gain.read mem (S.owner.read mem ((row v p).val : Word w)))) :=
      ite_eq_left (tested.mpr hit)
    rw [branch]
    simp only [ite_eq_left hit]
    rw [hostWord,DescentPackedZip.bank_read S.numer mem ((row v p).isLt.trans_le room.groups.2) room.numer,old v p,
      DescentPackedZip.bank_read S.gain mem (v.isLt.trans_le room.hosts.2) room.gain,gainRead v,
      DescentPackedZip.bank_read S.shift mem ((gain v).isLt.trans_le room.gainKey) room.shift,
      fixed.shift (gain v),←Nat.cast_add]
    let i := (pair g (b*2^l)) (gain v,chunk (x v p))
    change S.results.read mem (i.val : Word w)=_
    rw [DescentPackedZip.bank_read S.results mem (i.isLt.trans_le room.resultKey) room.results,fixed.result i]
    simp only [i,table,chunk,Equiv.symm_apply_apply]
  · have branch : (expr S j).eval mem ((row v p).val : Word w) = 0 :=
      ite_eq_right (fun h => hit (tested.mp h))
    rw [branch]
    simp only [ite_eq_right hit,chunk_zero,Fin.val_zero,Nat.cast_zero]

theorem tariff (S : Header) (j : ℕ) : 2*(expr S j).work+4=94 := by rfl

end
end Hierarchy.DescentPackedWalsh.Weight

end OAI
