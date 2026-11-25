import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProbeStageProgramSize
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Gathering all operand pages onto one host axis for the packed overlap scan -/
namespace Hierarchy.DescentResetStemProject
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {N H G A a w : ℕ}

def dense (base amount : ℕ) : Bank := ⟨base,Nat.clog 2 (amount+1)⟩

theorem dense_capacity (base amount : ℕ) : amount≤(dense base amount).size :=
  (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

theorem dense_fits (base amount : ℕ) (end_ : base+(dense base amount).size<2^w) :
    (dense base amount).Fits w (base+(dense base amount).size) :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt end_,le_rfl⟩

def gatherFields (src : Fin N→Bank) := List.ofFn (fun q=>Expr.lookup (src q) .row)
def gatherPasses (src : Fin N→Bank) (H G A base : ℕ) :=
  ProbeStage.Native.columns (H*chunks G A) base (gatherFields src)
def gatherImage (src : Fin N→Bank) (H G A base : ℕ) (m : Memory w) :=
  result (gatherPasses src H G A base) m

def together (Y : Fin N→Fin H→Fin G→Cell a) (v : Fin (N*H)) :=
  Y (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2

theorem combine_row (q : Fin N) (p : Row H G A) :
    (row (N*H) G A (finProdFinEquiv (q,p.1),p.2)).val=
      q.val*(H*chunks G A)+(row H G A p).val := by
  simp only [row,finProdFinEquiv_apply_val]
  ring

theorem gather_run (base : ℕ) (src : Fin N→Bank) (Y : Fin N→Fin H→Fin G→Cell a) (m : Memory w)
    (fit : ∀j,(src j).Fits w base) (read : ∀j,Source (.lookup (src j) .row) (Y j) A m)
    (space : base+N*(H*chunks G A)<2^w) :
    let last:=gatherImage src H G A base m
    (program w (gatherPasses src H G A base)).Exec m last (clock (gatherPasses src H G A base)) ∧
    (∀p : Row (N*H) G A,last (base+(row (N*H) G A p).val)=((data (together Y) p).val:Word w)) ∧
    (∀u,u<base ∨ base+N*(H*chunks G A)≤u→last u=m u) := by
  let es:=gatherFields src
  have size : es.length=N:=List.length_ofFn
  have fits : ∀e∈es,e.Fits w base := by
    intro _ hit
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hit
    exact ⟨fit j,trivial⟩
  refine ⟨ProbeStage.Native.columns_exec es m
    (ProbeStage.Native.columns_safe es (le_refl base) fits (by simpa only [size] using space)),?_,?_⟩
  · rintro ⟨v,c⟩
    obtain ⟨⟨j,h⟩,rfl⟩:=finProdFinEquiv.surjective v
    let p : Row H G A:=(h,c)
    have index : j.val<es.length := by rw [size];exact j.isLt
    have cell:=ProbeStage.Native.columns_read es m (le_refl base) fits j.val index (row H G A p)
    have column : es[j.val]'index=.lookup (src j) .row := by simp [es,gatherFields]
    rw [column] at cell
    rw [combine_row j p,←Nat.add_assoc]
    simpa only [gatherImage,gatherPasses,es,p,data,together,Equiv.symm_apply_apply] using cell.trans (read j p)
  · intro u hu
    exact ProbeStage.Native.columns_frame es m (by simpa only [size] using hu)

theorem gather_clock (src : Fin N→Bank) (H G A base : ℕ) :
    clock (gatherPasses src H G A base)≤4+N*(4+(H*chunks G A)*18) := by
  apply le_trans (ProbeStage.Native.columns_clock _ _ 7 _ ?_)
  · simp [gatherFields]
  · intro _ h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact le_rfl

end
end Hierarchy.DescentResetStemProject

end OAI
