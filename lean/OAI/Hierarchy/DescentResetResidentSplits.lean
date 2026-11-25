import OAI.Hierarchy.DescentResetPackedSplit
import OAI.Hierarchy.DescentResetGLPanels
import OAI.Hierarchy.DescentPackedColonyFrame

namespace OAI
/-! # Computing reset split flags on the previously remixed amount bank -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentColonies DescentGL DescentPackedColony DescentSIMDLookup DescentIssuedFallbackPanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H Δ h l c b M w : ℕ}

theorem split_frame (A : Frame.Chart) (S : Frame.Room A H (2^c) Δ (h+l-c) b M w)
    (mem : Memory w) (addr : ℕ)
    (frame : addr<A.fresh Δ (h+l-c) ∨ A.fresh Δ (h+l-c)+(h+l-c)*A.page≤addr) :
    result (passes (A.issued Δ (h+l-c) b M) H (2^c) M (h+l-c)) mem addr=mem addr := by
  have outside {base count : ℕ} (e : Expr) (prev : Memory w)
      (away : addr < base ∨ base + count ≤ addr) :
      ProtocolRAM.image base count e prev addr = prev addr := by
    simp [ProtocolRAM.image, fillSegment, show ¬ (base ≤ addr ∧ addr < base + count) by omega]
  let r:=h+l-c
  have all (i : ℕ) (hi : i≤r) :
      result (passes (A.issued Δ r b M) H (2^c) M i) mem addr=mem addr := by
    induction i with
    | zero=>rfl
    | succ i ih=>
      rw [passes,result_append]
      apply (outside _ _ ?_).trans (ih (by omega))
      change addr<A.fresh Δ r+i*A.page ∨ A.fresh Δ r+i*A.page+H*chunks (2^c) M≤addr
      rcases frame with low|high
      · exact Or.inl (low.trans_le (Nat.le_add_right ..))
      · right
        have reach:=Nat.mul_le_mul_right A.page hi
        rw [Nat.succ_mul] at reach
        have top:=S.cells
        dsimp only [r] at *
        omega
  exact all r le_rfl

theorem splits_from_rows (small : c≤h+l)
    (A : Frame.Chart) (S : Frame.Room A H (2^c) Δ (h+l-c) b M w)
    (roster : Fin H→Fin Δ→Option (Fin H)) (weight : Fin H→Block (h+l)→ℕ)
    (L : DescentGL.Layout (h+l)) (D cap : ℕ) (mem : Memory w)
    (fit : ∀v x,weight v x<2^b) (nearby : ∀v i,mem (A.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w))
    (words : Reads A.weights (fun v hi=>encode b (2^(h+l-c)) (fun x=>
      (weight v ((rearrange L).symm (join small hi x)):Cell b))) M mem)
    (resident : A.mount Δ H (2^c) (h+l-c) b M D cap 0 (identitySeed (h+l-c)) mem=mem) :
    let k:=h+l-c
    let rows:=fun hi=>Scan.build (incoming (peers roster))
      (fun v low=>rearrangedLoad weight L v (join small hi low)) D cap k
    let ly:=A.issued Δ k b M
    let ps:=passes ly H (2^c) M k
    (ProtocolRAM.program w ps).Exec mem (result ps mem) (clock ps) ∧ CheapCode (ProtocolRAM.program w ps) ∧
      Reads (ly.source k) (fun v hi=>cache (rows hi) v) M (result ps mem) ∧
      clock ps≤4+k*(4+H*chunks (2^c) M*(2*(25+56*Δ)+4)) ∧
      ∀z,z<A.fresh Δ k ∨ A.fresh Δ k+k*A.page≤z→ result ps mem z=mem z := by
  have pre:=Frame.input A S roster (fun hi v z=>rearrangedLoad weight L v (join small hi z))
    D cap 0 (identitySeed (h+l-c)) mem nearby words
  rw [resident] at pre
  obtain ⟨execute,read,price⟩:=physical_splits small (A.issued Δ (h+l-c) b M) (Frame.hardware A S)
    (Frame.low A S) roster weight L D cap fit mem pre
  exact ⟨execute,@ProtocolRAM.program_cheap _ _,read,price,split_frame A S mem⟩

theorem resident_splits (small : c≤h+l) (pitch : M*2^(h+l-c)=2^l) (positive : 0<M)
    (A : Frame.Chart) (S : Frame.Room A H (2^c) Δ (h+l-c) b M w)
    (roster : Fin H→Fin Δ→Option (Fin H)) (weight : Fin H→Block (h+l)→ℕ)
    (L : DescentGL.Layout (h+l)) (D cap : ℕ) (mem : Memory w)
    (fit : ∀v x,weight v x<2^b) (nearby : ∀v i,mem (A.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w))
    (measured : DescentGLPacked.Dense (h:=h) (l:=l) A.weights.base
      (fun v z=>(weight v ((rearrange L).symm z):Cell b)) mem)
    (resident : A.mount Δ H (2^c) (h+l-c) b M D cap 0 (identitySeed (h+l-c)) mem=mem) :
    let k:=h+l-c
    let rows:=fun hi=>Scan.build (incoming (peers roster))
      (fun v low=>rearrangedLoad weight L v (join small hi low)) D cap k
    let ly:=A.issued Δ k b M
    let ps:=passes ly H (2^c) M k
    (ProtocolRAM.program w ps).Exec mem (result ps mem) (clock ps) ∧ CheapCode (ProtocolRAM.program w ps) ∧
      Reads (ly.source k) (fun v hi=>cache (rows hi) v) M (result ps mem) ∧
      clock ps≤4+k*(4+H*chunks (2^c) M*(2*(25+56*Δ)+4)) ∧
      ∀z,z<A.fresh Δ k ∨ A.fresh Δ k+k*A.page≤z→ result ps mem z=mem z := by
  exact splits_from_rows small A S roster weight L D cap mem fit nearby
    (grouped_remix small pitch positive A.weights.base (fun v x=>(weight v x:Cell b)) L mem measured) resident

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
