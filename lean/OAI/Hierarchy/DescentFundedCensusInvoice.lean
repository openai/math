import OAI.Hierarchy.DescentFundedCensus

namespace OAI
/-! # Time, code size and final bank of the charged reset computation -/
namespace Hierarchy.DescentFundedCensus
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM DescentPackedFlowBatch
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {s : Shape} (jobs : Fin s.jobs→Job s.bits)

def columns (s : Shape) (base : ℕ) : Bank:=⟨s.out base,Nat.clog 2 (s.jobs*s.rows)⟩

theorem columns_fits {w : ℕ} (s : Shape) (base : ℕ) (room : s.roof base<2^w) :
    (columns s base).Fits w (s.roof base) ∧ s.jobs*s.rows≤(columns s base).size :=by
  have size_le : (columns s base).size ≤ s.roof base :=
    Nat.le_add_left (2^(Nat.clog 2 (s.jobs*s.rows))) (s.out base)
  exact ⟨⟨Nat.two_pow_pos _,size_le.trans_lt room,le_rfl⟩,Nat.le_pow_clog (by decide) _⟩

theorem program_cheap (w base : ℕ) : CheapCode (program jobs w base) :=
  cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)

private theorem scan_names (w low rows pitch K start n : ℕ) (input : ℕ→Expr)
    (cheap : ∀j,start≤j→j<start+n→(input j).work≤K) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (DescentPackedFlowBatch.passes low rows pitch input start n))≤
      15+n*(11+4*K) :=by
  induction n generalizing start with
  | zero =>
    norm_num [DescentPackedFlowBatch.passes,ProtocolRAM.program,DescentStaticWordColumn.names_scan,Expr.work]
  | succ n ih=>
    have now:=cheap start le_rfl (by omega)
    have rest:=ih (start+1) (fun j lo hi=>cheap j (by omega) (by omega))
    simp only [DescentPackedFlowBatch.passes,ProtocolRAM.program,ProtocolRAM.Pass.procedure,
      DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan]
    rw [Nat.succ_mul n (11+4*K)]
    omega

theorem invoice (base w K : ℕ) (first : ∀j,(jobs j).first.work≤K)
    (second : ∀j,(jobs j).second.work≤K) (present : ∀j,(jobs j).present.work≤K) :
    let lim:=3*K+22
    ticks jobs base≤(4+10*(s.pageCount*2^s.width))+(4+s.jobs*(4+s.rows*(2*lim+4))) ∧
      DescentStaticWordColumn.names (program jobs w base)≤15*(s.pageCount*2^s.width+1)+(15+s.jobs*(11+4*lim)) :=by
  intro lim
  have bounded (i : ℕ) (inRange : i<s.jobs) : (instruction jobs base i).work≤lim:=by
    rw [instruction,dite_eq_left inRange]
    simp only [gated,valueExpr,DescentPackedZip.work]
    have a:=first ⟨i,inRange⟩
    have b:=second ⟨i,inRange⟩
    have c:=present ⟨i,inRange⟩
    dsimp only [lim]
    omega
  refine ⟨Nat.add_le_add_left (DescentPackedFlowBatch.tariff _ _ _ _ _ lim bounded) _,?_⟩
  rw [program,DescentStaticWordColumn.names_seq,DescentOrdinaryAtomFieldRAM.ROM.mount,DescentStaticWordColumn.names_mount]
  exact Nat.add_le_add_left
    (scan_names w (s.out base) s.rows s.rows lim 0 s.jobs (instruction jobs base)
      (fun j _ hi => bounded j (by simpa using hi))) _

end
end Hierarchy.DescentFundedCensus

end OAI
