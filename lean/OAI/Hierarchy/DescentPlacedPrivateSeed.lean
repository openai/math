import OAI.Hierarchy.DescentTerminalPlacedHistogram
import OAI.Hierarchy.DescentTerminalMaskCounter

namespace OAI
/-! # The single seed exponent is the registered private volume less all populated words -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena
open scoped BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw : ℕ} (V : Home.Format) (R : MaskAllocation.Channels blocks) (start : ℕ)
local notation "C" => meter V R start
def usedWords (sites : ℕ) (m : Memory bw) : ℕ :=
  ∑i : Fin sites,privateHome (measured (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (C).layout m i)

/-- The allocated physical volume and real private-word channels before the terminal code runs. -/
def SeedCount (header sites : ℕ) (m : Memory bw) (exponent : ℕ) : Prop :=
  ∃volume : ℕ,m header=(volume:Word bw) ∧ usedWords V R start sites m*V.piece+exponent=volume

theorem usedWords_frame (sites : ℕ) (m m' : Memory bw)
    (same : ∀f a,a<(R.bank f).size→ m ((R.bank f).base+a)=m' ((R.bank f).base+a)) :
    usedWords V R start sites m=usedWords V R start sites m' := by
  unfold usedWords
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg _
  funext f
  have bankRead : ((C).layout.channel f).read m (i.val : Word bw) =
      ((C).layout.channel f).read m' (i.val : Word bw) :=
    same f _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  simp only [measured, bankRead]

theorem SeedCount.frame {header sites exponent : ℕ} {m m' : Memory bw}
    (seeded : SeedCount V R start header sites m exponent) (headerEq : m' header=m header)
    (columns : ∀f a,a<(R.bank f).size→ m' ((R.bank f).base+a)=m ((R.bank f).base+a)) :
    SeedCount V R start header sites m' exponent := by
  obtain ⟨mass,stored,count⟩:=seeded
  exact ⟨mass,headerEq.trans stored,(congrArg (fun u=>u*V.piece+exponent)
    (usedWords_frame V R start sites m' m columns)).trans count⟩

variable (S : Shape) (I : Input) (header : ℕ) (short : v*span V.publicArity V.roles V.privateWords
  V.nodes V.addresses V.piece≤B) (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "b_" => afterMeter V S R start
local notation "O" => registers V S R start header
local notation "printed" => output V S I R start header short literal

theorem single_seed_count (m : Memory bw) (early : Earlier S I b_ (C).layout bw)
    (space : last V S I R start<2^bw) (prior : ∀f,(R.bank f).base+(R.bank f).size≤ start) (safe : header< start)
    {dead : ℕ} (observed : SeedCount V R start header S.sites m dead) :
    printed m (O).deadBits=(dead:Word bw) := by
  let first:=DescentTerminalEmitter.Compact.loaded (pageEnd S I b_) I.sources literal m
  have startLe : start≤(C).base:=Nat.le_add_right ..
  have beginLe : start≤ b_:=by change _≤(C).base+_+_+_+3;omega
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I b_
  have floor : b_≤(rowArena S I b_).finish:=(rowArena S I b_).start_le _
  have endAt : b_<2^bw:=floor.trans_lt (p0.trans_lt (p1.trans_lt (p2.trans_lt (p3.trans_lt (p4.trans_lt space)))))
  have saved a (ha:a< start) : first a=m a :=
    DescentStaticWordColumn.frame _ _ _ m a (.inl (ha.trans_le (beginLe.trans (floor.trans p0))))
  obtain ⟨total,held,paid⟩:=SeedCount.frame V R start observed (saved _ safe)
    (fun f a ha=>saved _ ((Nat.add_lt_add_left ha _).trans_le (prior f)))
  have debit:=MaskAllocation.terminal R start header short first total prior safe endAt held
    (show usedWords V R start S.sites first*V.piece≤total by omega)
  have seen : (input V S I R start header short literal m) (O).deadBits=
      ((total-usedWords V R start S.sites first*V.piece:ℕ):Word bw) := debit.2.2.1
  rw [before_print V S I R start header short literal m early space
    (show (O).deadBits < b_ by change _+2<_+3;omega),seen]
  exact congrArg (fun k : ℕ=>(k:Word bw)) (by omega)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
