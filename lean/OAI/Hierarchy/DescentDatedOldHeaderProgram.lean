import OAI.Hierarchy.DescentPackedNodeDigit
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # An ordinary operand reads its actual earlier compact node header -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a K H G M w : ℕ}

def headerExpr (base a K M : ℕ) (prior : Bank) (slot : Fin K) : Expr :=
  project (chart base a K M) (.lookup prior .row) slot

/-- One dictionary serves every block, operand and field. The old bank is
read independently on each physical row, including the final partial group. -/
theorem header_source (base : ℕ) (prior : Bank) (slot : Fin K) (out : ℕ) (m : Memory w)
    (values : Fin H→Fin G→Cell (a*K)) (before : prior.Fits w base)
    (capacity : H*chunks G M≤ prior.size) (read : Reads prior values M m)
    (low : base+K*2^((a*K)*M)≤ out) (room : out<2^w) :
    let mid:=ROM.after (pages a K M) ((a*K)*M) base m
    (headerExpr base a K M prior slot).Fits w out ∧
      Source (headerExpr base a K M prior slot) (fun h g=>take slot (values h g)) M mid := by
  intro mid
  have bounds : (chart base a K M slot).Fits w out :=
    ROM.bank_room (pages a K M) _ base out slot le_rfl low room
  have old : prior.Fits w out := ⟨before.1,before.2.1,
    before.2.2.trans ((Nat.le_add_right ..).trans low)⟩
  have stayed : Reads prior values M mid := by
    intro r
    have addr : prior.base+(row H G M r).val<base :=
      (Nat.add_lt_add_left ((row H G M r).isLt.trans_le capacity) _).trans_le before.2.2
    exact (ROM.frame _ _ _ m _ (.inl addr)).trans (read r)
  exact ⟨⟨bounds,old,trivial⟩,fetched (chart base a K M) (.lookup prior .row) slot out mid values
    (source_column _ out old mid _ capacity stayed) bounds rfl (initialized base a K M m slot)⟩

theorem header_dictionary (a K M base : ℕ) (m : Memory w)
    (room : base+K*2^((a*K)*M)<2^w) :
    let work:=K*2^((a*K)*M)
    let code:=ROM.mount (pages a K M) ((a*K)*M) w base
    code.Exec m (ROM.after (pages a K M) ((a*K)*M) base m) (4+10*work) ∧
      DescentStaticWordColumn.names code=15*(work+1) ∧ CheapCode code := by
  obtain ⟨ran,names⟩:=ROM.run (pages a K M) ((a*K)*M) base m room
  exact ⟨ran,names,ROM.cheap _ _ _ _⟩

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
