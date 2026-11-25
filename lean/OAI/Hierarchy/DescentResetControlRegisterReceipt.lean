import OAI.Hierarchy.DescentResetControlRegisterWords

namespace OAI
namespace Hierarchy.DescentResetControlRegisters.Chart
open DescentSIMDLookup DescentPackedZip DescentVenueQuantityPlanes ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (c : Chart) (base : ℕ) {w : ℕ}
local notation "p" => c.dims
local notation "M" => c.dims.lanes
local notation "H" => c.dims.hosts
local notation "G" => c.dims.groups
local notation "rows" => H*chunks G M
local notation "raw" => c.dims.oldHosts*c.dims.shapes

theorem sections (roof : c.endAddress base<2^w) :
    (bank (c.first base) rows).Fits w (c.endAddress base) ∧
    (bank (c.oldHost base) raw).Fits w (c.endAddress base) ∧
    (bank (c.shape base) raw).Fits w (c.endAddress base) ∧
    (⟨c.scale base,c.bits⟩:Bank).Fits w (c.endAddress base) ∧
    (⟨c.table base,c.bits+M⟩:Bank).Fits w (c.endAddress base) :=by
  have end_:c.first base+span rows+span raw+span raw+2^c.bits+2^(c.bits+M)<2^w:=roof
  simp only [Bank.Fits,Bank.size,bank,endAddress,table,scale,shape,oldHost,span] at *
  have scalarPos := Nat.two_pow_pos c.bits
  have tablePos := Nat.two_pow_pos (c.bits+M)
  have rowPos := Nat.two_pow_pos (Nat.clog 2 rows)
  have rawPos := Nat.two_pow_pos (Nat.clog 2 raw)
  refine ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,⟨Nat.two_pow_pos _,by omega,by omega⟩,
    ⟨Nat.two_pow_pos _,by omega,by omega⟩,⟨Nat.two_pow_pos _,by omega,by omega⟩,
    ⟨Nat.two_pow_pos _,by omega,le_rfl⟩⟩

theorem active_fits (x : Fin (p).blocks) (space : c.endAddress base<2^w) :
    (c.active base x.val).Fits w (c.endAddress base):=by
  have start:State.out p base+(p).blocks*rows≤c.first base:=
    Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1 < 2) _) _
  have xsmall:=Nat.mul_le_mul_right rows (Nat.le_of_lt x.isLt)
  have rowBank := (c.sections base space).1
  have before := (Nat.add_le_add_left xsmall (State.out p base)).trans start
  exact ⟨⟨Nat.two_pow_pos _,rowBank.2.1,(Nat.add_le_add_right before (span rows)).trans rowBank.2.2⟩,trivial⟩

theorem physical_inputs (old count inverse : Bank) (m : Memory w) (roof : c.endAddress base<2^w)
    (x : Fin (p).blocks) (xdata : Fin H→Fin G→Cell 1)
    (measured : ∀j : Row H G M,
      DescentVenueQuantityPlanes.image p (State.layout p base old count inverse) m
        (State.out p base+x.val*rows+(row H G M j).val)=((data xdata j).val:Word w)) :
    let final:=(c.phase base old count inverse w).image m
    Source (c.active base x.val) xdata M final ∧
    ∀e : Expr,∀j : Row H G M,
      let t:=(e.eval final ((row H G M j).val:Word w)).val%2^c.bits
      (c.broadcast base x.val e).eval final ((row H G M j).val:Word w)=
        ((data (fun h g=>if xdata h g=0 then 0 else (t:Cell c.bits)) j).val:Word w):=by
  intro final
  let firstState:=DescentVenueQuantityPlanes.image p (State.layout p base old count inverse) m
  have saved:Source (c.active base x.val) xdata M final:=by
    apply source_column _ (c.endAddress base) (c.active_fits base x roof).1 final xdata (Nat.le_pow_clog (by decide : 1 < 2) _)
    intro j
    have ir: (row H G M j).val<rows:=(row H G M j).isLt
    have bound : x.val*rows+(row H G M j).val<(p).blocks*rows:=by
      calc
        _<(x.val+1)*rows:=by rw [Nat.add_mul,one_mul];omega
        _≤_:=Nat.mul_le_mul_right _ x.isLt
    have low : State.out p base+x.val*rows+(row H G M j).val<c.first base:=by
      have total:(p).blocks*rows≤State.rounded (State.newRows p):=Nat.le_pow_clog (by decide : 1 < 2) _
      change _<State.out p base+State.rounded (State.newRows p)
      omega
    exact (DescentStaticWordColumn.frame (c.first base) c.count c.literal firstState _ (.inl low)).trans (measured j)
  refine ⟨saved,?_⟩
  intro e j
  exact (c.broadcast_read base final (c.resident base old count inverse m) roof x.val e _ _ (saved j)).trans
    (congrArg (fun v : Cell (c.bits*M)=>(v.val:Word w)) (c.data_at xdata _ j))

end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
