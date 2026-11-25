import OAI.Hierarchy.DescentResetReaderTables

namespace OAI
/-! # Installing all finite lookup pages used to read the reset stencil -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil.ReaderTables.Chart
open DescentGL DescentColonies DescentPackedColony DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel
open DescentPacking.PackedMatch.Local DescentPackedColony.Phase
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w q : ℕ} (C : ReaderTables.Chart)

/-- The dynamic operands are inherited verbatim. All decoder banks use the dated public layout. -/
def inputs (P : Inputs C.m C.c q) : Inputs C.m C.c q :=
  { P with
    broadcastBank:=C.column (.inl ())
    mask:=C.mask
    amount:=fun x=>C.column (.inr (.inl (.inl x)))
    vote:=fun d x=>C.column (.inr (.inl (.inr (d,x))))
    compare:=fun i x=>C.column (.inr (.inr (i,x)))
    planeTables:=StencilTables.tabs C.planeBase (2^C.r) C.m C.M }

abbrev planes : Arena.Image w := StencilTables.image C.planeBase (2^C.r) C.m C.M

theorem before_planes : C.origin≤C.planeBase:=by dsimp [planeBase,first];omega

theorem prepared (P : Inputs C.m C.c q) (out : ℕ) (mem : Memory w)
    (safe : C.stop≤out) (space : out<2^w) (word : C.n*C.M≤w)
    (live : ∀d,(P.planes d).Fits w out)
    (scalar : C.image.Resident mem) (plane : C.planes.Resident mem) :
    ReadersROM (C.inputs P) C.n C.b C.M C.H w out mem := by
  let tabs:=StencilTables.tabs C.planeBase (2^C.r) C.m C.M
  have endSlot (j : ReaderTables.Key C.r) : (C.column j).Fits w out := by
    have limit:=(C.column_end j).trans (C.plane_le.trans safe)
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (limit.trans_lt space),limit⟩
  have maskEnd : C.origin+C.mask.size≤out:=(Nat.le_add_right C.first _).trans (C.plane_le.trans safe)
  have maskFits : C.mask.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (maskEnd.trans_lt space),maskEnd⟩
  refine ⟨endSlot _,maskFits,rfl,C.mask_card,word,⟨?_,C.mask_read mem scalar⟩,?_,?_,?_,?_,?_⟩
  · exact C.cell_read (.inl ()) mem scalar
  · intro x
    exact ⟨endSlot _,rfl,C.cell_read (.inr (.inl (.inl x))) mem scalar⟩
  · intro d x
    exact ⟨endSlot _,rfl,C.cell_read (.inr (.inl (.inr (d,x)))) mem scalar⟩
  · intro i
    let e:=(2^C.r*C.m+2^C.r)*C.M
    have small : 2^(2^C.r*C.m*C.M)≤2^e :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right C.M (Nat.le_add_right ..))
    have pos : 0<2^e:=Nat.two_pow_pos _
    have upl : (tabs i).apply.base+(tabs i).apply.size≤out:=by
      dsimp [tabs,StencilTables.tabs,StencilTables.start,Bank.size]
      change C.planeBase+(i.val+1)*2^e+2^e≤out
      change C.planeBase+(C.m+1)*2^e≤out at safe
      rw [Nat.add_assoc, ← Nat.succ_mul]
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (show (i.val+1)+1≤C.m+1 by omega)) _).trans safe
    have shiftEnd : C.planeBase+2^(2^C.r*C.m*C.M)≤out:=by
      change C.planeBase+(i.val+1)*2^e+2^e≤out at upl
      omega
    exact ⟨live i,⟨Nat.two_pow_pos _,by change 2^(2^C.r*C.m*C.M)<2^w;omega,shiftEnd⟩,
      ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (upl.trans_lt space),upl⟩,rfl,rfl⟩
  · exact StencilTables.reads C.planeBase (2^C.r) C.m C.M mem plane
  · intro i x
    exact ⟨endSlot _,rfl,C.cell_read (.inr (.inr (i,x))) mem scalar⟩

theorem issue_readers (P : Inputs C.m C.c q) (out : ℕ) (mem : Memory w)
    (safe : C.stop≤out) (space : out<2^w) (word : C.n*C.M≤w) (live : ∀d,(P.planes d).Fits w out) :
    let I:Arena.Image w:=C.image
    let J:Arena.Image w:=C.planes
    let dst:=J.output (I.output mem)
    (I.program.seq J.program).Exec mem dst (8+10*(C.stop-C.origin)) ∧
    ReadersROM (C.inputs P) C.n C.b C.M C.H w out dst ∧
    (∀a,a<C.origin ∨ C.stop≤a→dst a=mem a) ∧ CheapCode (I.program.seq J.program) := by
  dsimp only
  have sep:=C.before_planes
  have last:=C.plane_le
  have ir : C.origin+(C.planeBase-C.origin)<2^w:=by omega
  have jr : C.planeBase+(C.stop-C.planeBase)<2^w:=by omega
  obtain ⟨exec,scalar,plane,frame,cheap,_⟩:=C.image.pair (C.planes (w:=w)) mem (Or.inl le_rfl) ir jr
  refine ⟨?_,C.prepared P out _ safe space word live scalar plane,?_,cheap⟩
  · have n : (C.image (w:=w)).length+(C.planes (w:=w)).length=C.stop-C.origin:=by
      change C.planeBase-C.origin+(C.stop-C.planeBase)=C.stop-C.origin
      omega
    rw [← n]
    intro labels registers cells machine
    exact @exec labels registers cells machine
  · intro a h
    exact frame a (by change a<C.origin∨C.planeBase≤a;omega) (by change a<C.planeBase∨C.stop≤a;omega)

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil.ReaderTables.Chart

end OAI
