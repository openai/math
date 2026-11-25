import OAI.Hierarchy.DescentResetPrimaryRange
import OAI.Hierarchy.DescentRecordedControlSources
import OAI.Hierarchy.DescentPublicOperandRows
import OAI.Hierarchy.DescentResetStemStoredChart

namespace OAI
/-! # Original private and public shape registers at an occupied retained receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentSIMDLookup DescentPackedZip
open DescentPackedColony DescentVenueQuantityPlanes DescentResetControlRegisters
open Computability.VPVNP.BurstRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {old : Reached W G q ε S k i z D wire hist} {rates : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset old rates) {oldH H oldM M w a : ℕ}
    (previous : Fintype.card old.V ≤ oldH) (next : Fintype.card B.next.V ≤ H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "J" => S.groupCount (i+1)
local notation "cap" => old.placement.cap
local notation "chosen" => B.next.vertex.trans (Fin.castLEEmb next)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb previous)
local notation "shapeId" v:arg => ((Z).hostFields T rank v).2.val
local notation "depthAt" v:arg => (Z).placement.b (DescentDenseHostOrder.position (Z).graph (v).val)
local notation "dims" => quantityDims B 1 oldH H oldM M
local notation "c" => (⟨dims,a⟩ : Chart)
local notation "values" x:arg => fun h g=>actualBit B next h g x

theorem shape_register_at (v : B.next.V) (group_ : Fin J) (x : DescentColonies.Block k)
    (active : actualBit B next (chosen v) group_ x ≠ 0)
    (fits : shapeId v < 2^a) :
    ((⟨dims,a⟩:Chart).enabled (values x) (controlScalar B previous next 3) (chosen v) group_).val =
      (localRank (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g) ((Z).localShape T v)).val := by
  have found : ∃y,chosen y=chosen v:=⟨v,rfl⟩
  have selected : controlReceiver B next (chosen v)=some v:=by
    unfold controlReceiver
    rw [dite_eq_left found]
    exact congrArg some ((chosen).injective found.choose_spec)
  have value : controlScalar B previous next 3 (chosen v) = shapeId v := by
    unfold controlScalar
    rw [selected]
    rfl
  change (if actualBit B next (chosen v) group_ x=0 then (0:Cell a) else
    (controlScalar B previous next 3 (chosen v):Cell a)).val = shapeId v
  rw [ite_eq_right active, value]
  exact Fin.val_cast_of_lt fits

/-- The fourth mask-selected physical register is the secondary coordinate of
the actual sparse inverse directory, even when several new sites share an old host. -/
theorem sparse_register_at (v : B.next.V) (group_ : Fin J) (x : DescentColonies.Block k)
    (active : actualBit B next (chosen v) group_ x ≠ 0)
    (fits : shapeId v < 2^a) :
    ((⟨dims,a⟩:Chart).enabled (values x) (controlScalar B previous next 3) (chosen v) group_).val =
      (finProdFinEquiv.symm ((Z).rawAtIndex T rank (B.next.vertex v)) :
        Fin oldH × Fin (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card).2.val := by
  have atId : B.next.vertex v=(Z).denseHostRank T rank v:=
    Fin.ext (dense_physical B previous v).symm
  have direct := (congrArg ((Z).rawAtIndex T rank) atId).trans ((Z).rawAtIndex_at T rank v)
  let secondary (i : Fin (oldH*(DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card)) :=
    (finProdFinEquiv.symm i : Fin oldH × Fin (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card).2.val
  have invert := congrArg (fun t : Fin oldH × Fin (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card => t.2.val)
    (finProdFinEquiv.symm_apply_apply ((Z).hostFields T rank v))
  exact (shape_register_at B previous next v group_ x active fits).trans ((congrArg secondary direct).trans invert).symm

/-- At any scanned host the paid active bit and register word either vanish together,
or the emitted fourth register names the same raw receiver as the compact directory. -/
theorem recorded_dispatch (h₀ : Fin H) (group_ : Fin J) (x : DescentColonies.Block k)
    (wide : 0<a) (fit : ∀v : B.next.V,shapeId v < 2^a) :
    let mask:=values x
    let active:=(⟨dims,a⟩:Chart).enabled mask (fun _=>1) h₀ group_
    let reg:=fun j : Fin 4=>(⟨dims,a⟩:Chart).enabled mask (controlScalar B previous next j) h₀ group_
    (active.val=0 → (reg 1).val=0) ∧
      ∀hv : h₀.val<Fintype.card B.next.V,active.val≠0 →
        (reg 3).val=(finProdFinEquiv.symm ((Z).rawAtIndex T rank ⟨h₀.val,hv⟩) :
          Fin oldH × Fin (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card).2.val := by
  intro mask active reg
  have one : (1:Cell a).val=1:=Fin.val_cast_of_lt (one_lt_pow₀ (by decide : 1<(2:ℕ)) wide.ne')
  by_cases blank : mask h₀ group_=0
  · simp [active,reg,DescentResetControlRegisters.Chart.enabled,blank]
  have live : active.val≠0:=by
    change (if mask h₀ group_=0 then (0:Cell a) else (1:Cell a)).val ≠ 0
    rw [ite_eq_right blank,one]
    decide
  refine ⟨fun denied=>False.elim (live denied),?_⟩
  intro hv _
  have perm : Function.Surjective B.next.vertex :=
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨B.next.vertex.injective,by simp⟩).surjective
  obtain ⟨v,hit⟩:=perm ⟨h₀.val,hv⟩
  have atHost : chosen v=h₀ := by
    apply Fin.ext
    change (B.next.vertex v).val=h₀.val
    exact congrArg (fun j : Fin (Fintype.card B.next.V) => j.val) hit
  have occupied : actualBit B next (chosen v) group_ x≠0:=by simpa only [atHost] using blank
  have actual:=sparse_register_at (oldM:=oldM) (M:=M) B previous next v group_ x occupied (fit v)
  let value (u : Fin H) := ((⟨dims,a⟩:Chart).enabled (values x) (controlScalar B previous next 3) u group_).val
  let address (u : Fin (Fintype.card B.next.V)) := (finProdFinEquiv.symm ((Z).rawAtIndex T rank u) :
    Fin oldH × Fin (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card).2.val
  exact (congrArg value atHost).symm.trans (actual.trans (congrArg address hit))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation "banks" w => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload
local notation "idx" => menu.publicInputIndex



theorem public_header_register {H K : ℕ} (values : (ports).Values H K)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin K) (j : Fin 8) :
    ((cfg).oldConfig.header ((cfg).basic
      (menu.publicData sh floor count hub g Y active reg values digits x h g₀)) j).val =
      ((ports).value values x h g₀ (DescentResetPublicOperandBook.Config.headerPort j)).val := by
  let i:=((cfg).oldConfig.ports (v).middle.rotorBits) (.inl (.inl j))
  have read:=menu.publicData_val sh floor count hub g Y active reg values digits x h g₀
    (Fin.castAdd (cfg).extraCount i)
  rw [DescentResetPublicOperandBook.Config.port_basic] at read
  change (menu.publicData sh floor count hub g Y active reg values digits x h g₀ (Fin.castAdd (cfg).extraCount i)).val = _
  simpa only [i,Equiv.symm_apply_apply] using read

theorem public_control_registers {H K : ℕ} (values : (ports).Values H K)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin K) (j : Fin 4) :
    (((cfg).reg (menu.publicData sh floor count hub g Y active reg values digits x h g₀)) j).val =
      (values.register j h g₀).val := by
  have all:=menu.public_header_register sh floor count hub g Y active reg values digits x h g₀
  fin_cases j
  · exact all 1
  · exact all 4
  · exact all 5
  · exact all 2

theorem public_shape_register {H K : ℕ} (values : (ports).Values H K)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin K) :
    ((cfg).oldConfig.header ((cfg).basic
      (menu.publicData sh floor count hub g Y active reg values digits x h g₀)) 2).val =
      (values.register 3 h g₀).val :=
  menu.public_header_register sh floor count hub g Y active reg values digits x h g₀ 2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
