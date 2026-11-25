import OAI.Hierarchy.DescentDatedMaterialSockets

namespace OAI
/-! The original rack reads the same forward path and normalized low endpoint before routing the source rank. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e" => v.material
local notation "s" => v.ticket.depotShape v.short
local notation "P₀" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "b" => v.material.fieldBits
local notation "H" => v.material.oldHosts
local notation "M" => v.material.lanes
local notation "B" => v.material.blocks
local notation "G₁" => v.material.groups

def originSocket (base : ℕ) (seat : DepotRAM.Material.Seat s) (x : Fin B) (low : Bool) : Expr :=
  v.materialProgram.originSocket base seat x low

theorem origin_work (base : ℕ) (seat : DepotRAM.Material.Seat s) (x : Fin B) (low : Bool) :
    (v.originSocket base seat x low).work=12:=rfl

theorem socket_work (base : ℕ) (ranks : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P₀)
    (p : Fin P₀) (seat : DepotRAM.Material.Seat s) (i : Fin B) (f : Port) :
    (v.materialSocket base ranks ports p seat i f).work=88:=rfl

private theorem zeros {w : ℕ} (hosts G lanes a : ℕ) (m : Memory w) : Source (.lit 0) (fun (_:Fin hosts) (_:Fin G)=>(0:Cell a)) lanes m :=by
  intro p
  have blank : encode a lanes (fun _ => 0) = 0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin lanes=>(0:Cell a))).val=0
    simp []
  simp [Expr.eval,data,blank]

private theorem cast_prior {hosts J K a lanes w : ℕ} (eqn : J=K) (z : Fin hosts→Fin J→Cell a)
    (src : Bank) (mem : Memory w) (read : Reads src z lanes mem) :
    Reads src (fun h (g : Fin K)=>z h (Fin.cast eqn.symm g)) lanes mem :=by subst K; exact read

variable {base w : ℕ} {parts reverse : Bank} (ok : v.MaterialRoom base parts reverse w) (m : Memory w)
variable (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts)) (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
local notation "result" => NativePhase.image (v.materialAt base parts reverse w) m
local notation "cal" => DepotRAM.Material.reverseEntries s R
local notation "rev" => fun h (_:Fin v.material.oldGroups)=>digest (cal h)
local notation "fields" => DepotRAM.Material.Sheets.fields s v.materialFormat state rev

include ok in
theorem material_origin_issued (pos : 0<(e).oldLanes) (lanes : 0<M) (blocks : 0<B) (bands : (e).oldGroups=G₁*B)
    (rank : ∀h p,m (reverse.base+(finProdFinEquiv (h,p)).val)=((cal h p).val:Word w))
    (old : Reads parts (fun h g=>DepotRAM.combine s (state h g)) (e).oldLanes m)
    (seat : DepotRAM.Material.Seat s) (x : Fin B) (low : Bool) (out : ℕ)
    (letBank : (v.receivedBank base (DepotRAM.Material.Sheets.id s (if low then 2 else 0) seat)).Fits w out)
    (rows : H*chunks G₁ M≤(v.receivedBank base (DepotRAM.Material.Sheets.id s (if low then 2 else 0) seat)).size)
    (ends : (e).endAddress base≤out) (room : out<2^w) :
    Source (v.originSocket base seat x low)
      (fun h g=>((fields (DepotRAM.Material.Sheets.id s (if low then 2 else 0) seat) h
        (Fin.cast bands.symm (finProdFinEquiv (g,x)))).val:Cell (Projection.launchWidth (e).reach B v.materialPitch low))) M result :=by
  let f : Fin 9:=if low then 2 else 0
  let j:=DepotRAM.Material.Sheets.id s f seat
  let src:=v.receivedBank base j
  let addr:=(e).projectionStart base
  let launch:=Projection.launchBank b B M addr low x
  let prior:=(((v.materialCharts base w).seq (v.materialJoin base parts reverse w)).seq (v.materialSheets base w)).seq
    ((v.materialJob base).phase ((e).overlapStart base) w)
  have seen:=cast_prior bands (fields j) src result (v.material_issued ok m R state pos rank old j)
  let vals : Fin H → Fin (G₁*B) → Cell b := fun h g=>fields j h (Fin.cast bands.symm g)
  have packed: Reads src (groupedRows vals) M result:=regroup_read lanes blocks src.base result vals seen
  have shared (d : Cell ((b*B)*M)): result (launch.base+d.val)=
      ((Projection.launchValue (e).reach b B M v.materialPitch low x d).val:Word w):=by
    change (Projection.stage H (e).hosts G₁ M (e).reach b B v.materialPitch addr w).image (prior.image m) _ = _
    rw [ok.sameReach]
    exact Projection.launch_installed (D:=(s).degree) H (e).hosts G₁ M b B v.materialPitch addr (prior.image m) low x d
  have lower : Projection.mapBase b B M addr≤out:=by
    calc
      _ ≤ Projection.markBase b B M (e).hosts G₁ addr := Nat.le_add_right ..
      _ ≤ Projection.roof b B M (e).hosts G₁ (e).reach addr := Nat.le_add_right ..
      _ = (e).endAddress base := v.stampedRoof base
      _ ≤ out := ends
  have endLaunch : launch.base+launch.size≤out:=(Projection.launch_before b B M addr low x).trans lower
  have launchFit : launch.Fits w out:=⟨Nat.two_pow_pos _,
    (Nat.le_add_left _ _).trans_lt (endLaunch.trans_lt room),endLaunch⟩
  have stored:=source_column src out letBank result _ rows packed
  intro t
  let d:=data («M»:=M) (groupedRows vals) t
  change launch.read result ((Expr.lookup src .row).eval result ((row H G₁ M t).val:Word w))=_
  rw [stored t,bank_read launch result (show d.val<launch.size from d.isLt) launchFit,shared d]
  apply congrArg (fun z:Cell ((Projection.launchWidth (e).reach B v.materialPitch low)*M)=>(z.val:Word w))
  unfold Projection.launchValue DescentSIMDLookup.table
  apply congrArg (encode _ M)
  funext i
  simp only [d,data,Equiv.symm_apply_apply,Function.comp_apply]
  split
  next hi =>
    let g : Fin G₁ := ⟨t.2.val*M+i.val,hi⟩
    let digits : Fin B → Cell b := fun k => vals t.1 (finProdFinEquiv (g,k))
    have digit := congrFun ((encode b B).symm_apply_apply digits) x
    exact congrArg (fun q : Cell b => (q.val : Cell (Projection.launchWidth (e).reach B v.materialPitch low))) digit
  next hi=>simp [Projection.narrow,choose_empty]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
