import OAI.Hierarchy.DescentDatedNodeMetadataChart
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # The two initial node pages from the public singleton-node seed chart -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : DescentDatedNodeMetadata.Chart)

def seedDigit (Q : Fin v.hosts→Option ℕ) (f : Fin 2) (h : Fin v.hosts) (n : Fin v.nodes) : Cell v.bits :=
  if n.val=0 then (Q h).elim 0 (fun width=>if f.val=0 then 1 else (width:Cell v.bits)) else 0

def seedField (Q : Fin v.hosts→Option ℕ) (f : Fin 2) (h : Fin v.hosts) (_ : Fin v.groups) : Cell (v.bits*v.nodes) :=
  encode v.bits v.nodes (v.seedDigit Q f h)

def seedLiteral (Q : Fin v.hosts→Option ℕ) (j : ℕ) : ℕ :=
  if hj : j<v.names*v.rows then
    let p : Fin v.names×Fin v.rows:=finProdFinEquiv.symm ⟨j,hj⟩
    let fx : Fin 2×Fin v.blocks:=finProdFinEquiv.symm p.1
    let rowId : Row v.hosts v.groups v.lanes:=(row v.hosts v.groups v.lanes).symm p.2
    (data (v.seedField Q fx.1) rowId).val
  else 0

def seedProgram (base w : ℕ) (Q : Fin v.hosts→Option ℕ) := DescentStaticWordColumn.program w base (v.seedLiteral Q) (v.names*v.rows)
def seedImage (base : ℕ) (Q : Fin v.hosts→Option ℕ) (m : Memory w) := DescentStaticWordColumn.image base (v.seedLiteral Q) m (v.names*v.rows)
def seedTicks :=4+10*(v.names*v.rows)

theorem seedCheap (base w : ℕ) (Q : Fin v.hosts→Option ℕ) : CheapCode (v.seedProgram base w Q) :=by apply DescentStaticWordColumn.cheap

theorem seedIssued (base : ℕ) (Q : Fin v.hosts→Option ℕ) (m : Memory w) (space : v.seedEnd base<2^w) :
    (v.seedProgram base w Q).Exec m (v.seedImage base Q m) v.seedTicks ∧
    (∀a,a<base ∨ v.seedEnd base≤a→v.seedImage base Q m a=m a) ∧ CheapCode (v.seedProgram base w Q) :=by
  have finish : base+v.names*v.rows≤v.seedEnd base:=Nat.le_add_right ..
  exact ⟨DescentStaticWordColumn.mount base (v.names*v.rows) (v.seedLiteral Q) m (finish.trans_lt space),
    fun a off=>DescentStaticWordColumn.frame _ _ _ _ _ (off.imp_right (finish.trans ·)),v.seedCheap base w Q⟩

theorem seedRead (base : ℕ) (Q : Fin v.hosts→Option ℕ) (m : Memory w) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.seedBank base f x) (v.seedField Q f) v.lanes (v.seedImage base Q m) :=by
  intro p
  let r : Fin v.rows:=row v.hosts v.groups v.lanes p
  let j : Fin (v.names*v.rows):=finProdFinEquiv (v.slot f x,r)
  have address : (v.seedBank base f x).base+r.val=base+j.val:=by
    change base+(v.slot f x).val*v.rows+r.val=base+(r.val+v.rows*(v.slot f x).val)
    ring
  change v.seedImage base Q m ((v.seedBank base f x).base+r.val)=_
  rw [address,show v.seedImage base Q m (base+j.val)=(v.seedLiteral Q j.val:Word w) from
    DescentStaticWordColumn.read _ _ _ _ j.isLt]
  rw [seedLiteral,dite_eq_left j.isLt]
  change ((data (v.seedField Q (finProdFinEquiv.symm (finProdFinEquiv.symm j).1).1) ((row v.hosts v.groups v.lanes).symm (finProdFinEquiv.symm j).2)).val:Word w)=_
  simp only [j,slot,Equiv.symm_apply_apply,r]

theorem seedFit (base : ℕ) (f : Fin 2) (x : Fin v.blocks) (space : v.seedEnd base<2^w) :
    (v.seedBank base f x).Fits w (v.seedEnd base) ∧ v.rows≤(v.seedBank base f x).size :=by
  have idx:=Nat.mul_le_mul_right v.rows (v.slot f x).isLt.le
  have edge : (v.seedBank base f x).base+(v.seedBank base f x).size≤v.seedEnd base:=by
    change base+(v.slot f x).val*v.rows+v.rounded≤base+v.names*v.rows+v.rounded;omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (edge.trans_lt space),edge⟩,
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

theorem seedPrice (base w : ℕ) (Q : Fin v.hosts→Option ℕ) :
    v.seedTicks+7*DescentStaticWordColumn.names (v.seedProgram base w Q)=109+115*(v.names*v.rows) :=by
  rw [seedProgram,DescentStaticWordColumn.names_mount];unfold seedTicks;ring

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
