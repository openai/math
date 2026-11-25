import OAI.Hierarchy.DescentResetControlPortRead

namespace OAI
/-! # The four compact receiver registers are masked separately in each group -/
namespace Hierarchy.DescentResetControlRegisters.Chart
open ProtocolRAM DescentSIMDLookup DescentPackedZip DescentVenueQuantityPlanes
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (c : Chart) (base : ℕ) {w : ℕ}
local notation "p" => c.dims
local notation "M" => c.dims.lanes
local notation "H" => c.dims.hosts
local notation "G" => c.dims.groups
local notation "S" => c.dims.shapes
local notation "raw" => c.dims.oldHosts*S
local notation "roof" => c.endAddress base

theorem port_fits (x : Fin (p).blocks) (cap : ℕ) (inverse depth levels : Bank) (space : roof<2^w)
    (iFit : inverse.Fits w roof) (dFit : depth.Fits w roof) (lFit : levels.Fits w roof) :
    (c.live base x.val).Fits w roof ∧ ∀j,(c.ports base cap x.val inverse depth levels j).Fits w roof :=by
  obtain ⟨rf,old,shape,scale,table⟩:=c.sections base space
  have index : (c.hostId base inverse).Fits w roof:=⟨iFit,rf,trivial⟩
  have act:=c.active_fits base x space
  have broadcast (e : Expr) (fit : e.Fits w roof) : (c.broadcast base x.val e).Fits w roof :=
    ⟨table,⟨scale,fit⟩,act⟩
  refine ⟨broadcast (.lit 1) trivial,?_⟩
  intro j
  fin_cases j
  · exact broadcast (.lit cap) trivial
  · exact broadcast _ ⟨lFit,dFit,old,index⟩
  · trivial
  · exact broadcast _ ⟨shape,index⟩

private theorem at_host {b H₀ G₀ M₀} (q : Row H₀ G₀ M₀) {f g : Fin H₀→Fin G₀→Cell b}
    (same : ∀k,f q.1 k=g q.1 k) : data f q=data g q :=by
  apply congrArg (encode b M₀)
  funext j
  split <;> simp_all

def enabled (mask : Fin H→Fin G→Cell 1) (v : Fin H→ℕ) (h : Fin H) (g : Fin G) : Cell c.bits :=
  if mask h g=0 then 0 else (v h:Cell c.bits)

/-- No raw actor is read for an absent compact host. Each word in that row has a zero mask,
including groups in the padded last machine word. -/
theorem source_ports_read {ι : Type*} (x : Fin (p).blocks) (cap : ℕ) (inverse depth levels : Bank)
    (m : Memory w) (keep : c.Resident base m) (space : roof<2^w)
    (iFit : inverse.Fits w roof) (dFit : depth.Fits w roof) (lFit : levels.Fits w roof)
    (mask : Fin H→Fin G→Cell 1) (occupied : Source (c.active base x.val) mask M m)
    (host : Fin H→Option ι) (lev shape : ι→ℕ)
    (absent : ∀h,host h=none→∀g,mask h g=0)
    (readAt : ∀q : Row H G M,∀v,host q.1=some v →
      (c.live base x.val).eval m ((row H G M q).val:Word w)=((c.withMask (data mask q) 1).val:Word w) ∧
      ∀i,(c.ports base cap x.val inverse depth levels i).eval m ((row H G M q).val:Word w)=
        ((c.withMask (data mask q) (![cap,lev v,0,shape v] i)).val:Word w)) :
    let dirs:=fun (i : Fin 4) (h : Fin H)=>(host h).elim 0 (fun v=>![cap,lev v,0,shape v] i)
    ((c.live base x.val).Fits w roof ∧ Source (c.live base x.val) (c.enabled mask (fun _=>1)) M m) ∧
    ∀i,(c.ports base cap x.val inverse depth levels i).Fits w roof ∧
      Source (c.ports base cap x.val inverse depth levels i) (c.enabled mask (dirs i)) M m :=by
  let dirs:=fun (i : Fin 4) (h : Fin H)=>(host h).elim 0 (fun v=>![cap,lev v,0,shape v] i)
  have code:=c.port_fits base x cap inverse depth levels space iFit dFit lFit
  have live (q : Row H G M) (t : ℕ) :
      c.withMask (data mask q) t=data (c.enabled mask (fun _=>t)) q := c.data_at mask t q
  have agree (q : Row H G M) (t : ℕ) (v : Fin H→ℕ)
      (same : t=v q.1 ∨ ∀g,mask q.1 g=0) :
      c.withMask (data mask q) t=data (c.enabled mask v) q :=by
    rw [live]
    apply at_host
    intro g
    rcases same with h|h
    · simp [enabled,h]
    · simp [enabled,h g]
  have blank (q : Row H G M) (off : host q.1=none) (e : Expr) (v : Fin H→ℕ) :
      (c.broadcast base x.val e).eval m ((row H G M q).val:Word w)=((data (c.enabled mask v) q).val:Word w) :=by
    rw [c.broadcast_read base m keep space x.val e _ _ (occupied q),agree q _ v (.inr (absent _ off))]
  have zero (q : Row H G M) : (((data (c.enabled mask (dirs 2)) q).val:ℕ):Word w)=0 :=by
    have muted (h g) : c.enabled mask (dirs 2) h g=0 :=by
      cases got:host h <;> simp [enabled,dirs,got]
    have dead : data (c.enabled mask (dirs 2)) q = encode c.bits M (fun _=>0) :=by
      apply congrArg (encode c.bits M)
      funext j
      split <;> simp [muted]
    rw [dead]
    simp [encode]
  constructor
  · refine ⟨code.1,?_⟩
    intro q
    cases h:host q.1 with
    | none=>exact blank q h (.lit 1) _
    | some v=>
      have read :=readAt q v h
      rw [read.1,live]
  · intro i
    refine ⟨code.2 i,?_⟩
    intro q
    cases h:host q.1 with
    | some v=>
      have read:=readAt q v h
      rw [read.2 i,agree q _ (dirs i) (.inl (by simp [dirs,h]))]
    | none=>
      fin_cases i
      · exact blank q h (.lit cap) _
      · exact blank q h _ _
      · exact (zero q).symm
      · exact blank q h _ _

theorem source_ports (x : Fin (p).blocks) (cap : ℕ) (inverse depth levels : Bank)
    (m : Memory w) (keep : c.Resident base m) (space : roof<2^w)
    (iFit : inverse.Fits w roof) (dFit : depth.Fits w roof) (lFit : levels.Fits w roof)
    (mask : Fin H→Fin G→Cell 1) (occupied : Source (c.active base x.val) mask M m)
    (host : Fin H→Option (Fin raw)) (lev : Fin raw→ℕ) (depthOf : Fin raw→ℕ)
    (idAt : ∀q : Row H G M,∀v,host q.1=some v→
      (c.hostId base inverse).eval m ((row H G M q).val:Word w)=(v.val:Word w))
    (absent : ∀h,host h=none→∀g,mask h g=0)
    (fitsDepth : ∀v : Fin raw,v.val/S<depth.size)
    (depthAt : ∀v : Fin raw,m (depth.base+v.val/S)=(depthOf v:Word w))
    (fitsLevel : ∀v,depthOf v<levels.size)
    (levelAt : ∀v,m (levels.base+depthOf v)=(lev v:Word w))
    (fits : ∀v : Fin raw,∀t∈[1,cap,lev v,v.val%S],t<2^c.bits) :
    let dirs:=fun (i : Fin 4) (h : Fin H)=>(host h).elim 0 (fun v=>![cap,lev v,0,v.val%S] i)
    ((c.live base x.val).Fits w roof ∧ Source (c.live base x.val) (c.enabled mask (fun _=>1)) M m) ∧
    ∀i,(c.ports base cap x.val inverse depth levels i).Fits w roof ∧
      Source (c.ports base cap x.val inverse depth levels i) (c.enabled mask (dirs i)) M m :=by
  apply c.source_ports_read base x cap inverse depth levels m keep space iFit dFit lFit mask occupied host lev
    (fun v=>v.val%S) absent
  intro q v seen
  exact c.ports_read base m keep space x.val cap inverse depth levels q
    (data mask q) (occupied q) v (idAt q v seen) (depthOf v) (lev v) (fitsDepth v) (depthAt v)
    dFit lFit (fitsLevel v) (levelAt v) (fits v)

end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
