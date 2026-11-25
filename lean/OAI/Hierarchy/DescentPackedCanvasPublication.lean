import OAI.Hierarchy.DescentPackedCanvasValues
import OAI.Hierarchy.DescentPackedCanvasMasks

namespace OAI
/-! # Native fixed-size public estimator rectangle, including all ghost sites and port slots -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle DescentPackedRectangle.Canvas
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H HP D u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
  (hosts : H≤HP) (ports : A.degree≤D) (f K : ℕ)
local notation "m" => u+l
local notation "N" => HP*(m+1)+HP*D
local notation "ord" => rowOrd HP m D
local notation "pub" => Equiv.trans (rowOrd HP (u+l) D) (finCongr (Eq.symm (Nat.mul_add HP (u+l+1) D)))
local notation "dep" => GroupStage.MixerHeader.depth A (A.mixerHeader digits name) f
local notation "bound" => A.wire*(A.z*G.b)*A.cap
local notation "nxt" => extendedPort (D:=D) hosts (neighborSlot (degree:=A.degree) name A.mutual)
local notation "geo" => loc A name digits f hosts ports
local notation "site" => (fun (v : Fin HP) (z : Bits (u+l))=>Padded.load A name digits v (address m z))
local notation "flow" => (fun p : Port HP D=>fun z : Bits (u+l)=>Padded.flow A name digits (Prod.snd p) (Prod.fst p) (address m z))

theorem publish (L : Tape) (T : Gather) (count rd rg : Bank) (base pitch out dPage gPage : ℕ)
    (mem : Memory w) (S : Room T pitch HP u l D w out) (safe : DescentMeasuredHeader.Fits L w HP m D base)
    (flag : T.live.base=base) (reads : rd.base=base+N) (gs : rg.base=base+2*N)
    (shape : ∀B∈[T.kind,T.owner,T.pointer,T.sites,T.flows],B.base+B.size≤base)
    (space : base+3*N≤dPage) (separate : dPage+N≤gPage) (extent : gPage+N≤out)
    (fit : ∀B∈[L.owner,count,rd,rg],B.Fits w dPage) (lengths : ∀B∈[L.owner,rd,rg],N≤B.size)
    («prefix» : count.base<base) (counted : mem count.base=(H:Word w)) (wide : HP<2^w)
    (dim : 2*m+1<2^w) (one : 1<2^w) (baseDepth : Fin HP→ℕ) (live : ∀v,baseDepth v≤ m)
    (same : ∀v : Fin H,baseDepth (v.castLE hosts)=dep (name.symm v)) (bounded : ∀v : V,dep v≤ m)
    («public» : Public T pitch HP u l D mem) (hdr : contents (k:=u+l) L baseDepth nxt f bound K mem)
    (loadRow : Installed T.sites.base (fun (v : Fin HP)=>shaped (u:=u) (l:=l) (fun z=>(site v ((DescentWalshPhysical.coordinates (u+l)).symm z):Cell b))) mem)
    (flowRows : ∀j : Fin D,Installed (T.flows.base+j.val*pitch) (fun (v : Fin HP)=>shaped (u:=u) (l:=l) (fun z=>(flow (v,j) ((DescentWalshPhysical.coordinates (u+l)).symm z):Cell b))) mem) :
    ∃dst : Memory w,((DescentPackedRectangle.code L T w base out HP u l D).seq
      (masks L.owner count rd rg dPage gPage HP m D w)).Exec mem dst
      ((headerTime L HP m D+(4+100*(N*2^u)))+((4+48*N)+(4+48*N))) ∧
      Loaded (b:=b) A name digits f K geo dPage gPage out dst ∧ ∀a<base,dst a=mem a := by
  have boundOut:base+3*N≤out:=by omega
  obtain ⟨mid,pack,data_,dr,gr,keep⟩:=DescentPackedRectangle.issued L T base pitch out S safe flag boundOut shape mem
    baseDepth nxt f bound K site flow hdr wide dim one live «public» loadRow flowRows
  have ownRoom : L.owner.base+N≤base:=(Nat.add_le_add_left (safe.fixed L.owner (by simp [DescentMeasuredHeader.Tape.fixed])) _).trans
    (safe.fits L.owner (by simp [DescentMeasuredHeader.Tape.banks])).2.2
  have pin (t:Rows HP m D):mid (L.owner.base+(ord t).val)=((owner t).val:Word w):=by
    rw [keep _ ((Nat.add_lt_add_left (ord t).isLt _).trans_le ownRoom)]
    exact hdr.2.1 t
  obtain ⟨dst,ran,depth,gains,frame⟩:=native_masks L.owner count rd rg dPage gPage mid hosts wide
    (extent.trans_lt ((Nat.le_add_right ..).trans_lt S.output)) separate fit lengths pin ((keep _ «prefix»).trans counted)
  refine ⟨dst,?_,⟨?_,?_,?_⟩,?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then pack ran machine
  · intro ix p
    obtain ⟨t,rfl⟩ := (pub).surjective ix
    have sameWord : (DescentPackedWalsh.row (pub t) p).val =
        (DescentPackedWalsh.row (ord t) p).val := by
      simp only [DescentPackedWalsh.row,finProdFinEquiv_apply_val]; rfl
    refine (frame (out+(DescentPackedWalsh.row (pub t) p).val)
      (Or.inr (extent.trans (Nat.le_add_right _ _)))).trans ?_
    rw [sameWord]
    have value := true_load A name digits hosts ports f baseDepth same bounded t
    simpa only [Equiv.symm_apply_apply,value] using data_ (ord t) p
  · intro ix
    obtain ⟨t,rfl⟩ := (pub).surjective ix
    change dst (dPage+(ord t).val)=_
    refine (depth t).trans ?_
    rw [reads,dr t]
    have calibrated := congrArg (fun n : ℕ => (n : Word w))
      (true_depth A name digits hosts ports f baseDepth same bounded t)
    by_cases hit : liveHost (H:=H) t <;> simpa [hit] using calibrated
  · intro ix
    obtain ⟨t,rfl⟩ := (pub).surjective ix
    change dst (gPage+(ord t).val)=_
    refine (gains t).trans ?_
    rw [gs,gr t]
    have calibrated := congrArg (fun n : ℕ => (n : Word w))
      (true_gain A name digits hosts ports f K baseDepth same bounded t)
    by_cases hit : liveHost (H:=H) t <;> simpa [hit] using calibrated
  · intro a low
    have below : a<dPage := low.trans_le ((Nat.le_add_right base (3*N)).trans space)
    exact (frame a (.inl below)).trans (keep a low)

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
