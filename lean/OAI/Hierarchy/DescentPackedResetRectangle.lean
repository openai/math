import OAI.Hierarchy.DescentPackedFlowHeader
import OAI.Hierarchy.DescentPackedRectanglePublication
import OAI.Hierarchy.DescentIssuedCanonicalReset

namespace OAI
/-! # Packed original reset inputs on the genuine numbered sites, levels and contacts -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
local notation "m" => u+l
local notation "N" => H*(m+1)+H*A.degree
local notation "bas" => GroupStage.MixerHeader.depth A (A.mixerHeader digits name)
private theorem rectangleDegreeBound (v : V) : (A.mutual v).card ≤ A.degree :=
  (Finset.card_filter_le ..).trans (A.degreeBound v)
local notation "caps" => rectangleDegreeBound A
local notation "loc" => portRow (k:=m) name A.mutual caps
local notation "nxt" => neighborSlot (degree:=A.degree) name A.mutual
local notation "sites" => (fun v z=>A.resetLoad digits v (address m z))
local notation "contacts" => (fun c : Contacts A.mutual=>fun z=>A.resetFlow digits (Sigma.fst c) (Subtype.val (Sigma.snd c)) (address m z))

structure InstalledRectangle (f K base out : ℕ) (dst : Memory w) : Prop where
  input : Installed out (fun i=>shaped (u:=u) (l:=l) (fun z=>(padded (loc (bas f)) (load (inputLevels (k:=u+l) (bas f)) sites contacts)
    (fun _=>0) i ((DescentWalshPhysical.coordinates (u+l)).symm z):Cell b))) dst
  levels (i : Fin N) : dst (base+N+i.val)=(padded (α:=ℕ) (loc (bas f))
    (level (inputLevels (k:=u+l) (bas f)) (inputDepth (bas f)) (pairDepth A.mutual (bas f))) 0 i:Word w)
  gains (i : Fin N) : dst (base+2*N+i.val)=(padded (α:=ℕ) (loc (bas f))
    (gain (inputLevels (k:=u+l) (bas f)) f (A.wire*(A.z*G.b)*A.cap) K) 0 i:Word w)

/-- Run first on the measured depth header, then on every packed high-coordinate row in order. -/
theorem rectangle (L : Tape) (T : Gather) (f K base pitch out : ℕ) (S : Room T pitch H u l A.degree w out)
    (safe : DescentMeasuredHeader.Fits L w H m A.degree base) (flag : T.live.base=base)
    (disjoint : base+3*N≤out) (before : ∀B∈[T.kind,T.owner,T.pointer,T.sites,T.flows],B.base+B.size≤base)
    (mem : Memory w) (hw : H<2^w) (wide : 2*m+1<2^w) (one : 1<2^w)
    (bounded : ∀v,bas f v≤ m) («public» : Public T pitch H u l A.degree mem)
    (fixed : contents (k:=u+l) L (bas f ∘name.symm) nxt f (A.wire*(A.z*G.b)*A.cap) K mem)
    (site : Installed T.sites.base (fun v=>shaped (u:=u) (l:=l) (fun z=>(A.resetLoad digits (name.symm v)
      (address m ((DescentWalshPhysical.coordinates (u+l)).symm z)):Cell b))) mem)
    (traffic : ∀j : Fin A.degree,Installed (T.flows.base+j.val*pitch) (fun v=>shaped (u:=u) (l:=l) (fun z=>
      (raw A name digits j v (address m ((DescentWalshPhysical.coordinates (u+l)).symm z)):Cell b))) mem) :
    ∃dst : Memory w,(DescentPackedRectangle.code L T w base out H u l A.degree).Exec mem dst
      (headerTime L H m A.degree+(4+100*(N*2^u))) ∧ InstalledRectangle (b:=b) A name digits f K base out dst ∧
      ∀a<base,dst a=mem a := by
  let siteAt : Fin H→Bits m→ℕ:=fun v z=>A.resetLoad digits (name.symm v) (address m z)
  let flow : Port H A.degree→Bits m→ℕ:=fun p z=>raw A name digits p.2 p.1 (address m z)
  obtain ⟨dst,ran,words,depth,gain,frame⟩:=DescentPackedRectangle.issued L T base pitch out S safe flag disjoint before mem (bas f ∘name.symm)
    nxt f (A.wire*(A.z*G.b)*A.cap) K siteAt flow fixed hw wide one (fun v=>bounded _) «public» site traffic
  refine ⟨dst,ran,⟨?_,?_,?_⟩,frame⟩
  · have fn (t : Rows H m A.degree) :=load_padded (k:=u+l) name A.mutual caps (bas f) bounded siteAt flow sites contacts
      (fun v=>by simp [siteAt]) (fun c=>funext (fun z=>raw_contact A name digits caps c (address m z))) t
    simpa only [fn,Equiv.apply_symm_apply] using words
  · intro ix
    obtain ⟨t,rfl⟩:=(rowOrd H m A.degree).surjective ix
    simpa only [depth_padded name A.mutual caps (bas f) bounded] using depth t
  · intro ix
    obtain ⟨t,rfl⟩:=(rowOrd H m A.degree).surjective ix
    simpa only [gain_padded name A.mutual caps (bas f) bounded] using gain t

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
