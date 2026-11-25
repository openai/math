import OAI.Hierarchy.DescentTerminalMaskedReached
import OAI.Hierarchy.DescentTerminalRolePrefix

namespace OAI
/-! # The actual reached occupation page supplies both directions of the terminal live-site chart -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentTerminalGraphPositions DescentTerminalVertexFields DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
    {G:PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist p:ℕ}
    (live:Reached W G price ε S k age z degree wire hist) (L:Order W.graph (S.hostSize age) p)
    (same:L.home=live.home)
local notation "groups" => S.groupCount age
local notation "blocks" => 2^k
local notation "shops" => S.hostSize age
local notation "grp" => fun v=>(live.placement.pos v).1
local notation "blk" => live.placement.block

theorem site_venue (i:Fin shops) (v:Fin (L.site i).nodes) :
    live.rawResident L same i v=finProdFinEquiv (grp (L.node i v),blk (L.node i v)) := rfl

omit [Fintype P] in
theorem chart_image (i:Fin shops) (g:Fin groups) (b:Fin blocks) :
    (∃v,live.home v=i ∧ grp v=g ∧ blk v=b) ↔ ∃u,live.chart L same i u=finProdFinEquiv (g,b) := by
  constructor
  · rintro ⟨v,hv,hg,hb⟩
    refine ⟨⟨v,by simpa only [same] using hv⟩,?_⟩
    change finProdFinEquiv (grp v,blk v)=finProdFinEquiv (g,b)
    rw [hg,hb]
  · rintro ⟨u,hu⟩
    change finProdFinEquiv (grp u.val,blk u.val)=finProdFinEquiv (g,b) at hu
    have pair:=finProdFinEquiv.injective hu
    exact ⟨u.val,same ▸ u.property,congrArg Prod.fst pair,congrArg Prod.snd pair⟩

variable {q t hid N A wb : ℕ} (channels:MaskAllocation.Channels (2^k)) (base:ℕ) (before after:Memory wb)
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) («groups»:=groups) channels base
local notation "dataAt" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) («groups»:=groups) machine
variable (hostFit:(S.hostSize age)≤2^wb) (wide:(S.groupCount age)≤wb) (keep:∀b,(S.hostSize age)≤(channels.occupied b).size)
    (words:∀b (i:Fin (S.hostSize age)),before ((channels.occupied b).base+i.val)=
      ((encode 1 (S.groupCount age) (fun j=>(if ∃v,live.home v=i ∧ (live.placement.pos v).1=j ∧ live.placement.block v=b then 1 else 0):Fin (S.groupCount age)→Cell 1)).val:Word wb))
    (stop:ℕ) (early:∀b,(channels.occupied b).base+(channels.occupied b).size ≤ stop)
    (frame:∀j<stop,after j=before j)

include hostFit wide keep words early frame in
omit [Fintype P] in
theorem measured_chart (i:Fin shops) (c:Fin (groups*blocks)) :
    blankAt (dataAt after i) c≠0 ↔ ∃u,live.chart L same i u=c := by
  obtain ⟨⟨g,b⟩,rfl⟩:=finProdFinEquiv.surjective c
  have hold:=DescentTerminalPrimitiveFrames.occupation_below (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) machine before after b i g stop
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.occupied_at] using early b) frame
  have old:=DescentTerminalRolePrefix.presence (q:=q) (t:=t) (hid:=hid) (N:=N) (slots:=A) (p:=p)
    channels base before live.home grp blk b i g hostFit (keep b) (words b i) wide
  have read:=hold.trans old
  rw [←chart_image live L same]
  by_cases h:∃v,live.home v=i ∧ grp v=g ∧ blk v=b
  · have yes:=read.trans (ite_eq_left h)
    refine ⟨fun _=>h,fun _ eqn=>?_⟩
    rw [eqn] at yes
    norm_num at yes
  · have no:=read.trans (ite_eq_right h)
    have blank:blankAt (dataAt after i) (finProdFinEquiv (g,b))=0:=Fin.ext no
    simp [h,blank]

end
end Hierarchy.DescentSixParty.Reached

end OAI
