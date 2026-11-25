import OAI.Computability.BorderVNP.PackedInheritedWorkJoint
import OAI.Computability.BorderVNP.PackedInheritedWorkPorts
import OAI.Computability.BorderVNP.PackedInheritedWorkTransport
import OAI.Computability.BorderVNP.PackedInheritedWorkReturn

/-! # Genuine lineage readback on the assembled geometry and width kernel -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.PublicParallel Shortening.PublicEndpoints
open Epoch Epoch.Round Cover PackedHistoryCircuit PackedHistoryCircuit.Normalized InheritedBank
open VPVNP.VerifierNetwork
open private shape from OAI.Computability.BorderVNP.PackedInheritedWorkJoint
open scoped Classical BorderVNP.Epoch.Cube

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {D m k V E n np w d lev : ℕ} [NeZero D] {K Bin P B Old : Type} [Field K] [Fintype Bin] [Fintype P]
variable [Fintype B] [Fintype Old] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K (Cube D) d}
variable (e : PaidIdentity K D m) (s : Stage m Bin lev child) (q : s.Index e)
variable (old : ∀ i, Site.Programs (child i).pack.layout) (names : ∀ i, (child i).pack.layout.Site ↪ Fin V)
variable (pdir : Directory (s.result e q) (siteCapacity e (k*V) n) E)
local notation3 "Seeds" => ((Cube D → Deck (lev+1)) × Bin)
variable (seed : ((Cube D → Deck (lev+1)) × Bin) ↪ Fin n) (p : Ports np) (port : P ↪ Fin np)
variable (binName : ((Cube D → Deck (lev+1)) × Bin) → ℕ) (position : e.Entry → ℕ)
local notation3 "sites" => siteCapacity e (k*V) n
local notation3 "nextPorts" => p.parallel k V
local notation3 "portRows" => Parallel.portRows k port
local notation3 "next" => s.privatePrograms e q old pdir.sites pdir.cables portRows binName position
local notation3 "saved" => ((s.result e q).dense pdir.cables).pack.layout
variable (siteFit : siteCapacity e (k*V) n ≤ 2^w)
variable (geom : Frame ((Fin k × Old) ⊕ (((Cube D → Deck (lev+1)) × Bin) × Fin e.count × Fin w)) (SavedPins B (siteCapacity e (k*V) n) E w ⊕ Unit))
variable (y : Fin k → WithWidths Old V w → Bool) (room : ∀ t, s.matched t < 2^w)
local notation3 (prettyPrint := false) "guess" => NamedReceipt.word s room q
local notation3 (prettyPrint := false) "x" => Sum.elim (fun z : Fin k × WithWidths Old V w => y z.1 z.2) guess
local notation3 (prettyPrint := false) "prior" => Sum.elim (fun z : Fin k × Old => y z.1 (.inl z.2)) guess
local notation3 (prettyPrint := false) "f" => jointNode (k := k) (V := V) (E := E) (w := w) (B := B) (Old := Old) e seed (nextPorts).host (nextPorts).width siteFit geom

include geom in
/-- Both true program fields appear at their actual saved site, and the
geometry is exactly the preceding physical pass. Static external pointer
provenance is propagated from the child rectangles. -/
theorem joint_image (site : pdir.sites = siteRows e s.input (parallelName names) seed)
    (input : ∀ i, Covers (names i) (fun v => (old i v).program.size) (assignedColumn true) (y i))
    (ready : PublicEndpoints.Represents saved pdir.dense.sites pdir.dense.cables pdir.dummy
      (fun z : Inputs B sites E w w => geom.eval prior (.inl (.inr (.inr z)))))
    (ports : ∀ i, p.Reads (child i).pack.layout (names i) port)
    (width : ∀ i, p.width i < 2^w) (holes : ∀ i ∉ Set.range port, p.width i = 0)
    (data : ∀ i, RecordData (child i).pack.layout) {C T : ℕ} (hT : 0<T) (cert : s.RecordFactor e C)
    (cap : ∀ i, RecordsWithin (child i) (data i) true T)
    (charge : ∀ i v, (old i v).program.publicNodes ≤ (data i).prior v ∧ (old i v).program.expandedLoad ≤ (data i).payload v)
    (word : 2*(loadMultiplier e*C*k*T) < 2^w) :
    ((fun z : SavedPins B sites E w => (f).eval x (.inl (.inl z))) = fun z => geom.eval prior (.inl z : SavedPins B sites E w ⊕ Unit)) ∧
      ∀ b, Covers pdir.dense.sites (fun v => if b then (next v).program.size else (next v).program.work)
        (assignedColumn b) ((f).eval x ∘ Sum.inl) := by
  let src := jointFields (k := k) (V := V) (w := w) (Old := Old) (A := Seeds) (B := B) (E := E) e (nextPorts).host (nextPorts).width siteFit
  let full : WidthInput Old Seeds k V e.count w ⊕ (SavedPins B sites E w ⊕ Unit) → Bool := Sum.elim x ((shape (k := k) (V := V) (n := n) (E := E) (w := w) (A := Seeds) (B := B) (Old := Old) e geom).eval x)
  have hg : (shape (k := k) (V := V) (n := n) (E := E) (w := w) (A := Seeds) (B := B) (Old := Old) e geom).eval x = geom.eval prior := by
    funext z
    simp only [shape,Frame.subst_eval]
    congr 1
    funext t
    rcases t with t | t <;> simp only [Frame.initial_eval,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,id_eq]
  have selected (i j) : full (src.child (i,j)) = y i (.inr (j.1,true,j.2)) := rfl
  have oldRead (i) : Covers (names i) (fun v => (old i v).program.size)
      (Frame.initial fun z => src.child (i,z)) full :=
    (input i).of_bits (fun _ _ => by simp only [Frame.initial_eval,assignedColumn,selected])
  have ep : PublicEndpoints.Represents saved pdir.dense.sites pdir.dense.cables pdir.dummy (full ∘ src.saved) := by
    have eq : full ∘ src.saved = fun z => geom.eval prior (.inl (.inr (.inr z))) := by
      funext z
      exact congrFun hg (.inl (.inr (.inr z)))
    rwa [eq]
  have hp := Ports.sewn e s q names seed pdir p port site ports holes
  have hz := node_installed e s q old names pdir seed portRows binName position src room full site oldRead rfl ep
    hp.attach hp.size (fun i => width (finProdFinEquiv.symm i).2) hp.hole data hT cert cap charge word
  constructor
  · funext z
    have h := Retained.joint_geometry (Frame.initial id) (shape (k := k) (V := V) (n := n) (E := E) (w := w) (A := Seeds) (B := B) (Old := Old) e geom) (node e seed src) x z
    have hx : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
    rw [hx,hg] at h
    exact h
  · intro b
    have he (i j) : (assignedColumn b).eval ((f).eval x ∘ Sum.inl) (i,j) =
        (column (node e seed src) b).eval full (i,j) := by
      simp only [assignedColumn,Frame.initial_eval,Function.comp_apply,column,Frame.select_eval]
      exact jointNode_words (k := k) (V := V) (E := E) (w := w) (B := B) (Old := Old) e seed (nextPorts).host (nextPorts).width siteFit geom x i b j
    cases b
    · exact hz.1.of_bits (he · ·)
    · exact hz.2.of_bits (he · ·)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
