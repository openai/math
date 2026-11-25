import OAI.Hierarchy.DescentIssuedNodeOrder
import OAI.Hierarchy.DescentCoalescedRecords
import OAI.Hierarchy.DescentStageAtoms
import OAI.Hierarchy.DescentSelectedHubs

namespace OAI
/-! # The local record lists and hub tags issued by a native ordinary transition -/

namespace Hierarchy.DescentSixParty
open DescentKernelHistory DescentHostDirectory MarkedWorld GadgetNetwork
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε)
    (c : (T.result he).Choice)
private abbrev particleWorld :=
  let r := BitDescription.scannedRows he T
  W.selected G r.pick (fun _ => T.z) (fun _ => T.unitPos) r.fit r.pack (r.profile c)

private abbrev particleRecords :=
  let r := BitDescription.scannedRows he T
  let z := fun _ : r.pairs => T.z
  StarKeys.newRecords W.graph r.pick (bestLayout (branchWidth G z (r.profile c))) r.pack T.records z (r.profile c)

def transferRow {N M : MarkedWorld F d P bits} {Y : Type} (same : N=M) (x : M.graph.Site→Y) : N.graph.Site→Y :=
  same.symm ▸ x

inductive ParticleRows (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice) : (N : MarkedWorld F d P bits)→(norm : Normalize N)→
    (norm.result.graph.Site→ℕ)→(norm.result.graph.Site→Bool)→Prop where
  | stage {V : Type} [DecidableEq V] (key : (particleWorld he T c).graph.Site↪Key V) (flag : V→Bool)
      (pos : W.graph.Site→V) (tags : T.hub=flag∘pos)
      (k g q : ℕ) (old : ∀e∈W.core,q∣W.graph.width e) (used : ∀j,(BitDescription.scannedRows he T).pick j∈W.core)
      (chunks : ∀_i : (BitDescription.scannedRows he T).pairs,q∣T.z) (inc : HubIncidence W (flag∘pos))
      (packed : ∀x y,(BitDescription.scannedRows he T).pack x=(BitDescription.scannedRows he T).pack y→(flag∘pos) x=(flag∘pos) y)
      (same : ∀v,flag (key v).1=W.selectedHub G (BitDescription.scannedRows he T).pick (fun _ => T.z) (fun _ => T.unitPos) (BitDescription.scannedRows he T).fit (BitDescription.scannedRows he T).pack ((BitDescription.scannedRows he T).profile c) (flag∘pos) inc used packed v) :
      ParticleRows he T c _
        (subroundNormalize W G (BitDescription.scannedRows he T).pick (fun _ => T.z) (fun _ => T.unitPos) (BitDescription.scannedRows he T).fit (BitDescription.scannedRows he T).pack ((BitDescription.scannedRows he T).profile c) key flag k g q old used chunks)
        (fun v=>((particleWorld he T c).coalescedRecords key flag k g (particleRecords he T c) v).length)
        (coalescedHub (particleWorld he T c) key flag k g)
  | named {N : MarkedWorld F d P bits} (norm : Normalize N) {count : norm.result.graph.Site→ℕ}
      {flag : norm.result.graph.Site→Bool} (prior : ParticleRows he T c N norm count flag)
      (s : Equiv.Perm norm.result.graph.Site) (e : Equiv.Perm norm.result.graph.Edge) :
      ParticleRows he T c N (norm.appendNames s e)
        (transferRow (norm.appendNames_result s e) (count∘s.symm))
        (transferRow (norm.appendNames_result s e) (flag∘s.symm))

end
end Hierarchy.DescentSixParty

end OAI
