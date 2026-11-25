import OAI.Computability.BorderVNP.CubeLabelTrialTables
import OAI.Computability.BorderVNP.CubeLabelStages
import OAI.Computability.BorderVNP.CubeLabelPassFit
import OAI.Computability.BorderVNP.LabelIndexTrialRoom

/-! # Cache and chosen labels after each physical stage

Initialization establishes the empty conditioned means. At a fresh cell the read-only trial
computes its semantic score, and committing its least minimizer replaces every affected mean.
The label word is written after this commit, leaving the linked rows and all preceding labels
intact.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube Cube.MeanChoice Cube.LabelIndex Finset

/-- Memory readback for the assigned prefix and the current conditional means. -/
structure StageView (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before) (labelBase z k : ℕ)
    (initial current : ℕ → ℕ) : Prop where
  /-- Every label word below the native cursor is the corresponding selected label. -/
  labels : ∀ c : Fin l.cells, c.val < k → current (labelBase+c.val) = (stage (fromTables l before ep) z k c).val
  /-- Every cache word is the scaled conditional mean on exactly that prefix of cells. -/
  means : ∀ j, current ((l.trialFrame labelBase).cacheAddr (binOrdinal z j).val) =
    cache (fromTables l before ep) (cellsBefore l.cells k) (stage (fromTables l before ep) z k) j
  /-- Heads, linked rows, and per-cell demands retain their initialized values. -/
  inputs : ∀ a, l.heads ≤ a → a < l.cableMean → current a = initial a

private theorem first_stage {l : Layout} {before : ℕ → ℕ} (ep : Endpoints l before)
    (a : Acc) (view : View l before a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels)
    (labelBase z : ℕ) (hz : l.labels = z+1) : StageView l before ep labelBase z 0 a.mem a.mem := by
  constructor
  · intro c hc; omega
  · have empty : cellsBefore l.cells 0 = ∅ := by simp [cellsBefore]
    intro j
    rw [empty]
    rcases j with ⟨u,t⟩|u
    · obtain ⟨hi,_,_⟩ := binOrdinal_cable_decode u t
      rw [empty_cable_cache]
      change a.mem (if _ < l.labels^2 then l.cableMean+_ else l.dataMean+_) = _
      rw [hz,ite_eq_left hi]
      exact (view.pairs _ (by simpa [hz,pow_two] using hi)).trans view.cableTotal
    · obtain ⟨hi,hu⟩ := binOrdinal_data_decode u
      rw [empty_data_cache]
      change a.mem (if _ < l.labels^2 then l.cableMean+_ else l.dataMean+_) = _
      simp only [Layout.trialFrame,hz,not_lt.mpr hi,ite_false,hu]
      rw [view.bins u.val (by rw [hz]; exact u.isLt),view.dataTotal,hz]
  · exact fun _ _ _ => rfl

/-- The full prefix of the physical scoring and commit table agrees with the ascending
semantic minimizer after every stage, on both the chosen labels and the scaled mean cache. -/
theorem stage_cache (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before) (al : Allocated l)
    (a : Acc) (view : View l before a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels)
    (labelBase z : ℕ) (hz : l.labels = z+1) (separate : labelBase+l.cells ≤ l.heads)
    (k : ℕ) (hk : k ≤ l.cells) :
    StageView l before ep labelBase z k a.mem ((l.trialFrame labelBase).prefix z
      (fun c => incidents (cableAt l before) c l.cableCount) a.mem k) := by
  let p := l.trialFrame labelBase
  let es := fun c => incidents (cableAt l before) c l.cableCount
  let rows := fromTables l before ep
  have seg : p.cables+p.Z^2 ≤ p.data := by simpa only [p,Layout.trialFrame,pow_two] using al.cableMean
  induction k with
  | zero => exact first_stage ep a view labelBase z hz
  | succ k ih =>
    have ok : k < l.cells := hk
    let c : Fin l.cells := ⟨k,ok⟩
    let old := p.prefix z es a.mem k
    let s := cellsBefore l.cells k
    let x := stage rows z k
    let v := firstMinimum (scoreNat rows s x c)
    let pass := p.bins c.val v.val old (es k)
    let mid := pass.image old (p.Z^2+p.Z)
    have oldView : StageView l before ep labelBase z k a.mem old := ih ok.le
    have prior (o : Fin l.cells) : o ∈ s ↔ o < c := by simp [s,cellsBefore,Fin.lt_def,c]
    have read (o : Fin l.cells) (h : o < c) : old (p.labels+o.val) = (x o).val := oldView.labels o h
    have he := al.heads
    have hn := al.nodes
    have hd := al.data
    have demand : old (p.demands+c.val) = sumWidth
        (fun i => if (deliveryAt l before i).1 = c.val then (deliveryAt l before i).2 else 0) l.deliveryCount :=
      (oldView.inputs _ (by change l.heads ≤ l.data+k; omega) (by change l.data+k < l.cableMean; omega)).trans
        (view.data k ok)
    have chosen : p.winner z k old (es k) = v := congrArg firstMinimum (funext fun u =>
      p.score_tables l before ep old c s x u hz prior read demand oldView.means)
    have incident (j) := p.incident_tables l before ep old c s x v hz prior read demand j
    have off (addr : ℕ) (h : addr < l.cableMean) : mid addr = old addr := by
      apply pass.image_off
      intro j _ eq
      have low := p.cacheAddr_lower seg j
      change p.cables ≤ p.cacheAddr j at low
      change addr = p.cacheAddr j at eq
      change addr < p.cables at h; omega
    have writes : p.prefix z es a.mem (k+1) = Function.update mid (labelBase+k) v.val := by
      change Function.update (p.updated z k old (es k)) (labelBase+k) (p.winner z k old (es k)).val = _
      rw [Frame.updated,chosen]
    have semantic : stage rows z (k+1) = Function.update x c v := by rw [stage,dite_eq_left ok]
    have fixed : cellsBefore l.cells (k+1) = insert c s := cellsBefore_succ ok
    change StageView l before ep labelBase z (k+1) a.mem (p.prefix z es a.mem (k+1))
    rw [writes]
    constructor
    · intro o h
      change Function.update mid (labelBase+k) v.val (labelBase+o.val) = (stage rows z (k+1) o).val
      rw [semantic]
      by_cases same : o = c
      · subst o; simp [c]
      · have hn : o.val ≠ k := fun hv => same (Fin.ext hv)
        rw [Function.update_of_ne (show labelBase+o.val ≠ labelBase+k by omega),Function.update_of_ne same,
          off _ (by omega)]
        exact oldView.labels o (by omega)
    · intro j
      change Function.update mid (labelBase+k) v.val (p.cacheAddr (binOrdinal z j).val) =
        cache rows (cellsBefore l.cells (k+1)) (stage rows z (k+1)) j
      have low := p.cacheAddr_lower seg (binOrdinal z j).val
      change l.cableMean ≤ _ at low
      rw [Function.update_of_ne (show p.cacheAddr (binOrdinal z j).val ≠ labelBase+k by omega),semantic,fixed]
      change pass.image old (p.Z^2+p.Z) (pass.addr (binOrdinal z j).val) = _
      rw [show p.Z = z+1 from hz]
      exact commit_image_cache rows s x c v pass old oldView.means
        (fun b => congrArg Prod.fst (incident b)) (fun b => congrArg Prod.snd (incident b))
        (fun _ _ eq => p.cacheAddr_injective seg eq) j
    · intro addr h₁ h₂
      rw [Function.update_of_ne (show addr ≠ labelBase+k by omega),off addr h₂]
      exact oldView.inputs addr h₁ h₂

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
