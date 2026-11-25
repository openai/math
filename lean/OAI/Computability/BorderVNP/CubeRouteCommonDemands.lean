import OAI.Computability.BorderVNP.CubeRouteNativePlacement
import OAI.Computability.BorderVNP.PackedRoutingTeamAgreement

/-! # The native compact directory depends only on the actually placed private and live words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- The same injected private entries and live ports, with the same cell assignment
and widths, give one ordered directory on all physical processor memories. -/
theorem BankPlacement.directory_eq {d : Layout} {pp lp pp' lp' : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {C : ℕ} {cell : A → Fin C} {id : A ↪ ℕ} {width : A → ℕ}
    (left : BankPlacement d pp lp A cell id width) (right : BankPlacement d pp' lp' A cell id width)
    (keys : ∀ k, left.key k=right.key k) (bound : d.DestinationBounds) : d.directory pp lp = d.directory pp' lp' := by
  apply d.directory_congr_keys pp lp pp' lp' bound
  intro k
  rw [left.entry,right.entry,keys]

end Packing.Directory

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Transmission

/-- A physical data input may be indexed by the canonical common list of populated demands. -/
theorem DemandInput.congr_directory {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp pp' lp' : ℕ → ℕ × ℕ}
    {R w : ℕ} {owner : ℕ → Fin (R+1)} {pub : Arg → Word w} {m : Memory w}
    (h : DemandInput a D pp lp owner pub m) (eq : D.directory pp lp = D.directory pp' lp') :
    DemandInput a D pp' lp' owner pub m := by
  refine ⟨h.ready,h.records,eq ▸ h.count,?_,?_⟩
  · exact transfer eq (fun i row => DataWriter.demandAt (readings m)
      ((DataWriter.layout (readings pub) (readings m)).input+i*7)=row) h.raw
  · let emit := DataWriter.layout (readings pub) (readings m)
    exact transfer eq (fun _ row => readings m (emit.owners+row.cell*2)=(owner row.cell).val ∧
      readings m (emit.owners+row.cell*2+1)=a.cellBank+row.cell*a.cellStride) h.cells
where
  transfer {l r : List Packing.Directory.Row} (same : l = r) (P : ℕ → Packing.Directory.Row → Prop)
      (rows : ∀ i : Fin l.length, P i.val l[i.val]) : ∀ i : Fin r.length, P i.val r[i.val] := by subst r; exact rows

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
