import OAI.Hierarchy.TaggedWideHistoryUnit
import OAI.Hierarchy.TaggedWireRoleIndices
import OAI.Hierarchy.TaggedWireCalendarPorts
import OAI.Hierarchy.ProbeArchiveRowBound
import OAI.Hierarchy.ProtocolRAMCalendarCatalystArchive

namespace OAI
/-! # Fixed local storage for all native live and archived wires -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe ReportSockets WireTelescope CalendarTape
open ProtocolRAM Calendar Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
  (marked : Marks h W k attempts) (unique : Exclusive marked)

def paidGraph : PortGraph (Fin (siteLast h (2^W) k+1)) (Catalogue S π depth marked) :=
  ⟨fun i=>name (actualEnds S π depth marked i).1,fun i=>name (actualEnds S π depth marked i).2⟩


def amount (permanent : Catalogue S π depth marked→ℕ) (flow : Goods h W k→ℕ) (left : Catalysts h W k→ℕ) :
    Source S π depth marked→ℕ := Sum.elim permanent (Sum.elim flow left)

theorem shape {n : ℕ} (rows : Fin n≃Source S π depth marked) (paid : Catalogue S π depth marked→ℕ)
    (stock : Goods h W k→ℕ) (left : Catalysts h W k→ℕ) :
    installedWidths (sorted S π depth marked ∘ rows) (amount S π depth marked paid stock left ∘ rows) =
      (paidGraph S π depth marked).chordWidths paid+(commodityGraph π name).chordWidths stock+
        (catalystGraph name).chordWidths left := by
  unfold installedWidths
  change (∑j,amount S π depth marked paid stock left (rows j) • unitChord (sorted S π depth marked (rows j)))=_
  rw [rows.sum_comp (fun e=>amount S π depth marked paid stock left e • unitChord (sorted S π depth marked e))]
  simp only [Source,Fintype.sum_sum_type,amount,Sum.elim_inl,Sum.elim_inr]
  let D := paidGraph S π depth marked
  let G := commodityGraph π (name (h:=h) (W:=W) (k:=k))
  let A := catalystGraph (name (h:=h) (W:=W) (k:=k))
  have p (i) : paid i • unitChord (sorted S π depth marked (.inl i))=D.chordWidth i (paid i) :=
    (oriented_width D i (name.injective.ne (actual_distinct S π depth marked i)) _).symm
  have g (i) : stock i • unitChord (sorted S π depth marked (.inr (.inl i)))=G.chordWidth i (stock i) :=
    (oriented_width G i (name.injective.ne (goods_different π i)) _).symm
  have a (i) : left i • unitChord (sorted S π depth marked (.inr (.inr i)))=A.chordWidth i (left i) :=
    (oriented_width A i (name.injective.ne (physical_distinct S π depth marked (.inr (.inr i)))) _).symm
  simp only [p,g,a,PortGraph.chordWidths,Fintype.sum_sum_type,add_assoc,D,G,A]

variable {edges machine : ℕ} (mesh : Mesh) (slices : Event→List PaidWidths.Slice) (m : Memory machine)
    (edge : Catalogue S π depth marked ↪ Fin edges) (unitCost costCap reserveFuel payload : ℕ)

/-- Physical per-half-edge size is independent of the matching and any branch. -/
def ceiling (p : Public S h W k attempts) : ℕ :=
  Sum.elim (fun _=>clock mesh*unitCost*payload)
    (Sum.elim (fun _=>(2*costCap+1)*payload) (fun _=>reserveFuel*payload)) p

def archive (stop : ℕ) (i : Catalogue S π depth marked) :=
  PaidWidths.total (((events mesh).take stop).flatMap slices) m (edge i)

def live (p j : ℕ) (active saved : Goods h W k→ℕ) (bought : Bool) (i : Goods h W k) :=
  active i+held mesh.inject payload p*payloadUnit i+(if bought then held mesh.reserveSteps (saved i) j else 0)

def remaining (used : Catalysts h W k→ℕ) (i : Catalysts h W k) := reserveFuel*payload-used i

theorem fits {n : ℕ} (rows : Fin n≃Source S π depth marked) (stop p j : ℕ) (bought : Bool)
    (active saved : Goods h W k→ℕ) (used : Catalysts h W k→ℕ)
    (priced : ∀t∈events mesh,∀e : Catalogue S π depth marked,PaidWidths.total (slices t) m (edge e)≤unitCost*payload)
    (cap : ∀i,active i≤costCap*payload) (rcap : ∀i,saved i≤costCap*payload) :
    let bits := amount S π depth marked (archive S π depth marked mesh slices m edge stop)
      (live mesh payload p j active saved bought) (remaining reserveFuel payload used)
    ∀i b,bits (rows i)≤ceiling S mesh unitCost costCap reserveFuel payload (named S π depth marked unique rows (i,b)) := by
  intro bits i b
  let e := rows i
  change amount S π depth marked _ _ _ e≤ceiling S mesh unitCost costCap reserveFuel payload
    (physical S π depth marked unique (e,swap S π depth marked e b))
  rcases e with e|g|a
  · exact paid_history_prefix mesh slices m (edge e) unitCost payload stop (fun t ht=>priced t ht e)
  · exact commodity_held_cap mesh payload costCap p j (active g) (saved g) g bought (cap g) (rcap g)
  · exact Nat.sub_le ..

def fixedBound := (clock mesh*unitCost+(2*costCap+1)+reserveFuel)*payload

theorem ceiling_le (p : Public S h W k attempts) :
    ceiling S mesh unitCost costCap reserveFuel payload p ≤ fixedBound mesh unitCost costCap reserveFuel payload := by
  rcases p with p|g|a <;> simp only [ceiling,fixedBound,Sum.elim_inl,Sum.elim_inr,Nat.add_mul] <;> omega

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
