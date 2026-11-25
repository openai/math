import OAI.Hierarchy.TaggedWidePacketWantedFields
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMRowChoiceFits

namespace OAI
/-! # Real expression work of per-atom wanted widths, including every repeated request -/
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe Probe WireTelescope ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
open private scanWants from OAI.Hierarchy.ProbeSignedWantedRelease
variable {F E A : Type} [Field F] [Fintype E] [Nonempty E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ} {N W out B : ℕ}
variable (M : FixedMenu F edge req box ε tree N) (copies : ℕ) (party : Fin k→Expr)

private theorem atRow_id (a : Expr) : a.atRow .row=a := by induction a <;> simp_all [Expr.atRow]

private theorem scan_fits (n : ℕ) (f : Fin n→Expr) (ok : ∀i,(f i).Fits W out) :
    (scanWants n f).Fits W out := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨ok 0,ih _ (fun i=>ok i.succ)⟩

private theorem scan_work (n : ℕ) (f : Fin n→Expr) (ok : ∀i,(f i).work≤B) :
    (scanWants n f).work≤1+n*(B+1) := by
  induction n with
  | zero=>simp [scanWants,Expr.work]
  | succ n ih=>
    have first:=ok 0;have tail:=ih (fun i=>f i.succ) (fun i=>ok i.succ)
    simp only [scanWants,Expr.work,Nat.succ_mul];omega

theorem wantField_fits (tag here width nbr : Expr) (small : ∀i,(party i).Fits W out)
    (t : tag.Fits W out) (s : here.Fits W out) (w : width.Fits W out) (z : nbr.Fits W out) :
    (wantField M copies party tag here width nbr).Fits W out := by
  apply BoughtSockets.choose_fits_bound _ _ _ _ _ t
  intro i
  refine ⟨w,trivial,trivial,scan_fits _ _ ?_⟩
  intro j
  simp only [compareRole,Expr.Fits,atRow_id]
  simp [small,s,z]

def wantWork (atoms requests B : ℕ) := 1+atoms*(B+(B+4+requests*(32*(B+1)+1))+2)

theorem wantField_work (tag here width nbr : Expr) (small : ∀i,(party i).work≤B)
    (t : tag.work≤B) (s : here.work≤B) (w : width.work≤B) (z : nbr.work≤B) :
    (wantField M copies party tag here width nbr).work≤wantWork (Fintype.card M.index) (Fintype.card A) B := by
  let bound:=B+4+Fintype.card A*(32*(B+1)+1)
  apply le_trans (BoughtSockets.choose_work_bound _ _ bound _ _ ?_)
  · change 1+_*(tag.work+bound+2)≤1+_*(B+bound+2)
    gcongr
  intro i
  let choice:=(Fintype.equivFin M.index).symm i
  let item:=PositiveDemand req choice.val.val
  let toChord (j : Fin (Fintype.card item)):=edge (req ((Fintype.equivFin item).symm j).val)
  let low:Expr:=.branch .lt here nbr here nbr
  let high:Expr:=.branch .lt here nbr nbr here
  let dat:Expr:=.lit (copies*(M.packet choice).width)
  let x (j : Fin (Fintype.card item)):=compareRole ((party (toChord j).1.1).atRow .row)
    ((party (toChord j).1.2).atRow .row) low high dat
  have fee (j : Fin (Fintype.card item)) : (x j).work≤32*(B+1) := by
    have a:=small (toChord j).1.1;have b:=small (toChord j).1.2
    simp only [x,atRow_id,low,high,dat,compareRole,Expr.work];omega
  have all:=scan_work _ x fee
  have leA:=Fintype.card_le_of_injective (fun a:item=>a.val) Subtype.val_injective
  have enough:=Nat.mul_le_mul_right (32*(B+1)+1) leA
  change width.work+1+1+(scanWants (Fintype.card item) x).work+1≤bound
  unfold bound
  omega

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory


namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
variable {M D base z : ℕ} (old : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (before : Fin D→Expr)
theorem packetFields_work (a : ∀i,(old i).work≤z) (b : ∀i,(gate i).work≤z) (c : ∀i,(before i).work≤z) :
    ∀i,(packetFields old gate before i).work≤z := by
  refine Fin.addCases (fun i=>?_) (Fin.addCases (fun i=>?_) (Fin.addCases (fun i=>?_) (fun i=>?_)))
  · simpa only [packetFields_pre] using a i
  · simpa only [packetFields_turn] using b (i.castAdd D)
  · simpa only [packetFields_before] using c i
  · simpa only [packetFields_after] using b (Fin.natAdd ((M*3)*5) i)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
