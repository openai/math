import OAI.Hierarchy.TaggedWideCalendarSpill
import OAI.Hierarchy.TaggedWideSpillPosition

namespace OAI
/-! # The original paid scatter seats and the positions of a dated commodity comparison -/

noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillPosition
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.WordSeats ReportSockets
open WireTelescope SettledMatrix ProtocolRAMTurnShelf Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
set_option quotPrecheck false

variable {h W k edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
    (pad : Chord (siteLast h (2^W) k+1))
local notation "Good" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Center" => Columns h (2^W)×Fin k
local notation "Full" => Source edges Good Center
local notation "Sub" => Source edges Good Empty
local notation "A" => B.spillLayout (siteNumber h (2^W) k).injective pad
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "D" => B.datedLayout (siteNumber h (2^W) k).injective pad
local notation "pnum" => Fintype.card (TurnShelf.Positions (D).routes)
local notation "raw" => Σx:Sub,Fin (((A).steps x).length+1)
local notation "small" => (D).num
local notation "big" => (SettledMatrix.Layout.ordinal (r:=edges) (I:=Good) («A»:=Center)).symm

def positionOrder : Fin pnum≃TurnShelf.Positions (D).routes:= (Fintype.equivFin _).symm

def boundaryOrder : TurnShelf.Positions (D).routes ≃ raw :=
  Equiv.sigmaCongrLeft (β:=fun x : Sub=>Fin (((A).steps x).length+1)) small

def real (order : Fin n≃Full) :=
  (positionOrder S π B pad).toEmbedding.trans ((boundaryOrder S π B pad).toEmbedding.trans
    ((boundary S π B pad).trans (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).symm.toEmbedding))

abbrev trueBoundary := boundaryOrder S π B pad

theorem registered (order : Fin n≃Full) (i : Fin pnum) :
    ProtocolRAMLiveTurnOrder.boundaries S π B pad order (real S π B pad order i)=
      boundary S π B pad (trueBoundary S π B pad (positionOrder S π B pad i)) :=
  (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).apply_symm_apply _

def sparseSpine : ∀x:Sub,Spine (rowGraph (A).edge) ((A).original x).val.1 ((A).steps x) ((A).original x).val.2
  | .inl e=>ProtocolRAMPaidTurnPlacement.honestSpine S π B pad (.inl e)
  | .inr (.inl g)=>ProtocolRAMPaidTurnPlacement.honestSpine S π B pad (.inr (.inl g))
  | .inr (.inr dead)=>dead.elim

theorem registered_visit (x : raw) :
    ProtocolRAMPaidTurnPlacement.atBoundary S π B pad (boundary S π B pad x)=(sparseSpine S π B pad x.1).visit x.2 := by
  rcases x with ⟨(e|g|dead),u⟩
  · rfl
  · rfl
  · exact dead.elim

variable (order : Fin n ≃ Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
    (Columns h (2^W) × Fin k))
local notation "rows" => ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order)
local notation "strip" => real S π B pad order
local notation "pos" => positionOrder S π B pad
variable (spill : Commodity (Fin (2^h)) (Stages h (2^W)) k → ℕ)
    (col : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order)) → Fin 7 → ℕ)
local notation "w" => Layout.available (fun _:Fin edges=>0) spill (fun _:Center=>0) (fun _:Center=>0)
local notation "cnt" => (D).bits spill
variable (width : ∀ i, col i 4 =
    Layout.available (fun _ : Fin edges => 0) spill (fun _ : Columns h (2^W) × Fin k => 0)
      (fun _ : Columns h (2^W) × Fin k => 0) (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1)
include width

theorem covers_real (i : Fin rows) (positive : col i 4≠0) : i∈Set.range strip := by
  obtain ⟨z,hz⟩:=covered S π B pad order col (fun i _ ha => (width i).trans (congrArg w ha)) i positive
  let orig:=Equiv.sigmaCongrLeft (β:=fun x : Sub=>Fin (((A).steps x).length+1)) (SettledMatrix.Layout.numbered (r:=edges) (I:=Good) («A»:=Empty))
  change (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).symm (boundary S π B pad (orig z)) = i at hz
  refine ⟨(pos).symm ((boundaryOrder S π B pad).symm (orig z)),?_⟩
  change (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).symm
    (boundary S π B pad (boundaryOrder S π B pad (pos ((pos).symm ((boundaryOrder S π B pad).symm (orig z))))))=i
  simpa only [Equiv.apply_symm_apply] using hz

theorem width_restrict (i : Fin pnum) : (col ∘ strip) i 4=cnt (pos i).1 := by
  rw [Function.comp_apply,width,registered]
  change w (source (small (pos i).1))=Layout.available (fun _ : Fin edges => 0) spill (fun _ : Empty => 0) (fun _ : Empty => 0) (small (pos i).1)
  rcases small (pos i).1 with e|g|dead
  · rfl
  · rfl
  · exact dead.elim

theorem written_restrict {M sites slots : ℕ} (mem : Memory M) (base : ℕ)
    (put : Live col ↪ Seats sites slots)
    (written : ∀f : Fin 5,∀a : Fin sites×Fin slots,mem (TurnShelf.addr base a.1 a.2 f)=entry col put f a) :
    ∀f : Fin 5,∀a : Fin sites×Fin slots,mem (TurnShelf.addr base a.1 a.2 f)=
      entry (col ∘ strip) ((restrictedLive col strip).trans put) f a :=
  fun f a=>(written f a).trans (entry_restrict col strip (covers_real S π B pad order spill col width) put f a)

variable {attempts : ℕ} (depth : ℕ) (marked : Marks h W k attempts) (uni : Exclusive marked)
    (ident : {e : Fin edges // 0<(fun _ : Fin edges=>0) e} ↪ Catalogue S π depth marked)
local notation "put" => ProtocolRAMPaidTurnPlacement.put S π depth marked uni B pad (fun _:Fin edges=>0)
    ident order w (fun _=>rfl) col width

theorem paid_site (u : Live (col ∘ strip)) :
    (((restrictedLive col strip).trans put) u).1=
      (sparseSpine S π B pad (small (pos u.val).1)).visit (pos u.val).2 := by
  let a:=restrictedLive col strip u
  have native := ProtocolRAMPaidTurnPlacement.position_site S π depth marked uni B pad (fun _:Fin edges=>0)
    ident order w (fun _=>rfl) col width (fun e=>False.elim (Nat.not_lt_zero _ e.property)) a
  let e:=Equiv.sigmaCongrLeft (β:=fun x : Full=>Fin (((L).steps x).length+1)) big
  have chart:=congrArg (ProtocolRAMPaidTurnPlacement.atBoundary S π B pad)
    (e.apply_symm_apply (ProtocolRAMLiveTurnOrder.boundaries S π B pad order a.val))
  have endp : (put a).1=ProtocolRAMPaidTurnPlacement.atBoundary S π B pad
      (ProtocolRAMLiveTurnOrder.boundaries S π B pad order a.val):=native.trans chart
  exact endp.trans ((congrArg (ProtocolRAMPaidTurnPlacement.atBoundary S π B pad)
    (registered S π B pad order u.val)).trans (registered_visit S π B pad _))

end Hierarchy.ProtocolRAMDateSpillPosition
end

end OAI
