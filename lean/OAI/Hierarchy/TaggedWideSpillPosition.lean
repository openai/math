import OAI.Hierarchy.TaggedWireCoreSpillLayout
import OAI.Hierarchy.TaggedWireTurnPaidCoordinates

namespace OAI
/-! # The authenticated ordinary boundaries in the original chronological turn ROM -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMDateSpillPosition
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage CoreBoard WireTelescope SettledMatrix
open scoped Classical

variable {edges : ℕ} {I C : Type}

def source : Source edges I Empty ↪ Source edges I C where
  toFun := Sum.elim Sum.inl (Sum.elim (fun i=>Sum.inr (Sum.inl i)) Empty.elim)
  inj' := by
    intro a b h
    rcases a with a|a|dead
    · rcases b with b|b|dead
      · exact congrArg Sum.inl (Sum.inl.inj h)
      · cases h
      · exact dead.elim
    · rcases b with b|b|dead
      · cases h
      · exact congrArg (fun z : I=>Sum.inr (Sum.inl z)) (Sum.inl.inj (Sum.inr.inj h))
      · exact dead.elim
    · exact dead.elim

variable {h W k n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
    (pad : Chord (siteLast h (2^W) k+1))
local notation "Good" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Full" => Source edges Good (Columns h (2^W)×Fin k)
local notation "Sub" => Source edges Good Empty
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "L" => B.matrixLayout inj pad
local notation "A" => B.spillLayout inj pad
local notation "sourceOrder" => SettledMatrix.Layout.numbered (r:=edges) (I:=Good) («A»:=Empty)

theorem steps (x : Sub) : (L).steps (source x)=(A).steps x := by
  rcases x with e|i|dead
  · rfl
  · rfl
  · exact dead.elim

def boundary : (Σ x : Sub,Fin (((A).steps x).length+1)) ↪ ProtocolRAMLiveTurnOrder.Boundaries S π B pad where
  toFun x := ⟨source x.1, x.2.cast (congrArg (fun a=>a.length+1) (steps S π B pad x.1)).symm⟩
  inj' := by
    rintro ⟨x,i⟩ ⟨y,j⟩ same
    obtain rfl := source.injective (congrArg Sigma.fst same)
    have eq := congrArg (fun s : ProtocolRAMLiveTurnOrder.Boundaries S π B pad=>s.2.val) same
    exact congrArg (Sigma.mk x) (Fin.ext eq)

/-- Deleting the always-zero catalyst rows leaves precisely the chronological
positions of the dated routed matrix, with the same possible reversed spines. -/
def embed (order : Fin n≃Full) : TurnShelf.Positions (A).routes ↪
    Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order)) :=
  (Equiv.sigmaCongrLeft (β:=fun s : Sub=>Fin (((A).steps s).length+1)) sourceOrder).toEmbedding.trans
    ((boundary S π B pad).trans (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).symm.toEmbedding)

theorem covered (order : Fin n≃Full)
    (col : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order))→Fin 7→ℕ)
    (zero : ∀i c,(ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1=.inr (.inr c)→col i 4=0)
    (i : Fin _) (live : col i 4≠0) : i∈Set.range (embed S π B pad order) := by
  let bound:=ProtocolRAMLiveTurnOrder.boundaries S π B pad order
  have retained : ∃x : Sub,source x=(bound i).1 := by
    rcases h : (bound i).1 with e|g|c
    · exact ⟨.inl e,rfl⟩
    · exact ⟨.inr (.inl g),rfl⟩
    · exact (live (zero i c h)).elim
  obtain ⟨x,hx⟩:=retained
  let u : Fin (((A).steps x).length+1) := (bound i).2.cast
    (by rw [←hx,steps S π B pad x])
  let addr := Equiv.sigmaCongrLeft (β:=fun s : Sub=>Fin (((A).steps s).length+1)) sourceOrder
  refine ⟨addr.symm ⟨x,u⟩,bound.injective ?_⟩
  change bound (bound.symm (boundary S π B pad (addr (addr.symm ⟨x,u⟩))))=bound i
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact Sigma.ext hx ((Fin.heq_ext_iff (congrArg (fun x=>((L).steps x).length+1) hx)).mpr rfl)


end Hierarchy.ProtocolRAMDateSpillPosition

end
end OAI
