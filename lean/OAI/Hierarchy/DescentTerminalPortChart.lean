import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentQuotientHistory

namespace OAI
/-! # A terminal operand chart read from the physical signed-grain panel -/

namespace Hierarchy.DescentTerminalPortChart
open DescentSixParty DescentSharedCableNames DescentKernelHistory DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (names : Stage.Host J V k ↪ ℕ) (v : W.graph.Site)

local notation "h" => Stage.home A v
local notation "B" => Stage.source A native
local notation "roster" => Stage.neighbors A native names
abbrev Edge := Incident W.graph v

/-- Take the source position for a loop, so both uses of a loop in a local
tensor get the same public argument. -/
def first (e : Edge v) (pos : 0<A.grainCount e.val) : A.CellPorts h.1.1 h.1.2 h.2 :=
  if atSrc : W.graph.src e.val=v then
    .inl ⟨⟨e.val,congrArg A.pos atSrc,congrArg A.block atSrc⟩,⟨0,pos⟩⟩
  else
    let atDst := e.property.resolve_left atSrc
    .inr ⟨⟨e.val,congrArg A.pos atDst,congrArg A.block atDst⟩,⟨0,pos⟩⟩

theorem first_number (e : Edge v) (pos : 0<A.grainCount e.val) :
    (Stage.ofPort A native h (first A v e pos)).val=Stage.stream A native ⟨e.val,⟨0,pos⟩⟩ := by
  unfold first
  split <;> rfl

def label (e : Edge v) (pos : 0<A.grainCount e.val) : Fin (A.degree*A.cap) :=
  let r := Stage.live A native S ready names h (first A v e pos)
  finProdFinEquiv (r.neighbor,r.wire)

theorem label_injective (e f : Edge v) (ep : 0<A.grainCount e.val) (fp : 0<A.grainCount f.val)
    (eqn : label A native S ready names v e ep=label A native S ready names v f fp) : e=f := by
  let x := Stage.ofPort A native h (first A v e ep)
  let y := Stage.ofPort A native h (first A v f fp)
  have fields:=finProdFinEquiv.injective eqn
  have neigh : (roster).slot h x=(roster).slot h y:=congrArg Prod.fst fields
  have serial : (B).serial h ((B).peer h x.val) x.val=(B).serial h ((B).peer h y.val) y.val:=
    congrArg Fin.val (congrArg Prod.snd fields)
  have peer:= ((roster).same h x y).mp neigh
  rw [←peer] at serial
  have same:=(B).distinguish (((B).mem_parallel h _ _).mpr ⟨x.property,rfl⟩)
    (((B).mem_parallel h _ _).mpr ⟨y.property,peer.symm⟩) serial
  change (Stage.ofPort A native h (first A v e ep)).val=(Stage.ofPort A native h (first A v f fp)).val at same
  rw [first_number,first_number] at same
  exact Subtype.ext (congrArg Sigma.fst ((Stage.stream A native).injective same))

theorem label_read (e : Edge v) (pos : 0<A.grainCount e.val) :
    (Stage.signedPanel A native S ready names h
        (Stage.signed A native S ready h.1 h.2 (first A v e pos))).map
      (fun r=>finProdFinEquiv (r.neighbor,r.wire))=some (label A native S ready names v e pos) := by
  rw [Stage.signed_read]
  rfl

/-- Zero-width edges have no p-word. Giving them separate identifiers
allows the same chart to label the entire boundary, including empty ports. -/
def rank (pin : Attached W.graph v ↪ ℕ) : Boundary W.graph v ↪ ℕ where
  toFun
    | .inl e=>if pos : 0<A.grainCount e.val then (label A native S ready names v e pos).val
      else A.degree*A.cap+2*native e.val
    | .inr z=>A.degree*A.cap+2*pin z+1
  inj' := by
    rintro (e|z) (f|y) eqn
    · dsimp only at eqn
      split at eqn <;> rename_i ep <;> split at eqn <;> rename_i fp
      · exact congrArg Sum.inl (label_injective A native S ready names v e f ep fp (Fin.ext eqn))
      · have := (label A native S ready names v e ep).isLt; omega
      · have := (label A native S ready names v f fp).isLt; omega
      · exact congrArg Sum.inl (Subtype.ext (native.injective (by omega)))
    · dsimp only at eqn
      split at eqn <;> rename_i ep
      · have := (label A native S ready names v e ep).isLt; omega
      · omega
    · dsimp only at eqn
      split at eqn <;> rename_i fp
      · have := (label A native S ready names v f fp).isLt; omega
      · omega
    · exact congrArg Sum.inr (pin.injective (by dsimp only at eqn; omega))

theorem positive_rank (pin : Attached W.graph v ↪ ℕ) (e : Edge v) (pos : 0<A.grainCount e.val) :
    rank A native S ready names v pin (.inl e)=(label A native S ready names v e pos).val := dite_eq_left pos

theorem pin_rank (pin : Attached W.graph v ↪ ℕ) (z : Attached W.graph v) :
    rank A native S ready names v pin (.inr z)=A.degree*A.cap+2*pin z+1 := rfl

include ready in
theorem positive_of_bit (e : Edge v) (j : Fin (W.graph.width e.val)) : 0<A.grainCount e.val := by
  have hh:=A.grainCount_fit S ready e.val
  by_contra! zero
  rw [Nat.eq_zero_of_le_zero zero,Nat.zero_mul] at hh
  exact (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)) hh

end
end Hierarchy.DescentTerminalPortChart

end OAI
