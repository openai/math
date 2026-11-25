import OAI.Hierarchy.DescentRetainedOriginFacts
import OAI.Hierarchy.DescentDatedOriginCodes
import OAI.Hierarchy.DescentTerminalGrainPrefix
import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentPackedLocalLookup

namespace OAI
/-! # The terminal's physical signed chip and local grain number -/
namespace Hierarchy.DescentTerminalSignedGrainWord
open DescentSIMDLookup DescentSharedCableNames DescentSignedCableCodec DescentTerminalPointerDigits
open DescentSixParty DescentColonies DescentStageEdgeReceipt DescentGroupPeerOrder
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentPackedFallbackTree.Image
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D cap H G w M a : ℕ}

theorem digit_bound (a i n : ℕ) : digit a i n<2^a := by
  simp only [digit,Nat.mul_add,Nat.mul_one,pow_add,Nat.mod_mul_right_div_self]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Numeric address and lane of an authentic packed signed port. This includes the last partial word. -/
def chip (B : Bank) (mem : Memory w) (h : Fin H) (g : Fin G) (pos : 0<M) : Cell a :=
  ⟨digit a (lane g pos).val (mem (B.base+(row H G M (position h g pos)).val)).val,digit_bound _ _ _⟩

theorem chip_read (B : Bank) (mem : Memory w) (x : Fin H→Fin G→Cell a) (stored : Reads B x M mem)
    (h : Fin H) (g : Fin G) (pos : 0<M) (wide : a*M≤w) : chip B mem h g pos=x h g := by
  let p:=position h g pos
  have fit : (data x p).val<2^w := (data x p).isLt.trans_le (Nat.pow_le_pow_right (by decide) wide)
  have coord : p.2.val*M+(lane g pos).val=g.val:=Nat.div_add_mod' ..
  apply Fin.ext
  change digit a (lane g pos).val (mem (B.base+(row H G M p).val)).val=_
  rw [stored p,Fin.val_cast_of_lt fit,data,digit_encode,dite_eq_left (coord.trans_lt g.isLt)]
  have key : (⟨_,coord.trans_lt g.isLt⟩:Fin G)=g:=Fin.ext coord
  rw [key]
  rfl

def wing (D cap : ℕ) (B : Bank) (mem : Memory w) (h : Fin H) (g : Fin G) (pos : 0<M) :=
  DescentSignedCableCodec.decode D cap (chip B mem h g pos)

theorem wing_read (B : Bank) (mem : Memory w) (x : Fin H→Fin G→Option (Stage.Live D cap))
    (stored : Reads B (fun h g=>DescentSignedCableCodec.encode (x h g)) M mem) (h : Fin H) (g : Fin G)
    (pos : 0<M) (wide : DescentSignedCableCodec.width D cap*M≤w) : wing D cap B mem h g pos=x h g := by
  rw [wing,chip_read B mem _ stored h g pos wide,DescentSignedCableCodec.decode_encode]

theorem live_number (u : Stage.Live D cap) :
    (project D cap (DescentSignedCableCodec.encode (some u))).val=
      (u.neighbor.val*cap+(u.wire.val-u.within.val))*cap+u.within.val+1 := by
  simp [project,Packed.token,grainId,first,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem ghost_number : (project D cap (DescentSignedCableCodec.encode none)).val=0 := by simp [project,Packed.token]

/-- A standalone native implementation is one masked lookup on each already-issued signed word.
    A consumer can instead compose project into its own finite menu with no intermediate bank. -/
theorem issued (banks : Banks) (out : ℕ) (mem : Memory w)
    (x : Fin H→Fin G→Option (Stage.Live D cap)) (pos : 0<M)
    (safe : Fits banks (DescentSignedCableCodec.width D cap) (Packed.bits (D*cap*cap)) M H G w out)
    (res : resident (project D cap) banks H G M mem)
    (prior : Reads banks.source (fun h g=>DescentSignedCableCodec.encode (x h g)) M mem) :
    let dst:=imageBank H G M out banks mem
    (program banks out H G M w).Exec mem dst (4+44*(H*chunks G M)) ∧
    (∀h g,point D cap ⟨digit (Packed.bits (D*cap*cap)) (lane g pos).val
      (dst (out+(row H G M (position h g pos)).val)).val,digit_bound _ _ _⟩=(x h g).map grain) ∧
    ∀j,(j<out ∨ out+H*chunks G M≤j)→dst j=mem j := by
  obtain ⟨run,read,before,after⟩:=DescentPackedLocalLookup.compile banks out (project D cap)
    (fun h g=>DescentSignedCableCodec.encode (x h g)) pos safe mem res prior
  refine ⟨run,?_,fun j away=>away.elim (before j) (after j)⟩
  intro h g
  have eqn : (⟨_,digit_bound _ _ _⟩:Cell (Packed.bits (D*cap*cap)))=
      project D cap (DescentSignedCableCodec.encode (x h g)):=Fin.ext (read h g)
  rw [eqn,point_project]

section Stage
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W T q ε J V k) (native : W.graph.Edge↪ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J↪Fin G) (hosts : V↪Fin H)
local notation "names" => cableNames k (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))
local notation "board" => Prepare.signed A native S ready groups hosts
local notation "live" => Stage.signedPanel A native S ready names

theorem stored_site (x : Block k) (j : Fin (2*A.cap)) (v : J×V) :
    board x j (hosts v.2) (groups v.1)=live (v,x) j := by
  have hit : ∃z : J×V,groups z.1=groups v.1 ∧ hosts z.2=hosts v.2:=⟨v,rfl,rfl⟩
  have unique : hit.choose=v:=Prod.ext (groups.injective hit.choose_spec.1) (hosts.injective hit.choose_spec.2)
  simp only [Prepare.signed,Prepare.spreadField,dite_eq_left hit,unique]

variable (cables : Block k→Fin (2*A.cap)→Bank) (mem : Memory w)
    (prior : ∀(x : Block k) (j : Fin (2*A.cap)), Reads (cables x j)
      (fun h g => DescentSignedCableCodec.encode (D:=A.degree) (cap:=A.cap) (Prepare.signed A native S ready groups hosts x j h g)) M mem)
    (pos : 0<M) (wide : DescentSignedCableCodec.width A.degree A.cap*M≤w)

include prior wide

theorem stage_wing (x : Block k) (j : Fin (2*A.cap)) (v : J×V) :
    wing A.degree A.cap (cables x j) mem (hosts v.2) (groups v.1) pos=live (v,x) j :=
  (wing_read (cables x j) mem (board x j) (prior x j) (hosts v.2) (groups v.1) pos wide).trans
    (stored_site A native S ready groups hosts x j v)

theorem stage_grain (x : Block k) (j : Fin (2*A.cap)) (v : J×V) :
    point A.degree A.cap (project A.degree A.cap (chip (cables x j) mem (hosts v.2) (groups v.1) pos))=
      (live (v,x) j).map grain := by
  rw [chip_read (cables x j) mem (fun h g => DescentSignedCableCodec.encode (board x j h g)) (prior x j) (hosts v.2) (groups v.1) pos wide,point_project,stored_site]

theorem physical_port (v : Stage.Host J V k) (p : A.CellPorts v.1.1 v.1.2 v.2) :
    wing A.degree A.cap (cables v.2 (Stage.signed A native S ready v.1 v.2 p)) mem (hosts v.1.2) (groups v.1.1) pos=
      some (Stage.live A native S ready names v p) := by
  rw [stage_wing A native S ready groups hosts cables mem prior pos wide,Stage.signed_read]

theorem terminal_grains (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s))) :
    let h:=Stage.home A v
    present (fun j=>point A.degree A.cap (project A.degree A.cap
      (chip (cables h.2 j) mem (hosts h.1.2) (groups h.1.1) pos)))=
      Finset.univ.map (DescentTerminalPointerDigits.token A native S ready names v) := by
  let h:=Stage.home A v
  apply Eq.trans _ (DescentTerminalPointerDigits.grains_exact A native S ready names v coords)
  apply congrArg present
  funext j
  exact stage_grain A native S ready groups hosts cables mem prior pos wide h.2 j h.1

end Stage
end
end Hierarchy.DescentTerminalSignedGrainWord

end OAI
