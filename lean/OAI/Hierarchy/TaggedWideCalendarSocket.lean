import OAI.Hierarchy.TaggedWideCalendarSigned
import OAI.Hierarchy.TaggedWideChordAperture
import OAI.Hierarchy.TaggedWirePacketGatheredBit
import OAI.Hierarchy.TaggedWideActiveBits
import OAI.Hierarchy.TaggedWidePassSites

namespace OAI
/-! # Reading the actual signed input on the selected before-state chord -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open ThreeFlat Routing Diagonal TraceWords TraceCircuit
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM Tagged
open scoped Classical BigOperators
variable {F V : Type} [Field F] [Fintype V] {S m D width copyWidth digits : ℕ}

/-- A mode is the fixed, bounded vector of native neighbor bucket words, in
the strip's original local-party order. The last bucket can mean absent. -/
def socketTags (m digits : ℕ) : (Fin m→Word digits) ↪ (Fin (m*digits)→Bool) where
  toFun a:=blocks m digits (fun i=>bits (a i))
  inj' _a _b eqn:=funext fun i=>bits_injective (congrFun ((blocks m digits).injective eqn) i)

/-- The finite format gate reads only the low degree-index bits for each local party. -/
def socketProgram (pin : Fin m→Fin digits→V)
    (body : (Fin m→Word digits)→BitNetwork F (Fintype.card V)) :=
  WideHost.localFamily (fun key=>Guard.mode (body key) (Function.uncurry pin ∘ finProdFinEquiv.symm)
    (socketTags m digits key)) (fun _=>Sum.inl)

theorem socketProgram_value (pin : Fin m→Fin digits→V)
    (body : (Fin m→Word digits)→BitNetwork F (Fintype.card V)) (v : V→Bool) (key : Fin m→Word digits)
    (reads : ∀i j,v (pin i j)=bits (key i) j) :
    TypedWiring.value (socketProgram pin body) v=TypedWiring.value (body key) v := by
  rw [socketProgram,WideHost.localFamily_eval]
  change (∏a,TypedWiring.value (Guard.mode (body a) _ (socketTags m digits a)) v)=_
  apply Guard.modes_value
  funext t
  obtain ⟨⟨i,j⟩,rfl⟩:=finProdFinEquiv.surjective t
  calc
    _ = v (pin i j) := by simp
    _ = bits (key i) j := reads i j
    _ = _ := (blocks_at (fun q => bits (key q)) i j).symm

theorem socketProgram_cost (pin : Fin m→Fin digits→V)
    (body : (Fin m→Word digits)→BitNetwork F (Fintype.card V)) :
    (socketProgram pin body).cells+(socketProgram pin body).internal≤
      177^(m*digits)*∑a,((body a).cells+(body a).internal) := by
  rw [socketProgram,WideHost.localFamily_size,Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _=>Guard.mode_fee ..

variable (U : Widths m) (i : Fin m) (key : Fin m→Word digits)
    (packed : Fin D×Fin width→V)

/-- The local signed input has a fixed public width, even on a wider physical
chord that also carries other commodities. Its high bits are zero. -/
def wantedSocket (t : (portGraph m).Port i) (j : Fin copyWidth) : V⊕Bool :=
  if h : j.val<U t.val.1 ∧ j.val<width ∧ (key (other t)).val<D then
    .inl (packed (⟨(key (other t)).val,h.2.2⟩,⟨j.val,h.2.1⟩))
  else .inr false

variable {s : Fin S} (total : (portGraph S).Port s→ℕ)
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) width total)

omit [Fintype V] in
theorem wantedSocket_read (v : V→Bool) (a : State U i) (state : (portGraph S).Port s→ℕ→Bool)
    (land : (portGraph m).Port i→(portGraph S).Port s)
    (keyRead : ∀t,0<U t.val.1→(key (other t)).val=index parts (other (land t)))
    (fits : ∀t,U t.val.1≤total (land t)) (room : ∀t,total t≤width)
    (chord : ∀q j,v (packed (q,j))=ChordAperture.canonical parts state q j)
    (low : ∀t (j : Fin (U t.val.1)),(a t).val.testBit j.val=state (land t) j.val)
    (t : (portGraph m).Port i) (j : Fin copyWidth) :
    Sum.elim v id (wantedSocket U i key packed t j)=(a t).val.testBit j.val := by
  by_cases live:j.val<U t.val.1
  · have upto:=live.trans_le (fits t)
    obtain ⟨q,hq,own⟩:=found parts (land t) (Nat.zero_lt_of_lt upto)
    have same : (key (other t)).val=q.val := (keyRead t (Nat.zero_lt_of_lt live)).trans hq.symm
    have small := (live.trans_le (fits t)).trans_le (room _)
    have ok : j.val<U t.val.1 ∧ j.val<width ∧ (key (other t)).val<D :=
      ⟨live,small,same.trans_lt q.isLt⟩
    rw [wantedSocket,dite_eq_left ok]
    change v (packed (_,_))=_
    rw [show (⟨(key (other t)).val,ok.2.2⟩ : Fin D)=q from Fin.ext same,chord]
    simpa only [ChordAperture.canonical,own,Option.elim_some,ite_eq_left upto] using (low t ⟨j.val,live⟩).symm
  · rw [wantedSocket,dite_eq_right (fun h=>live h.1)]
    exact (Nat.testBit_eq_false_of_lt ((a t).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt live)))).symm

/-- The low socket reads at an actual pass boundary follow from the other
packets' empty fibers and the low-word convention of the physical split. -/
theorem wanted_low {n : ℕ} (rest : Widths S) (g : Fin n→Widths S) (pick : Fin n)
    (place : Fin m ↪ Fin S) (s₀ : Fin m) (shape : g pick=Probe.placeWidths place U)
    (away : ∀k,k≠pick→Subsingleton (State (g k) (place s₀)))
    (z : State (rest+∑k,g k) (place s₀)) (t : (portGraph m).Port s₀) (j : Fin (U t.val.1)) :
    let a:=blockPortState g (place s₀) ((splitPortState rest (∑k,g k) (place s₀) z).2) pick
    let localState:=PhysicalMatrix.read place U s₀ (cast (congrArg (fun W=>State W (place s₀)) shape) a)
    (localState t).val.testBit j.val=(z (PhysicalMatrix.port place s₀ t)).val.testBit j.val := by
  intro a localState
  let t':=PhysicalMatrix.port place s₀ t
  have h : g pick t'.val.1=U t.val.1 :=
    (congrArg (fun W : Widths S=>W t'.val.1) shape).trans (PhysicalMatrix.width_at place U t.val.1)
  have digit:=PassMatrix.active_digit rest g pick (place s₀) away z t' (j.cast h.symm)
  change ((cast (congrArg (fun W=>State W (place s₀)) shape) a) t').val.testBit _=_
  rw [PacketNeighbor.state_cast_val shape]
  exact digit

end Hierarchy.WireTelescope.PacketNeighbor
end

end OAI
