import OAI.Hierarchy.DescentRotorPrivateFields
import OAI.Hierarchy.DescentPrivateTreeGeometry
import OAI.Hierarchy.DescentPrivateTreeRoutes

namespace OAI
/-! # Branch-independent fallback slots with live width read from the common prefix bank -/

namespace Hierarchy.DescentPrivateTreeTemplate
open DescentContacts DescentChosenRouter DescentMixedRouter DescentRouterSlots
open DescentTreePrefixIntervals DescentContactTree DescentResetCableSlots DescentOldOccurrenceRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def widthTerm (w u : ℕ) : Term w 0 1 :=
  ProtocolRAMPortScale.scale w (ProtocolRAMPortScale.bitWidth u) u

theorem scale_read {w : ℕ} (u val : ℕ) (m : Memory w) (vars : Fin 1→Word w) (input : vars 0=(val:Word w)) :
    (widthTerm w u).eval Fin.elim0 m vars=((u*val:ℕ):Word w) := by
  rw [widthTerm,ProtocolRAMPortScale.eval_scale _ _ _ _ (ProtocolRAMPortScale.fits u),input]
  simp [Nat.cast_mul,mul_comm]

theorem scale_cheap (w u : ℕ) : ProtocolRAM.admissible (widthTerm w u) := DescentWordProduct.scale_ok ..
theorem scale_work (w u : ℕ) : (widthTerm w u).binds≤1+2*ProtocolRAMPortScale.bitWidth u := ProtocolRAMPortScale.binds ..

variable {V A I F K : Type} [Fintype V] [DecidableEq V] [Fintype A] [Fintype I] [Fintype F] [Field K]
variable {k n h C bits u m B w : ℕ} (P : Placement V I F A k (2^n)) (Ht : ℕ)
variable (depth : ∀s t,(P.fallbackBook s t).height≤Ht) (G : NonlinearExpanders.Graph n h)
variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C) (u:=u) P G hw pay) (D : ℕ)
local notation "sel" => selected P G hw pay hardware
local notation "dev" => device G hw u P.contact P.input P.site P.owner P.align (D:=D)

theorem edgeAt_slot (s : Bool) (t : F) (e : Physical.Edge (P.fallbackBook s t).height) :
    edgeAt (P.fallbackBook s t).height (tree P Ht depth G s t e).val=some e := by
  change edgeAt _ (order _ e).val=some e
  rw [edgeAt,dite_eq_left (order _ e).isLt]
  exact congrArg some ((order _).symm_apply_apply e)

def arrivals (id : I↪Fin m) (terminal : F↪Fin B) (s : Bool) : Fin m→DescentPrivateLeafHistogram.Arrival B Ht :=
  DescentPrivateTreeRoutes.padded id (DescentPrivateTreeRoutes.route P.contact P.owner terminal
    (fun s t=>(P.fallbackBook s t).height) depth (fun s t=>(P.fallbackBook s t).codes) s)

/-- One fixed scheduled census for an entire orientation and both endpoint
reads of every private cable of every exceptional device in that bank. -/
theorem selected_headers (base : ℕ) (key : Expr) (id : I↪Fin m) (terminal : F↪Fin B)
    (s : Bool) (m₀ : Memory w) (fit : key.Fits w base)
    (words : ∀i,key.eval m₀ (i.val:Word w)=((DescentPrivateLeafHistogram.number (arrivals P Ht depth id terminal s i)).val:Word w))
    (room : Histogram.stop base m (B*2^Ht+1)<2^w) :
    let dst:=Histogram.after base key (fun i=>DescentPrivateLeafHistogram.number (arrivals P Ht depth id terminal s i)) m₀
    (Histogram.program w base m (B*2^Ht+1) key).Exec m₀ dst (Histogram.ticks m (B*2^Ht+1) key) ∧
    ∀(t : F) (site : Physical.Site (P.fallbackBook s t).height→ℕ) (e : (dev (sel s (.inr t))).Edge),
      read u ((terminal t).val*2^Ht) (fun j=>dst (Histogram.starts base m (B*2^Ht+1)+j))
        (lookup Ht (P.fallbackBook s t).height (privateWire P Ht depth G hw pay hardware D (s,.inr t) e).val site)=
        ![1,(site ((dev (sel s (.inr t))).src e):Word w),(site ((dev (sel s (.inr t))).dst e):Word w),
          ((dev (sel s (.inr t))).width e:Word w),1] := by
  obtain ⟨run,counts⟩:=DescentPrivateLeafHistogram.run_read base key (arrivals P Ht depth id terminal s) m₀ words fit room
  refine ⟨run,?_⟩
  intro t site e
  have eh : edgeAt (P.fallbackBook s t).height (privateWire P Ht depth G hw pay hardware D (s,.inr t) e).val=some e :=
    edgeAt_slot P Ht depth G s t e
  simp only [lookup,eh,read]
  have le : start Ht e.2≤ stop Ht e.2 := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have cap:=stop_le (e.1.isLt.trans_le (depth s t)) e.2
  have ct:=counts (terminal t) _ _ le cap
  have width:=(DescentPrivateTreeRoutes.width P.contact P.owner terminal (fun s t=>(P.fallbackBook s t).height) depth
    (fun s t=>(P.fallbackBook s t).codes) D u P.input P.site id s t e)
  rw [ct]
  change ![1,_,_,(u:Word w)*_,1]=![1,_,_,((DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner (fun _=>u) s (.inr t) _).width e:Word w),1]
  rw [width,Nat.cast_mul]
  rfl

end
end Hierarchy.DescentPrivateTreeTemplate

end OAI
