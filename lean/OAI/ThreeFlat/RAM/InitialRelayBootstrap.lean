import OAI.ThreeFlat.RAM.InitialRelayGraph
import OAI.ThreeFlat.RAM.InitialRelayStored

namespace OAI
/-! # The native two-scan bootstrap publishes the initial lifted graph -/

namespace ThreeFlat.RAM.InitialRelayBootstrap

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure Diagonal Diagonal.SlotImage
open scoped Fin.CommRing

variable {W : ℕ}

def procedure (current : Word W) (C : Columns) (axes degree t : ℕ) : Procedure W :=
  (InitialRelayGraph.procedure current C.graph axes degree).seq (InitialRelayWidth.procedure current t)

def budget (W : ℕ) (C : Columns) (axes degree lanes : ℕ) : ℕ :=
  (13+6*(axes*degree)*(2*(InitialRelayGraph.term (W:=W) C.graph axes degree).binds+4))+
  (13+axes*degree*lanes*6)

private theorem closed_binds {n : ℕ} (f : PhysicalPinsExpr.Formula n) :
    (HeaderScan.closed f : DescriptorExpr.Term W 0 n).binds = f.work := by
  induction f <;> simp [HeaderScan.closed,PhysicalPinsExpr.Formula.work,DescriptorExpr.Term.literal,
    DescriptorExpr.Term.binary,DescriptorExpr.Term.select,DescriptorExpr.Term.load,DescriptorExpr.Term.binds, *] <;> omega

theorem graph_binds (origin axes degree : ℕ) :
    (InitialRelayGraph.term (W:=W) origin axes degree).binds=167 := by
  rw [InitialRelayGraph.term,closed_binds]; rfl

theorem size (current : Word W) (C : Columns) (axes degree t : ℕ) :
    (procedure current C axes degree t).labels=532 ∧
    (procedure current C axes degree t).registers=176 ∧
    (procedure current C axes degree t).slots=0 := by
  simp [procedure, Procedure.seq, InitialRelayGraph.procedure, InitialRelayWidth.procedure,
    HeaderScan.procedure, DescriptorExpr.Term.labels_eq, graph_binds, DescriptorExpr.Term.literal,
    DescriptorExpr.Term.binds]

theorem budget_eq (C : Columns) (axes degree lanes : ℕ) :
    budget W C axes degree lanes = 26+2028*(axes*degree)+6*(axes*degree*lanes) := by
  rw [budget,graph_binds]
  ring

def image (C : Columns) (axes degree lanes t : ℕ) (m : Memory W) : Memory W :=
  InitialRelayWidth.image C.widths (axes*degree*lanes) t (InitialRelayGraph.image C.graph axes degree m)

/-- The second scan consults the pointer and the last two seed fields
after the first one finishes. -/
def loaded (current : Word W) (C : Columns) (axes degree lanes : ℕ) (m : Memory W) : Prop :=
  InitialRelayGraph.loaded current C.graph axes degree m ∧
  InitialRelayWidth.loaded current C.widths (axes*degree*lanes) (InitialRelayGraph.image C.graph axes degree m)

theorem loaded_of_frame (current : Word W) (C : Columns) (axes degree lanes : ℕ) (m : Memory W)
    (graph : InitialRelayGraph.loaded current C.graph axes degree m)
    (width : InitialRelayWidth.loaded current C.widths (axes*degree*lanes) m)
    (frame : ∀ a, a=current.val ∨ a=(m current.val+2).val ∨ a=(m current.val+3).val →
      a<C.graph ∨ C.graph+6*(axes*degree)≤a) : loaded current C axes degree lanes m := by
  have frozen (a : ℕ) (h : a=current.val ∨ a=(m current.val+2).val ∨ a=(m current.val+3).val) :
      InitialRelayGraph.image C.graph axes degree m a=m a := by
    have := frame a h
    simp [InitialRelayGraph.image,fillSegment,show ¬(C.graph≤a ∧ a<C.graph+6*(axes*degree)) by omega]
  refine ⟨graph,?_⟩
  unfold InitialRelayWidth.loaded at width ⊢
  rwa [frozen _ (Or.inl rfl),frozen _ (Or.inr (Or.inl rfl)),frozen _ (Or.inr (Or.inr rfl))]

theorem spec (current : Word W) (C : Columns) (axes degree lanes t : ℕ)
    (graphFit : C.graph+6*(axes*degree)<2^W) (widthFit : C.widths+axes*degree*lanes<2^W)
    (hd : 0<degree) (ha : axes≤W) (wide : 6<2^W) :
    (procedure current C axes degree t).Spec (loaded current C axes degree lanes)
      (fun m out => out=image C axes degree lanes t m) (budget W C axes degree lanes) := by
  let ready := InitialRelayWidth.loaded current C.widths (axes*degree*lanes)
  have graph : (InitialRelayGraph.procedure current C.graph axes degree).Spec
      (loaded current C axes degree lanes) (fun m out => out=InitialRelayGraph.image C.graph axes degree m ∧ ready out)
      (13+6*(axes*degree)*(2*(InitialRelayGraph.term (W:=W) C.graph axes degree).binds+4)) := by
    intro P R K M pc reg pub exit hi hd' c m start hm
    obtain ⟨k,hk,out,m',run,finish,eq⟩ :=
      InitialRelayGraph.spec current C.graph axes degree graphFit hd ha wide M pc reg pub exit hi hd' c m start hm.1
    exact ⟨k,hk,out,m',run,finish,eq,by simpa only [eq] using hm.2⟩
  have widths : (InitialRelayWidth.procedure current t).Spec ready
      (fun m out => out=InitialRelayWidth.image C.widths (axes*degree*lanes) t m)
      (13+axes*degree*lanes*6) := InitialRelayWidth.spec current C.widths (axes*degree*lanes) t widthFit
  intro P R K machine
  apply Procedure.Spec.mono (A:=procedure current C axes degree t)
    (Procedure.Spec.seq (A:=InitialRelayGraph.procedure current C.graph axes degree)
      (B:=InitialRelayWidth.procedure current t) graph widths (fun _ _ h => h.2))
    (fun _ h => h) _ le_rfl machine
  rintro m out ⟨mid,⟨rfl,_⟩,rfl⟩
  rfl

theorem stored_spec {k r : ℕ} (current : Word W) (hk : 2≤k+1) (C : Columns) (t : ℕ)
    (hrows : C.rows=(k+1)*(r*2)) (wt : t<2^W) (axesFit : k+1≤W) (degree : 0<r*2) (wide : 6<2^W)
    (graphFit : C.graph+6*C.rows<2^W) (widthFit : C.widths+C.rows*2^(k+1)<2^W)
    (apart : C.graph+6*C.rows≤C.widths ∨ C.widths+C.rows*2^(k+1)≤C.graph) :
    (procedure current C (k+1) (r*2) t).Spec (loaded current C (k+1) (r*2) (2^(k+1)))
      (fun m out => out=image C (k+1) (r*2) (2^(k+1)) t m ∧
        Stored (LaneCursor.graph hk r) (Equiv.refl _) (CompressorPacking.Native.tagOrdinal _) C
          (fun a => (out a).val) (fun _ => t))
      (budget W C (k+1) (r*2) (2^(k+1))) := by
  intro P R K machine
  apply Procedure.Spec.mono (A:=procedure current C (k+1) (r*2) t)
    (spec current C (k+1) (r*2) (2^(k+1)) t (by simpa only [hrows] using graphFit)
      (by simpa only [hrows] using widthFit) degree axesFit wide) (fun _ h => h) _ le_rfl machine
  rintro m out rfl
  refine ⟨rfl,InitialRelayWidth.stored _ _ _ _ _ t wt hrows ?_ (by simpa only [hrows] using apart)⟩
  exact InitialRelayGraph.image_fields hk C m hrows axesFit graphFit

end ThreeFlat.RAM.InitialRelayBootstrap

end OAI
