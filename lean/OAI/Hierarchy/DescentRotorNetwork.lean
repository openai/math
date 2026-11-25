import OAI.Hierarchy.DescentGoodBaseMatrix
import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # The configured layered rotor as a literal open binary network -/

namespace Hierarchy.DescentRotor.Physical
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open DescentBaseProfile Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {Y : ℕ} (c : Fin Y → Fin Y → ℕ)

def chunks (s b : ℕ) : (Fin (s*b) → Bool) ≃ (Fin s → Fin b → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)).trans (Equiv.curry _ _ _)

/-- One physical binary word, indexed first by layer and then bundle digit. -/
def bundle (R u w : ℕ) : (Fin (R*(u*w))→Bool) ≃ (Fin R → Fin u → Fin (2^w)) :=
  (chunks R (u*w)).trans (Equiv.piCongrRight fun _=> (chunks u w).trans (Equiv.piCongrRight fun _=> bitWord w))

abbrev Pin (Y : ℕ) := Fin Y × Bool

def host (D R C w u : ℕ) : Network D (Pin Y) (fun _=>R*(u*w)) where
  Site := Fin Y
  Edge := Arc c
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := (supplyGraph c).tail
  dst := (supplyGraph c).head
  width _ := R*(u*(C*w))
  attach := Prod.fst
  position _ := 0
  in_ball _ := by simp

variable {K : Type*} [Field K] {D R C w u : ℕ}

private def endpoint (v : Fin Y) (p : (supplyGraph c).Port v) :
    {e : Arc c // (supplyGraph c).tail e=v ∨ (supplyGraph c).head e=v} := ⟨p.val.1,by
  have hit := p.property
  cases side : p.val.2 with
  | false => exact Or.inl (by simpa [side,PortGraph.vertex] using hit)
  | true => exact Or.inr (by simpa [side,PortGraph.vertex] using hit)⟩

abbrev LayerTable (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (K : Type*) := (v : Fin Y) →
  Fin (2^w) → Fin (2^w) → (supplyGraph c).State (fun _=>Fin (2^(C*w))) v → K

def hostTables (T : Fin R → LayerTable c C w K) : (host c D R C w u).Tables K :=
  fun v wires pins => ∏r, ∏k, T r v
    (bundle R u w (pins ⟨(v,false),rfl⟩) r k) (bundle R u w (pins ⟨(v,true),rfl⟩) r k)
    (fun p=>bundle R u (C*w) (wires (endpoint c v p)) r k)

def assignments : (host c D R C w u).Assignment ≃ (Fin R → Arc c → Fin u → Fin (2^(C*w))) :=
  (Equiv.piCongrRight fun _=>bundle R u (C*w)).trans (Equiv.piComm _)

/-- Padded inactive rows have their actual zero words. Active rows carry the
binary words of exactly the packets chosen for this base. -/
def pinValues (x y : Fin R → Fin Y → Fin u → Fin (2^w)) : Ports (fun _ : Pin Y=>R*(u*w)) :=
  fun t=>(bundle R u w).symm (fun r=>if t.2 then y r t.1 else x r t.1)

private abbrev ArcWords (C w u : ℕ) := Arc c → Fin u → Fin (2^(C*w))

private def siteFactor (T : Fin R → LayerTable c C w K)
    (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (r : Fin R) (a : ArcWords c C w u) (v : Fin Y) : K :=
  ∏ k, T r v (x r v k) (y r v k) (fun p => a p.val.1 k)

private theorem pin_left (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (v : Fin Y) (r : Fin R) :
    bundle R u w (pinValues x y (v,false)) r = x r v :=
  congrFun ((bundle R u w).apply_symm_apply (fun j => x j v)) r

private theorem pin_right (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (v : Fin Y) (r : Fin R) :
    bundle R u w (pinValues x y (v,true)) r = y r v :=
  congrFun ((bundle R u w).apply_symm_apply (fun j => y j v)) r

private theorem site_read (T : Fin R → LayerTable c C w K)
    (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (a : (host c D R C w u).Assignment) (v : Fin Y) :
    (host c D R C w u).read (hostTables c T) a (pinValues x y) v =
      ∏ r, siteFactor c T x y r (assignments (D:=D) (R:=R) (C:=C) (w:=w) (u:=u) c a r) v := by
  change (∏ r : Fin R, ∏ k : Fin u, T r v (bundle R u w (pinValues x y (v,false)) r k)
    (bundle R u w (pinValues x y (v,true)) r k) (fun p => bundle R u (C*w) (a p.val.1) r k)) = _
  apply Finset.prod_congr rfl
  intro r _
  rw [pin_left, pin_right]
  rfl

private def layerFactor (T : Fin R → LayerTable c C w K)
    (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (r : Fin R) (a : ArcWords c C w u) : K :=
  ∏ v, siteFactor c T x y r a v

private theorem layer_value (T : Fin R → LayerTable c C w K)
    (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (r : Fin R) :
    attachedLayer (T r) u (x r) (y r) = ∑ a, layerFactor c T x y r a := by
  rw [attachedLayer_eq]
  unfold PortGraph.contraction
  apply Finset.sum_congr (congrArg (@Finset.univ (ArcWords c C w u)) (Subsingleton.elim _ _))
  intro a _
  rfl

private theorem read_product (T : Fin R → LayerTable c C w K)
    (x y : Fin R → Fin Y → Fin u → Fin (2^w)) (a : (host c D R C w u).Assignment) :
    (∏ v : Fin Y, (host c D R C w u).read (hostTables c T) a (pinValues x y) v) =
      ∏ r, layerFactor c T x y r (assignments (D:=D) (R:=R) (C:=C) (w:=w) (u:=u) c a r) := by
  exact (Finset.prod_congr rfl (fun v _ => site_read (D:=D) c T x y a v)).trans Finset.prod_comm

theorem host_value (T : Fin R → LayerTable c C w K) (x y : Fin R → Fin Y → Fin u → Fin (2^w)) :
    (host c D R C w u).value (hostTables c T) (pinValues x y) =
      ∏r, attachedLayer (T r) u (x r) (y r) := by
  let decode := assignments (D:=D) (R:=R) (C:=C) (w:=w) (u:=u) c
  let total (z : Fin R → ArcWords c C w u) := ∏ r, layerFactor c T x y r (z r)
  calc
    _ = ∑ a : (host c D R C w u).Assignment, total (decode a) :=
      Finset.sum_congr rfl (fun a _ => read_product (D:=D) c T x y a)
    _ = ∑ z : Fin R → ArcWords c C w u, total z := decode.sum_comp total
    _ = ∏ r, ∑ a, layerFactor c T x y r a := (Fintype.prod_sum (layerFactor c T x y)).symm
    _ = _ := Finset.prod_congr rfl (fun r _ => (layer_value c T x y r).symm)

variable {E : Type*} [Fintype E] {n h : ℕ} {G : NonlinearExpanders.Graph n h} {hw : 0<w}
  {src dst : E→Fin (2^n)} {pay : ℝ}

def actualPins (P : BaseCircuit K G C w u hw src dst pay) (x y : E→Fin u→Bool) :
    Ports (fun _ : Pin (2^n)=>P.layers*(u*w)) :=
  pinValues
    (fun r v=>fillRows 0 (fun e=>(P.choose e,e.1)) (packetWord (packetAddress src dst hw) x) (r,v))
    (fun r v=>fillRows 0 (fun e=>(P.choose e,e.2.1)) (packetWord (packetAddress src dst hw) y) (r,v))

theorem actual_value (P : BaseCircuit K G C w u hw src dst pay) (x y : E→Fin u→Bool) :
    (host G.arcs D P.layers C w u).value (hostTables G.arcs P.tables) (actualPins P x y)=
      if ∀e,x e=y e then 1 else 0 :=
  (host_value (D:=D) G.arcs P.tables _ _).trans (P.realizes x y)

end
end Hierarchy.DescentRotor.Physical

end OAI
