import OAI.Hierarchy.DescentTrivalentRotor
import OAI.Hierarchy.DescentNamedContact

namespace OAI
/-! # Removing dummy binary coordinates at the actual physical rotor terminals -/

namespace Hierarchy.DescentRotor.Physical
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits NonlinearExpanders
open Computability.BorderVNP.Crossing DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {K E : Type} [Field K] [Fintype E] {n h C w u D : ℕ} (G : Graph n h)
    {hw : 0<w} {src dst : E→Fin (2^n)} {pay : ℝ}
variable (P : BaseCircuit K G C w u hw src dst pay)

def rawBits (src dst : E→Fin (2^n)) (u : ℕ) : Pin (2^n)→ℕ
  | (v,false) => width src (fun _=>u) v
  | (v,true) => width dst (fun _=>u) v

def sourceWords (p : Ports (rawBits src dst u)) : E→Fin u→Bool :=
  labels src (fun _=>u) (fun v=>p (v,false))
def targetWords (p : Ports (rawBits src dst u)) : E→Fin u→Bool :=
  labels dst (fun _=>u) (fun v=>p (v,true))

def rawPins (x y : E→Fin u→Bool) : Ports (rawBits src dst u)
  | (v,false) => (labels src (fun _=>u)).symm x v
  | (v,true) => (labels dst (fun _=>u)).symm y v

private theorem packet_local {R : Type*} (addr : E→R×Fin w) (x y : E→Fin u→Bool) (p : R)
    (keep : ∀e,(addr e).1=p → x e=y e) : packetWord addr x p=packetWord addr y p := by
  funext k
  unfold packetWord
  apply congrArg (bitWord w)
  funext i
  split
  next h => exact congrFun (keep h.choose (congrArg Prod.fst h.choose_spec)) k
  next => rfl

theorem layer_local {A R : Type*} {Y : ℕ} (choose : R→A) (terminal : R→Fin Y)
    (addr : E→R×Fin w) (old : E→Fin Y) (agreement : ∀ e,terminal (addr e).1=old e)
    (x y : E→Fin u→Bool) (r : A) (v : Fin Y) (eqn : ∀e,old e=v → x e=y e) :
    fillRows 0 (fun p=>(choose p,terminal p)) (packetWord addr x) (r,v) =
    fillRows 0 (fun p=>(choose p,terminal p)) (packetWord addr y) (r,v) := by
  unfold fillRows
  split
  next q =>
    apply packet_local
    intro e use
    exact eqn e ((agreement e).symm.trans ((congrArg terminal use).trans (congrArg Prod.snd q.choose_spec)))
  next => rfl

private def encode (p : Ports (rawBits src dst u)) := actualPins P (sourceWords p) (targetWords p)

private theorem labels_local {J : Type} [Fintype J] (atSite : E → J) (wt : E → ℕ)
    (x y : Ports (width atSite wt)) (e : E) (same : x (atSite e) = y (atSite e)) :
    labels atSite wt x e = labels atSite wt y e :=
  congrArg (fun b =>
    DescentContactTree.Physical.concat (fun q : Fibre atSite (atSite e) => wt q.val) b ⟨e,rfl⟩) same

private theorem encode_local :
    DescentLocalAdapters.Local (rotor G P D) id (rawBits src dst u) (encode G P) := by
  intro j x y same pin hp
  rcases pin with ⟨v,(_|_)⟩
  · have read := same (v,false) hp
    have eqn (e : E) (h : src e=v) : sourceWords x e=sourceWords y e := by
      subst v
      exact labels_local src (fun _ => u) (fun j => x (j,false)) (fun j => y (j,false)) e read
    apply congrArg (bundle _ _ _).symm
    funext r
    exact layer_local P.choose (fun p=>p.1) (packetAddress src dst hw) src (fun _=>rfl) _ _ r v eqn
  · have read := same (v,true) hp
    have eqn (e : E) (h : dst e=v) : targetWords x e=targetWords y e := by
      subst v
      exact labels_local dst (fun _ => u) (fun j => x (j,true)) (fun j => y (j,true)) e read
    apply congrArg (bundle _ _ _).symm
    funext r
    exact layer_local P.choose (fun p=>p.2.1) (packetAddress src dst hw) dst (fun _=>rfl) _ _ r v eqn

def namedRotor (D : ℕ) := DescentLocalAdapters.graph (rotor G P D) id (rawBits src dst u)
def namedTables (D : ℕ) := DescentLocalAdapters.tables (rotor G P D) id (rawBits src dst u)
  (rotorTables G P D) (encode G P)

theorem named_value (p : Ports (rawBits src dst u)) :
    (namedRotor G P D).value (namedTables G P D) p =
      if ∀e,sourceWords p e=targetWords p e then 1 else 0 :=
  (DescentLocalAdapters.value _ _ _ _ _ (encode_local G P) p).trans
    (rotor_value G P (sourceWords p) (targetWords p))

theorem named_words (x y : E→Fin u→Bool) :
    (namedRotor G P D).value (namedTables G P D) (rawPins (src:=src) (dst:=dst) x y)=
      if x=y then 1 else 0 := by
  rw [named_value]
  simp [sourceWords,targetWords,rawPins,funext_iff]

theorem named_degree (v : (namedRotor G P D).Site) : (namedRotor G P D).bitDegree v≤3 :=
  (DescentLocalAdapters.degree _ _ _ Function.injective_id v).trans (rotor_degree G P v)

private theorem packet_volume :
    Fintype.card E≤P.layers*2^n*w := by
  let f (e : E) : (Fin P.layers × Fin (2^n)) × Fin w :=
    let p := packetAddress src dst hw e
    ((P.choose p.1,p.1.1),p.2)
  have unique : Function.Injective f := by
    intro e d eq
    have output := Prod.mk.inj eq
    have pair := Prod.mk.inj output.1
    exact packetAddress_injective src dst hw (Prod.ext (P.proper _ _ pair.1 pair.2) output.2)
  simpa using Fintype.card_le_of_injective f unique

theorem named_price :
    (((∑e,(namedRotor G P D).width e)+(∑q,rawBits src dst u q):ℕ):ℝ) ≤
      21*((2*h+4)*(2*h*C+2):ℕ)*pay := by
  apply le_trans _ (rotor_price G P (D:=D))
  apply Nat.cast_le.mpr
  apply Nat.add_le_add_left
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,rawBits,Finset.sum_add_distrib,width_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,smul_eq_mul]
  have bound := Nat.mul_le_mul_right u (packet_volume G P)
  nlinarith only [bound]

end
end Hierarchy.DescentRotor.Physical

end OAI
