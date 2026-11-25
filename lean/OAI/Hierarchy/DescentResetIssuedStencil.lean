import OAI.Hierarchy.DescentResetPackedStencil
import OAI.Hierarchy.DescentResetPackedSplit
import OAI.Hierarchy.DescentFallbackOrderPivot

namespace OAI
/-! # The physically evaluated stencil returns the actual measured reset endpoint -/

namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentColonies DescentGL DescentIssuedFallbackPanel
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {m c n q : ℕ} (small : c≤ m)
variable (near : V→Finset V) (b : V→ℕ) (L : Layout m) (weight : V→Block m→ℕ) (traffic : V→V→Block m→ℕ)
variable (hub : V→Bool) (Δ f B K g Y cap : ℕ) (hi : Block c) (v : V)
variable (ports : Fin q→Option (Contacts near)) (inc : V→List V)
local notation "D" => (32*Nat.clog 2 (2*Δ))
local notation "weights" => (fun u z=>rearrangedLoad weight L u (join small hi z))

def edgeWords (port : Option (Contacts near)) (j : Fin 2 ⊕ Block (m-c)) : ℕ :=
  match port with
  | none=>0
  | some e=>match j with
    | .inl s=>
      if s.val=0 then edgeLevel near b e-c
      else threshold K (2^f*B) (edgeLevel near b e) (∑z,traffic e.1 e.2.val z) (2^(m-c)*cap)
    | .inr x=>traffic e.1 e.2.val ((rearrange L).symm (join small hi x))

/-- Facts about the elementary source columns. The directory may repeat a live port.
The two scalar columns of each contact are shared by every low-coordinate query. -/
structure Input (a : panel (m-c) q n) : Prop where
  base : header a 0=b v-c
  merged : header a 1=m-g-c
  hubBit : decide (header a 2≠0)=hub v
  weightAt (x) : old a x=weights v x
  flag (d : Fin (m-c)) (x) : marked a d x=Scan.lookup (Scan.build inc weights D (2^(f+1)*B) (m-c)) d.val v x
  order (i x) : before a i x=decide ((rearrange L).symm (join small hi i)<(rearrange L).symm (join small hi x))
  peers (p) (j) : edge a p j=edgeWords small near b L traffic f B K cap hi (ports p) j

omit [DecidableEq V] in
private theorem depth_of_lookup {r : ℕ} (rows : Scan.Buffer V r) (v : V)
    (a : DescentColonies.PackedSplit.Flags r) (flags : ∀d x,a d x=Scan.lookup rows d.val v x) (x : Block r) :
    DescentColonies.PackedSplit.depth a x=Scan.leafDepth rows v x := by
  apply congrArg Prod.fst
  have go (len start : ℕ) (top : start+len≤r) :
      Scan.seek (fun d=>if h:d<r then a ⟨d,h⟩ x else false) len start=
        Scan.seek (fun d=>Scan.lookup rows d v x) len start := by
    induction len generalizing start with
    | zero=>rfl
    | succ t ih=>
      have inside : start<r := by omega
      simp only [Scan.seek,dite_eq_left inside,flags ⟨start,inside⟩ x]
      split
      · rw [ih (start+1) (by omega)]
      · rfl
  exact go r 0 (by omega)

theorem issued_word (a : panel (m-c) q n) (baseLow : ∀u,c≤b u) (hubLow : c≤ m-g)
    (depth : ∀u,b u≤ m) (safe : ∀u x,weight u x≤B) (trafficBound : ∀u z x,traffic u z x≤cap)
    (positive : 0<K) (hB : 0<B) (hD : 0<D)
    (listAt : ∀u z,u∈inc z ↔ z∈near u)
    (covered : ∀e:Contacts near,incident near v e ↔ ∃p,ports p=some e)
    (physical : Input small near b L weight traffic hub Δ f B K g cap hi v ports inc a) (x : Block (m-c)) :
    let keys:=resetKeys near Δ f B K weight (fun u z i=>(traffic u z i:ℝ)) b depth L
    let data:=endpoint near b L weight f D B g Y safe (fun u j=>(u,j)∈keys) hub v ((rearrange L).symm (join small hi x))
    word a f B Y x=2*shapeCode (m-c) Y (fieldsRelative c data)+
      ((hub v) || decide ((v,group (b v) (join small hi x))∈keys)).toNat := by
  intro keys data
  have depths (i) : split a i=DescentColonies.depth weights (fun t z=>z∈near t) D (f+1) B (fun u j=>safe u _) v i :=
    (depth_of_lookup _ _ (marked a) physical.flag i).trans (Scan.leafDepth_eq inc _ listAt weights hD (f+1) B (fun u j=>safe u _) v i)
  have overEq : fails a x ↔ «over» small near b L traffic f B K hi v x (fun _=>2^(m-c)*cap) := by
    constructor
    · rintro ⟨p,i,agree,above⟩
      rw [physical.base] at agree
      cases lookup : ports p with
      | none=>simp only [physical.peers,lookup,edgeWords,binHere,ite_self,Finset.sum_const_zero,lt_self_iff_false] at above
      | some e=>
        refine ⟨e,(covered e).mpr ⟨p,lookup⟩,i,agree,?_⟩
        simpa only [physical.peers,lookup,edgeWords,Fin.val_zero,Fin.val_one,zero_ne_one,one_ne_zero,↓reduceIte] using above
    · rintro ⟨e,live,i,agree,above⟩
      obtain ⟨p,yes⟩:=(covered e).mp live
      refine ⟨p,i,?_,?_⟩
      · simpa only [physical.base] using agree
      · simpa only [physical.peers,yes,edgeWords,Fin.val_zero,Fin.val_one,zero_ne_one,one_ne_zero,↓reduceIte] using above
  have localBad : bad a x=decide ((v,group (b v) (join small hi x))∈keys) := by
    unfold bad keys
    apply Bool.decide_congr
    rw [physical.base,depths,keys_at small near b baseLow depth L weight traffic Δ f B K hi v x cap trafficBound positive hB]
    rw [show 2*(2^f*B)=2^(f+1)*B by rw [pow_succ];ring]
    exact or_congr (split_iff_before weights (fun t z=>z∈near t) D (f+1) B (fun t j=>safe t _) v x _).symm overEq
  have truthful:=row_at small near b L weight f D B g Y safe (fun u j=>(u,j)∈keys) hub v hi x
    (baseLow v) depth hubLow
  have rowEq : shape a f B Y x=fieldsRelative c data := by
    dsimp only [shape,data]
    rw [physical.base,physical.merged,physical.hubBit,localBad]
    have sameFlag : decide ((v,group (b v) (join small hi x))∈keys) =
        @decide ((v,group (b v) (join small hi x))∈keys) (Classical.propDecidable _) :=
      congrArg (fun d=>@decide ((v,group (b v) (join small hi x))∈keys) d) (Subsingleton.elim _ _)
    rw [sameFlag]
    simpa only [funext physical.weightAt,funext depths,funext (fun i=>funext (physical.order i))] using truthful.symm
  simp only [word,rowEq,physical.hubBit,localBad]

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
