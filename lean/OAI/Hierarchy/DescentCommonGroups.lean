import OAI.Hierarchy.DescentHostDirectory

namespace OAI
/-! # Projecting independently grouped old blocks to one shared next host -/

namespace Hierarchy.DescentHostDirectory
open scoped Classical
noncomputable section
variable {G V : Type} [DecidableEq G] [DecidableEq V]

def liftSite (g : G) : V↪G×V := ⟨fun v=>(g,v),fun _ _ h=>congrArg Prod.snd h⟩
def liftKey (g : G) : Key V↪Key (G×V) :=
  ⟨fun k=>((g,k.1),k.2),by rintro ⟨v,id⟩ ⟨w,code⟩ h;simpa using h⟩
def splitKey : Key (G×V) ≃ G×Key V where
  toFun k := (k.1.1,k.1.2,k.2)
  invFun a := liftKey a.1 a.2
  left_inv _ := rfl
  right_inv _ := rfl

def groupedNear (near : V→Finset V) (v : G×V) : Finset (G×V) := (near v.2).map (liftSite v.1)

omit [DecidableEq G] [DecidableEq V] in
theorem grouped_symmetric (near : V→Finset V) (sym : ∀a b,b∈near a ↔ a∈near b)
    (u v : G×V) : v∈groupedNear near u ↔ u∈groupedNear near v := by
  have one (x y : G×V) (h : y∈groupedNear near x) : x∈groupedNear near y := by
    obtain ⟨b,hb,eqn⟩:=Finset.mem_map.mp h
    obtain rfl : (x.1,b)=y := eqn
    exact Finset.mem_map.mpr ⟨x.2,(sym _ _).1 hb,Prod.eta x⟩
  exact ⟨one _ _,one _ _⟩

omit [DecidableEq G] [DecidableEq V] in
theorem grouped_degree (near : V→Finset V) (v : G×V) : (groupedNear near v).card=(near v.2).card :=
  Finset.card_map _

theorem grouped_next (near : V→Finset V) (D slots : ℕ) (g : G) (key : Key V) :
    next (groupedNear near) D slots (liftKey g key)=(next near D slots key).map (liftKey g) := by
  ext y
  obtain ⟨⟨h,w⟩,tail⟩ := y
  constructor
  · intro mem
    obtain ⟨allowed,within⟩ := Finset.mem_product.mp mem
    have home : h=g ∧ (w=key.1 ∨ w∈near key.1) := by
      rcases Finset.mem_insert.mp allowed with self | neighbor
      · change (h,w)=(g,key.1) at self
        exact ⟨congrArg Prod.fst self, Or.inl (congrArg Prod.snd self)⟩
      · obtain ⟨x,hx,hit⟩ := Finset.mem_map.mp neighbor
        change (g,x)=(h,w) at hit
        have xw : x=w := congrArg Prod.snd hit
        exact ⟨(congrArg Prod.fst hit).symm, Or.inr (xw ▸ hx)⟩
    obtain ⟨rfl,vertex⟩ := home
    exact Finset.mem_map.mpr ⟨(w,tail),Finset.mem_product.mpr ⟨Finset.mem_insert.mpr vertex,within⟩,rfl⟩
  · intro mem
    obtain ⟨⟨x,rest⟩,old,hits⟩ := Finset.mem_map.mp mem
    rw [←hits]
    obtain ⟨allowed,within⟩ := Finset.mem_product.mp old
    change ((g,x),rest) ∈ (insert (g,key.1) (groupedNear near (g,key.1))) ×ˢ _
    refine Finset.mem_product.mpr ⟨?_,within⟩
    rcases Finset.mem_insert.mp allowed with self | edge
    · exact Finset.mem_insert.mpr (Or.inl (congrArg (Prod.mk g) self))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨x,edge,rfl⟩))

theorem grouped_directory (near : V→Finset V) (D slots hops : ℕ) (g : G) (key : Key V) :
    directory (groupedNear near) D slots hops (liftKey g key)=
      (directory near D slots hops key).map (liftKey g) := by
  induction hops with
  | zero => simp [directory]
  | succ n ih =>
    ext y
    simp only [directory,ih,Finset.mem_biUnion,Finset.mem_map]
    constructor
    · rintro ⟨_,⟨x,old,rfl⟩,step⟩
      rw [grouped_next] at step
      obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp step
      exact ⟨z,⟨x,old,hz⟩,rfl⟩
    · rintro ⟨z,⟨x,old,step⟩,rfl⟩
      refine ⟨liftKey g x,⟨x,old,rfl⟩,?_⟩
      rw [grouped_next]
      exact Finset.mem_map.mpr ⟨z,step,rfl⟩

theorem same_and_close (near : V→Finset V) (D slots hops : ℕ) {x y : Key (G×V)}
    (close : y∈directory (groupedNear near) D slots hops x) :
    (splitKey y).1=(splitKey x).1 ∧ (splitKey y).2∈directory near D slots hops (splitKey x).2 := by
  have id : liftKey (splitKey x).1 (splitKey x).2=x := rfl
  rw [←id,grouped_directory] at close
  obtain ⟨k,h,rfl⟩ := Finset.mem_map.mp close
  exact ⟨rfl,h⟩

/-- One fixed host is reused by all resulting blocks. Every graph edge
certified in the grouped directory keeps the group and has a permitted common
neighbor, even when its old accepted history used group-specific dyadic marks. -/
theorem common_host {S E : Type} (name : S ↪ Key (G×V)) (src dst : E→S)
    (near : V→Finset V) (D slots hops : ℕ)
    (close : ∀e,name (dst e)∈directory (groupedNear near) D slots hops (name (src e))) :
    let addr := name.trans splitKey.toEmbedding
    (∀e,(addr (dst e)).1=(addr (src e)).1) ∧
    (∀e,(addr (dst e)).2∈directory near D slots hops (addr (src e)).2) := by
  exact ⟨fun e=>(same_and_close near D slots hops (close e)).1,
    fun e=>(same_and_close near D slots hops (close e)).2⟩

end
end Hierarchy.DescentHostDirectory

end OAI
