import OAI.Hierarchy.DescentTerminalLocalPortNames
import OAI.Hierarchy.DescentTerminalRouteRows
import OAI.Hierarchy.DescentTerminalLocalPortGather

namespace OAI
/-! # Agreement of the issued local tokens with the actual two orders in every occupied bin -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalRouteRows Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {G V M A S W q a : ℕ} (sites : Fin S→Site) (pos : 0<W) (qp : 0<q)
  (f : ∀i,Room (sites i) G V M A) (fit : ∀i,(sites i).rows q≤W)
  (cables : ∀i,(sites i).Name ↪ Word a) (args : ∀i,(sites i).Arg→Word a)
local notation "C" => counts (q:=q) sites
local notation "K" => Bins (W:=W) (q:=q) sites
abbrev HomeRow := (i : Fin S) × Fin (C i)
def physical (u : HomeRow (q:=q) sites) : Fin K×Fin W :=
  finProdFinEquiv.symm (rowIndex pos C u)
theorem physical_inj : Function.Injective (physical (q:=q) sites pos) :=
  finProdFinEquiv.symm.injective.comp (rowIndex pos C).injective
def findHome (b : Fin K) (r : Fin W) : Option (HomeRow (q:=q) sites) :=
  if h : ∃u,physical sites pos u=(b,r) then some h.choose else none
theorem home_iff (b : Fin K) (r : Fin W) (u : HomeRow (q:=q) sites) :
    findHome sites pos b r=some u ↔ physical sites pos u=(b,r) := by
  by_cases live : ∃v,physical sites pos v=(b,r)
  · simp only [findHome,dite_eq_left live,Option.some.injEq]
    exact ⟨fun eqn=>eqn ▸ live.choose_spec,fun h=>physical_inj sites pos (live.choose_spec.trans h.symm)⟩
  · simp [findHome,live];exact fun h=>live ⟨u,h⟩

def localOwner (i : Fin S) : Fin W := ⟨offset W C i,Nat.mod_lt _ pos⟩
def tagged (v : Named sites) := Book.own (localOwner (q:=q) sites pos v.1) (cables v.1 v.2)
def matrix (b : Fin K) (r : Fin W) : Row q (Nat.clog 2 (W*2^a)) := fun side slot=>
  (findHome sites pos b r).bind (fun u=>((issue (sites u.1) (f u.1) (cables u.1) (args u.1)).row q u.2.val side slot).map
    (Book.own (localOwner (q:=q) sites pos u.1)))
include fit in
theorem real_names (sourceRef : ∀i v,args i v=cables i ((sites i).arg v.1 v.2)) :
    Names sites pos qp (tagged (q:=q) sites pos cables) (matrix sites pos f cables args) := by
  constructor
  · intro b src t
    constructor
    · intro live
      unfold matrix at live
      obtain ⟨u,hu,visible⟩ := Option.bind_eq_some_iff.mp live
      obtain ⟨n,hname,htag⟩ := Option.map_eq_some_iff.mp visible
      obtain ⟨j,hj,eqn⟩:=(live_port (sites u.1) (f _) (cables _) (args _) qp u.2.val src.2 n).1 hname
      have left : (Site.source qp j).1=u.2:=Fin.ext (congrArg Prod.fst hj)
      have right : (Site.source qp j).2=src.2:=Fin.ext (congrArg Prod.snd hj)
      refine ⟨⟨u.1,j⟩,?_,by simpa [tagged,eqn] using htag⟩
      have whereAt:=(home_iff sites pos b src.1 u).1 hu
      exact Prod.ext ((congrArg Prod.fst (show physical sites pos ⟨u.1,(Site.source qp j).1⟩=(b,src.1) by rwa [left])).trans rfl)
        (Prod.ext (congrArg Prod.snd (show physical sites pos ⟨u.1,(Site.source qp j).1⟩=(b,src.1) by rwa [left])) right)
    · rintro ⟨⟨i,j⟩,whereAt,rfl⟩
      let r:=Site.source qp j
      have gi:physical sites pos ⟨i,r.1⟩=(b,src.1):=congrArg (fun z:Fin K×(Fin W×Fin q)=>(z.1,z.2.1)) whereAt
      have sj : r.2=src.2:=congrArg (fun z:Fin K×(Fin W×Fin q)=>z.2.2) whereAt
      simp only [matrix,(home_iff sites pos b src.1 _).2 gi,Option.bind_some]
      rw [(live_port (sites i) (f _) (cables _) (args _) qp r.1.val src.2 _).2 ⟨j,Prod.ext rfl (congrArg Fin.val sj),rfl⟩]
      rfl
  · intro b dst t
    constructor
    · intro live
      unfold matrix at live
      obtain ⟨u,hu,visible⟩ := Option.bind_eq_some_iff.mp live
      obtain ⟨n,hname,htag⟩ := Option.map_eq_some_iff.mp visible
      obtain ⟨j,hj,eqn⟩:=(live_arg (sites u.1) (f _) (cables _) (args _) qp u.2.val dst.2 n).1 hname
      have left : (Site.target qp j).1=u.2:=Fin.ext (congrArg Prod.fst hj)
      have right : (Site.target qp j).2=dst.2:=Fin.ext (congrArg Prod.snd hj)
      refine ⟨⟨u.1,j⟩,?_,?_⟩
      · have whereAt:=(home_iff sites pos b dst.1 u).1 hu
        have loc : physical sites pos ⟨u.1,(Site.target qp j).1⟩=(b,dst.1):=by rwa [left]
        have bin_at : (physical sites pos ⟨u.1,(Site.target qp j).1⟩).1 = b := congrArg Prod.fst loc
        have row_at : (physical sites pos ⟨u.1,(Site.target qp j).1⟩).2 = dst.1 := congrArg Prod.snd loc
        exact Prod.ext bin_at (Prod.ext row_at right)
      · exact (congrArg (Book.own (localOwner (q:=q) sites pos u.1))
          ((sourceRef u.1 j).symm.trans eqn)).trans htag
    · rintro ⟨⟨i,j⟩,whereAt,rfl⟩
      let r:=Site.target qp j
      have gi:physical sites pos ⟨i,r.1⟩=(b,dst.1):=congrArg (fun z:Fin K×(Fin W×Fin q)=>(z.1,z.2.1)) whereAt
      have sj:r.2=dst.2:=congrArg (fun z:Fin K×(Fin W×Fin q)=>z.2.2) whereAt
      simp only [matrix,(home_iff sites pos b dst.1 _).2 gi,Option.bind_some]
      rw [(live_arg (sites i) (f _) (cables _) (args _) qp r.1.val dst.2 _).2 ⟨j,Prod.ext rfl (congrArg Fin.val sj),rfl⟩]
      exact congrArg (fun token => some (Book.own (localOwner (q:=q) sites pos i) token)) (sourceRef i j)
  · rintro ⟨i,v⟩ ⟨j,u⟩ same equal
    have tagVal : (tagged (q:=q) sites pos cables ⟨i,v⟩).val =
        (tagged (q:=q) sites pos cables ⟨j,u⟩).val := congrArg Fin.val equal
    have eqv : finProdFinEquiv (localOwner (q:=q) sites pos i,cables i v)=
        finProdFinEquiv (localOwner (q:=q) sites pos j,cables j u):=
      Fin.ext tagVal
    obtain ⟨home,code⟩:=Prod.mk.inj (finProdFinEquiv.injective eqv)
    have sameBin : bin W C i=bin W C j:=by simpa [source,global_bin sites pos fit] using congrArg Fin.val same
    have shared : first W C i=first W C j := by rw [first_eq W C i,first_eq W C j,sameBin];exact congrArg (_+·) (congrArg Fin.val home)
    have occupied (v : Fin S) : 0<C v:=by simp [counts,Site.rows]
    have eqr : rowIndex pos C ⟨i,⟨0,occupied i⟩⟩=rowIndex pos C ⟨j,⟨0,occupied j⟩⟩:=Fin.ext (by
      change first W C i + 0 = first W C j + 0
      exact congrArg (· + 0) shared)
    have close:=congrArg Sigma.fst ((rowIndex pos C).injective eqr)
    change i=j at close
    subst j
    exact congrArg (Sigma.mk i) ((cables i).injective code)

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
