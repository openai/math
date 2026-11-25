import OAI.Hierarchy.DescentSharedBookImage
import OAI.Hierarchy.DescentShortBookScan

namespace OAI
/-! # Numeric address bounds for the measured fallback record -/
namespace Hierarchy.DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentPairedKeyComparison
variable {D cap w out : ℕ}

theorem unlessSeen_fits (a b : Expr) (xs : List Expr) (ha:a.Fits w out) (hb:b.Fits w out)
    (read : ∀ x∈xs,x.Fits w out) : (unlessSeen a b xs).Fits w out := by
  induction xs with
  | nil=>exact hb
  | cons u us ih=>exact ⟨read _ (by simp),ha,trivial,ih (fun x hx=>read x (by simp [hx]))⟩

theorem sum_fits (xs : List Expr) (read : ∀ x∈xs,x.Fits w out) : (foldSum xs).Fits w out := by
  induction xs with
  | nil=>trivial
  | cons u us ih=>exact ⟨read _ (by simp),ih (fun x hx=>read x (by simp [hx]))⟩

theorem measure_fits (peer : Fin D→Expr) (codes : Fin D×Fin cap→Expr) (H : ℕ)
    (target : Option (Expr×Expr)) (peers : ∀j,(peer j).Fits w out) (rows : ∀j,(codes j).Fits w out)
    (atTarget : ∀v z,target=some (v,z)→v.Fits w out ∧ z.Fits w out) :
    (measure peer codes H target).Fits w out := by
  apply sum_fits
  intro e he
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp he
  have selected:(pass (peer j.1) (codes j) target).Fits w out:=by
    cases eqn:target with
    | none=>trivial
    | some p=>
      rcases p with ⟨v,z⟩
      obtain ⟨vok,zok⟩:=atTarget v z eqn
      simp [pass,earlier,tail,high,Expr.Fits,vok,zok,peers,rows]
  refine ⟨peers _,trivial,trivial,unlessSeen_fits _ _ _ (peers _) ⟨rows _,trivial,trivial,selected⟩ ?_⟩
  intro x hx
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hx
  exact peers i
end Hierarchy.DescentFallbackRankRAM

namespace Hierarchy.DescentSharedBookScan.Public
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentFallbackRankRAM DescentNativeFallbackShapes
open scoped Classical
noncomputable section
variable {r Y D H cap base w out : ℕ}
theorem page_fit (i : ℕ) (hi:i<lanes) (before : stop base r Y D H cap≤out) (safe : out<2^w) :
    (page base (bits r Y D H cap) i).Fits w out := by
  let pad:=2^(bits r Y D H cap)
  have h:=Nat.mul_le_mul_right pad hi
  rw [Nat.succ_mul] at h
  have upper:base+i*pad+pad≤out:=by unfold stop at before;dsimp only [pad] at *;omega
  exact ⟨Nat.two_pow_pos _,by change pad<2^w;omega,upper⟩

theorem record_fits (oldNeighbors oldHub : Bank) (Ht : ℕ) (before : stop base r Y D H cap≤out)
    (safe : out<2^w) (nh : oldNeighbors.Fits w out) (hub : oldHub.Fits w out) :
    (record (bank base r Y D H cap oldNeighbors oldHub) H D (2^Ht) (Ht+2)).Fits w out := by
  let B:=bank base r Y D H cap oldNeighbors oldHub
  have control (op : Op) : (ctl B op).Fits w out:=by
    exact ⟨page_fit _ ((opOrdinal op).isLt.trans_le (Nat.le_add_right _ 4)) before safe,trivial⟩
  have near (x : Expr) (hx:x.Fits w out) : (nb B x).Fits w out:=⟨nh,control _,hx⟩
  have port (j : Fin D) : (side B j).Fits w out:=near _ trivial
  have thisSlot : (slot B).Fits w out:=near _ ⟨control _,trivial⟩
  have layout (i : Fin 4) :
      (page base (bits r Y D H cap) (Fintype.card Op+i.val)).Fits w out:=
    page_fit _ (by have:=i.isLt;unfold lanes;omega) before safe
  have shapesAt (j : Fin D×Fin (2^Ht)) : (shapes B j).Fits w out:=by
    refine ⟨layout 3,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
    · exact ⟨by simpa [B,bank] using layout 0,control _⟩
    · exact ⟨layout 1,control _⟩
    · exact ⟨layout 2,control _⟩
    · exact ⟨⟨hub,port _⟩,trivial,trivial,trivial⟩
  have empty : (measure (side B) (shapes B) H (Δ:=D) (cap:=2^Ht) none).Fits w out:=
    measure_fits _ _ _ _ port shapesAt (by simp)
  have someSlot : (measure (side B) (shapes B) H (Δ:=D) (cap:=2^Ht) (some (slot B,ctl B .destShape))).Fits w out:=
    measure_fits _ _ _ _ port shapesAt (by rintro _ _ h;cases h;exact ⟨thisSlot,control _⟩)
  have scan : (expr B H D (2^Ht)).Fits w out:=
    ⟨control _,trivial,empty,⟨thisSlot,trivial,trivial,someSlot⟩⟩
  exact ⟨scan,trivial,scan,trivial⟩

end
end Hierarchy.DescentSharedBookScan.Public

end OAI
