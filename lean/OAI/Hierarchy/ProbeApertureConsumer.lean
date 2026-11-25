import OAI.Hierarchy.ProbeApertureCanonical

namespace OAI
/-! # Wiring every compacted chord directly into a signed terminal circuit -/

noncomputable section
namespace Hierarchy.Probe.ApertureCompactor
open ThreeFlat Routing Routing.StableCompaction
open Diagonal TraceCircuit TraceWords MotifSelectorChecks
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {F : Type*} [CommRing F] {q n d b p u : ℕ}

/-- Common site pins and constants for genuine role widths and raw payload bits. -/
structure SocketRight (q n d b p : ℕ) where
  widths : Fin q→Fin (n*b)→Fin p⊕Bool
  inputs : Fin q→Fin (n*d)→Fin p⊕Bool

private def source : Fin p⊕Bool→BitSource (q*(n*d)) p
  | .inl i => .pin i
  | .inr v => .constant v

def SocketRight.wires (S : SocketRight q n d b p) (i : Fin q) :
    Fin (Size n d b)→BitSource (q*(n*d)) p :=
  Fin.append (fun j=>source (S.widths i j))
    (Fin.append (fun j=>source (S.inputs i j)) (fun j=>.hidden (finProdFinEquiv (i,j))))

def SocketRight.part (S : SocketRight q n d b p) (K : BitNetwork F u)
    (feed : Fin u→BitSource (q*(n*d)) p) : Unit⊕Fin q → Component F (q*(n*d)) p
  | .inl _=>⟨_,K,feed⟩
  | .inr i=>⟨_,strict F n d b,S.wires i⟩

def SocketRight.attach (S : SocketRight q n d b p) (K : BitNetwork F u)
    (feed : Fin u→BitSource (q*(n*d)) p) : BitNetwork F p :=
  BitNetwork.glue (fun i=>(S.part K feed i).net) (fun i=>(S.part K feed i).wire)

private theorem read_source (s : Fin p⊕Bool) (h : Fin (q*(n*d))→Bool) (v : Fin p→Bool) :
    (source s).read h v=Sum.elim v id s := by cases s <;> rfl

private theorem SocketRight.read_at (S : SocketRight q n d b p) (v : Fin p→Bool)
    (width : Fin q→Fin n→ℕ) (x y : Fin q→Fin (n*d)→Bool) (i : Fin q)
    (addr : ∀j,Sum.elim v id (S.widths i j)=blocks n b (fun a=>bits (width i a:Word b)) j)
    (input : ∀j,Sum.elim v id (S.inputs i j)=x i j) :
    (fun j=>(S.wires i j).read (blocks q (n*d) y) v)=pins (width i) (x i) (y i) := by
  funext j
  refine Fin.addCases (fun t=>?_) (fun j=>Fin.addCases (fun t=>?_) (fun t=>?_) j) j
  · simpa only [wires,pins,Fin.append_left,read_source] using addr t
  · simpa only [wires,pins,Fin.append_right,Fin.append_left,read_source] using input t
  · simp [wires,pins,BitSource.read,blocks_at,-Fin.natAdd_eq_addNat]

/-- Once the native binary widths and raw aperture bits have been read,
the trivalent contraction presents exactly the compacted payload to K.
Noncanonical private bits have zero weight in every field. -/
theorem SocketRight.attach_value (S : SocketRight q n d b p) (K : BitNetwork F u)
    (feed : Fin u→BitSource (q*(n*d)) p) (v : Fin p→Bool) (width : Fin q→Fin n→ℕ)
    (x : Fin q→Fin (n*d)→Bool) (bound : ∀i j,width i j≤d) (room : d<2^b)
    (addr : ∀i j,Sum.elim v id (S.widths i j)=blocks n b (fun a=>bits (width i a:Word b)) j)
    (input : ∀i j,Sum.elim v id (S.inputs i j)=x i j) :
    let out:=blocks q (n*d) (fun i=>compact (ApertureMask.mask (width i)) (x i))
    (S.attach K feed).eval v=if ∀i,canonical (width i) (x i) then
      K.eval (fun j=>(feed j).read out v) else 0 := by
  let wanted : Fin q→Fin (n*d)→Bool:=fun i=>compact (ApertureMask.mask (width i)) (x i)
  let good := ∀i,canonical (width i) (x i)
  have choice (y : Fin q→Fin (n*d)→Bool) :
      (∀i,canonical (width i) (x i) ∧ y i=compact (ApertureMask.mask (width i)) (x i)) ↔
      good ∧ y=wanted := by
    constructor
    · exact fun h=>⟨fun i=>(h i).1,funext (fun i=>(h i).2)⟩
    · rintro ⟨hc,rfl⟩
      exact fun i=>⟨hc i,rfl⟩
  rw [attach,BitNetwork.glue_eval,←(blocks q (n*d)).sum_comp]
  simp only [Fintype.prod_sum_type,Fintype.prod_unique,part,S.read_at v width x _ _ (addr _) (input _),
    strict_eval F _ (bound _) room,Fintype.prod_boole,choice]
  change (∑ y : Fin q→Fin (n*d)→Bool, K.eval (fun j=>(feed j).read (blocks q (n*d) y) v) *
    (if good ∧ y=wanted then 1 else 0)) = if good then K.eval (fun j=>(feed j).read (blocks q (n*d) wanted) v) else 0
  by_cases clean : good <;> simp [clean,mul_ite]

theorem SocketRight.attach_cost (S : SocketRight q n d b p) (K : BitNetwork F u)
    (feed : Fin u→BitSource (q*(n*d)) p) :
    (S.attach K feed).cells+(S.attach K feed).internal ≤ K.cells+K.internal+q*(n*d)+
      q*(n*d*(200*b+65)+(n*d+n*d*(500*b+501)+128000*(n*d+1)*(Nat.log 2 (n*d+1)+2)^3)) := by
  have h:=Nat.mul_le_mul_left q (strict_cost F n d b)
  simp only [attach,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_sum_type,
    part,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_unit,nsmul_eq_mul,
    Nat.cast_id,one_mul]
  rw [Nat.mul_add] at h
  omega

end Hierarchy.Probe.ApertureCompactor
end

end OAI
