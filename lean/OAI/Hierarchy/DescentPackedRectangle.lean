import OAI.Hierarchy.DescentMeasuredHeaderScan
import OAI.Hierarchy.DescentPackedWalshCube
import OAI.Hierarchy.DescentPackedWalshRAM

namespace OAI
/-! # Mask and gather whole old site or contact words into Walsh estimator rows -/
namespace Hierarchy.DescentPackedRectangle
open DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l D b w : ℕ}
local notation "k" => u+l
local notation "N" => H*(k+1)+H*D
local notation "R" => Rows H k D
local notation "idx" => rowOrd H k D
local notation "coords" => DescentWalshPhysical.coordinates

structure Gather where
  owner : Bank
  kind : Bank
  pointer : Bank
  live : Bank
  sites : Bank
  flows : Bank

def Gather.banks (A : Gather) := [A.owner,A.kind,A.pointer,A.live,A.sites,A.flows]
def expression (A : Gather) : Expr :=
  .branch .eq (.lookup A.live (.lookup A.owner .row)) (.lit 0) (.lit 0)
    (.branch .eq (.lookup A.kind .row) (.lit 0) (.lookup A.sites (.lookup A.pointer .row))
      (.lookup A.flows (.lookup A.pointer .row)))

def offset (pitch : ℕ) (t : R) (p : Cube u) : ℕ := match t with
  | .inl (v,_) => (DescentPackedWalsh.row v p).val
  | .inr (v,i) => i.val*pitch+(DescentPackedWalsh.row v p).val

structure Room (A : Gather) (pitch H u l D w out : ℕ) : Prop where
  banks : ∀B∈A.banks,B.Fits w out
  owner : (H*(u+l+1)+H*D)*2^u≤A.owner.size
  kind : (H*(u+l+1)+H*D)*2^u≤A.kind.size
  pointer : (H*(u+l+1)+H*D)*2^u≤A.pointer.size
  flags : H*(u+l+1)+H*D≤A.live.size
  sites : H*2^u≤A.sites.size
  width : H*2^u≤pitch
  traffic : D*pitch≤A.flows.size
  output : out+(H*(u+l+1)+H*D)*2^u<2^w

structure Public (A : Gather) (pitch H u l D : ℕ) (m : Memory w) : Prop where
  owner (t : Rows H (u+l) D) (p : Cube u) : m (A.owner.base+(DescentPackedWalsh.row ((rowOrd H (u+l) D) t) p).val)=(((rowOrd H (u+l) D) t).val:Word w)
  kind (t : Rows H (u+l) D) (p : Cube u) : m (A.kind.base+(DescentPackedWalsh.row ((rowOrd H (u+l) D) t) p).val)=(tag t:Word w)
  pointer (t : Rows H (u+l) D) (p : Cube u) : m (A.pointer.base+(DescentPackedWalsh.row ((rowOrd H (u+l) D) t) p).val)=(offset (H:=H) (u:=u) (l:=l) (D:=D) pitch t p:Word w)

theorem zero_word : chunk (fun _ : Cube l=>(0:Cell b))=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin (2^l)=>(0:Cell b))).val=0
  simp

/-- Emit every padded site-level or contact as an actual packed source word.
The physical source banks are precisely the preceding site and signed flow outputs. -/
theorem native (A : Gather) (pitch out : ℕ) (S : Room A pitch H u l D w out) (mem : Memory w)
    (depth : Fin H→ℕ) (next : Port H D→Option (Fin H))
    (site : Fin H→DescentGL.Bits k→ℕ) (flow : Port H D→DescentGL.Bits k→ℕ)
    (wide : 1<2^w) («public» : Public A pitch H u l D mem)
    (active : ∀t:R,mem (A.live.base+(idx t).val)=(isLive depth next t:Word w))
    (oldSite : Installed A.sites.base (fun v=>shaped (u:=u) (l:=l) (fun z=>(site v ((coords _).symm z):Cell b))) mem)
    (oldFlow : ∀j : Fin D,Installed (A.flows.base+j.val*pitch)
      (fun v=>shaped (u:=u) (l:=l) (fun z=>(flow (v,j) ((coords _).symm z):Cell b))) mem) :
    let dst:=image out (N*2^u) (expression A) mem
    (scan w out (N*2^u) (expression A)).Exec mem dst (4+100*(N*2^u)) ∧
    Installed out (fun v=>shaped (u:=u) (l:=l) (fun z=>(realLoad depth next site flow ((rowOrd H (u+l) D).symm v) ((coords _).symm z):Cell b))) dst ∧
    CheapCode (scan w out (N*2^u) (expression A)) := by
  intro dst
  have fits : (expression A).Fits w out := by
    simp only [expression,Expr.Fits]
    repeat' first | exact S.banks _ (by simp [Gather.banks]) | trivial | constructor
  refine ⟨?_, ?_, scan_cheap w out (N*2^u) (expression A)⟩
  · have rate : 2*(expression A).work+4=100 := rfl
    rw [show 4+100*(N*2^u) = 4+(N*2^u)*(2*(expression A).work+4) by
      rw [rate, Nat.mul_comm 100]]
    intro pcCount regCount slotCount machine
    exact scan_exec out (N*2^u) (expression A) mem fits S.output machine
  intro v p
  obtain ⟨t,rfl⟩ := (rowOrd H (u+l) D).surjective v
  simp only [Equiv.symm_apply_apply]
  let slot := DescentPackedWalsh.row (idx t) p
  refine (ProtocolRAMGeneratedWrite.read_image out (N*2^u) (expression A) mem slot).trans ?_
  have rOwner := (DescentPackedZip.bank_read A.owner mem (slot.isLt.trans_le S.owner)
    (S.banks _ (by simp [Gather.banks]))).trans («public».owner t p)
  have rKind := (DescentPackedZip.bank_read A.kind mem (slot.isLt.trans_le S.kind)
    (S.banks _ (by simp [Gather.banks]))).trans («public».kind t p)
  have rPtr := (DescentPackedZip.bank_read A.pointer mem (slot.isLt.trans_le S.pointer)
    (S.banks _ (by simp [Gather.banks]))).trans («public».pointer t p)
  have rLive := (DescentPackedZip.bank_read A.live mem ((idx t).isLt.trans_le S.flags)
    (S.banks _ (by simp [Gather.banks]))).trans (active t)
  have nz : (1:Word w)≠0 := by
    intro eq
    have one : (1:Word w).val=1 := Fin.val_cast_of_lt wide
    exact Nat.one_ne_zero (by simpa only [one, Fin.val_zero] using congrArg Fin.val eq)
  simp only [expression, Expr.eval, rOwner, rPtr, rKind, rLive]
  have zeroRow : (0:Word w) =
      ((chunk (shaped (u:=u) (l:=l) (fun _ : Cube (u+l) => (0:Cell b)) p)).val : Word w) := by
    change (0:Word w) = ((chunk (fun _ : Cube l => (0:Cell b))).val : Word w)
    simp only [zero_word, Fin.val_zero, Nat.cast_zero]
  cases t with
  | inl vv=>
    obtain ⟨v,z⟩:=vv
    have load:=DescentPackedZip.bank_read A.sites mem ((DescentPackedWalsh.row v p).isLt.trans_le S.sites)
      (S.banks _ (by simp [Gather.banks]))
    by_cases h : depth v+z.val≤k
    · simpa [isLive,tag,realLoad,h,nz,Comparison.test,offset,load] using oldSite v p
    · simpa [isLive,realLoad,h,Comparison.test] using zeroRow
  | inr vv=>
    obtain ⟨v,j⟩:=vv
    have below : j.val*pitch+(DescentPackedWalsh.row v p).val<D*pitch := by
      calc _<j.val*pitch+pitch:=Nat.add_lt_add_left ((DescentPackedWalsh.row v p).isLt.trans_le S.width) _
           _=(j.val+1)*pitch:=(Nat.succ_mul ..).symm
           _≤_:=Nat.mul_le_mul_right _ j.isLt
    have load:=DescentPackedZip.bank_read A.flows mem (below.trans_le S.traffic) (S.banks _ (by simp [Gather.banks]))
    cases h:next (v,j) with
    | none=>simpa [isLive,realLoad,h,Comparison.test] using zeroRow
    | some z=>
      have moved : A.flows.base+(j.val*pitch+(DescentPackedWalsh.row v p).val)=
          (A.flows.base+j.val*pitch)+(DescentPackedWalsh.row v p).val := by omega
      simpa [isLive,tag,realLoad,h,nz,Comparison.test,offset] using
        load.trans ((congrArg mem moved).trans (oldFlow j v p))

end
end Hierarchy.DescentPackedRectangle

end OAI
