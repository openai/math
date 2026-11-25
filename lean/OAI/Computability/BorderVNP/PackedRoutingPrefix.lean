import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # Executing the private-prefix pass on the emitted geometry words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D s m n C d k w J A : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}
variable (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
variable (original : Fin J → N.Site) (live : Fin A → P)

private theorem prefix_le (owners : ℕ → ℕ) (desc i c : ℕ) : PrivatePlacement.prefixCounts owners desc i c ≤ i*desc := by
  unfold PrivatePlacement.prefixCounts
  calc
    _ ≤ ∑ _j ∈ Finset.range i, desc := Finset.sum_le_sum fun j _ => by split <;> omega
    _ = i*desc := by simp

include net code fit

/-- Numerical address room and the real emitted owners/counts imply every bounded-word
premise of the native placement loop. -/
theorem Image.privateFit {W : ℕ} (head origin desc gap : ℕ) (before : ℕ → ℕ)
    (img : Image F (siteID ∘ original) (portID ∘ live) x origin before)
    (headRoom : head+92 < 2^W) (control : before (head+92)+8 < 2^W)
    (arrayRoom : (bases origin m C J).livePairs < 2^W)
    (bankRoom : ∀ c, suppliedSize N cell c+gap+J*desc < 2^W) :
    (privateLayout head origin m C J desc gap).Fits W before := by
  let b := bases origin m C J
  let l := privateLayout head origin m C J desc gap
  have h := img.placed N cell aux siteID edgeID portID F net code fit original live origin before
  have owner (i : Fin J) : l.owner before i = (cell (original i)).val := by
    simpa only [l,privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm 2 i.val] using
      congrArg Prod.fst (h.1 i)
  constructor
  case frame => exact headRoom
  case control => exact control
  case owners => intro i hi; rw [owner ⟨i,hi⟩]; exact Fin.isLt _
  case values =>
    intro i hi
    let p : Fin J := ⟨i,hi⟩
    let c := cell (original p)
    have a := owner p
    have total := h.2.1 c
    have initial : l.supplied = b.supplied := by dsimp [l,b,privateLayout,bases,PrivatePlacement.Layout.supplied]; omega
    have charge := bankRoom c
    have one := prefix_le (l.owner before) desc i c.val
    have bound := Nat.mul_le_mul_right desc (show i+1 ≤ J from hi)
    rw [Nat.add_mul,Nat.one_mul] at bound
    change before (l.supplied+l.owner before i)+gap+PrivatePlacement.prefixCounts (l.owner before) desc i (l.owner before i) < 2^W ∧
      PrivatePlacement.prefixCounts (l.owner before) desc i (l.owner before i)+desc < 2^W
    change l.owner before i = c.val at a
    rw [a,initial,total]
    omega
  all_goals dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied] at *
  all_goals omega

/-- Start at the real reconstructed word memory. The fixed prefix program returns
the true per-cell description placement with its linear tick charge. -/
theorem Image.private_run {W : ℕ} (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8)
    (s₀ : Bank W) (mz : Memory W) (origin desc gap : ℕ)
    (img : Image F (siteID ∘ original) (portID ∘ live) x origin (readings mz))
    (header : Header (pub 0).val origin m C J (readings mz))
    (entries : readings mz ((pub 0).val+66) = J) (descField : readings mz ((pub 0).val+69) = desc)
    (gapField : readings mz (readings mz ((pub 0).val+92)+8) = gap)
    (headRoom : (pub 0).val+92 < 2^W) (control : readings mz ((pub 0).val+92)+8 < 2^W)
    (arrayRoom : (bases origin m C J).livePairs < 2^W)
    (bankRoom : ∀ c, suppliedSize N cell c+gap+J*desc < 2^W) :
    let l := privateLayout (pub 0).val origin m C J desc gap
    BoundedRun pub mac PrivatePlacement.program s₀ mz (PrivatePlacement.setup.slots+(J*15+1))
      (fun z => l.Image (readings mz) J z.mem) := by
  intro l
  apply PrivatePlacement.run_program pub mac l s₀ mz
    (img.privateFit N cell aux siteID edgeID portID F net code fit original live (pub 0).val origin desc gap
      (readings mz) headRoom control arrayRoom bankRoom) rfl (privateFields header entries descField gapField)
  intro c hc
  simpa only [l,privateLayout,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied,bases,Nat.mul_comm 2 m] using
    img.counterAt ⟨c,hc⟩

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
