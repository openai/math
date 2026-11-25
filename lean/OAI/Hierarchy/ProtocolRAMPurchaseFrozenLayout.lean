import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseKey
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenCount
import OAI.Hierarchy.ProtocolRAMPurchaseCapacity

namespace OAI
/-! # Disjoint memory ranges for all signs at one common price snapshot -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation Filter
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def firstBase (z d k extra : ℕ) := heapEnd z d copies+initialFactor d k extra*2^z

def start (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :=
  firstBase z d k extra+i.val*blockSize z d S.degree depth

def stop (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :=
  firstBase z d k extra+(i.val+1)*blockSize z d S.degree depth

def config (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) : PassConfig k :=
  {PurchaseCT.config k extra depth (stage i) with start:=start S extra depth i}

abbrev board (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :=
  geom S (stage i) (config S extra depth i)

abbrev desc (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :=
  let t := stage i;let c := config S extra depth i
  PurchaseStage.layout (embedded S t c) (sign S t c) (2^z) depth

def flagsBase (S : PurchaseSampler) (z d k extra depth : ℕ) :=
  firstBase z d k extra+count z d k*blockSize z d S.degree depth+2*(paths z S.degree depth+1)

def flagBank (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) : Bank :=
  ⟨PurchaseStage.decisionBase (desc S extra depth i),ProtocolRAMPurchaseSampler.bits (paths z S.degree depth)⟩

theorem disjoint (S : PurchaseSampler) (extra depth : ℕ) {i j : Key z d k} (ne : i≠j) :
    stop S extra depth i ≤ start S extra depth j ∨ stop S extra depth j ≤ start S extra depth i := by
  rcases lt_or_gt_of_ne ne with before | after
  · exact Or.inl (Nat.add_le_add_left (Nat.mul_le_mul_right _ before) _)
  · exact Or.inr (Nat.add_le_add_left (Nat.mul_le_mul_right _ after) _)

theorem size_le (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) (hd : 1≤d) :
    (board S extra depth i).endAddress ≤ stop S extra depth i := by
  let L := board S extra depth i
  let sh := stageAt z d (stage i)
  let : Nonempty sh.Group := ⟨(advisedStage z d (Equiv.refl _) (stage i)).group 0⟩
  have proof := template_dyadic hd sh (List.get_mem ..)
  have bound := L.end_linear (4^(rounds d+1)) (Nat.two_pow_pos z) (Fintype.card_pos (α:=sh.Group))
    ((Nat.two_pow_pos _).trans_le proof.span_lower) rfl proof.2
  have small : Layout.linearFactor (4^(rounds d+1)) S.degree depth*2^z≤blockSize z d S.degree depth :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  change L.endAddress ≤ start S extra depth i+Layout.linearFactor (4^(rounds d+1)) S.degree depth*2^z at bound
  change L.endAddress ≤ stop S extra depth i
  simp only [stop,start,Nat.succ_mul] at bound ⊢
  omega

theorem final_after (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    stop S extra depth i ≤ firstBase z d k extra+count z d k*blockSize z d S.degree depth :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _

def roomFactor (d D k extra depth : ℕ) :=
  initialFactor d k extra + (2*rounds d+1)*(2*k)*factor d D depth + 2*(D^depth+1)+
    (2*rounds d+1)*(2*k)*D^depth

theorem room (S : PurchaseSampler) (d k extra depth : ℕ) : ∀ᶠ z : ℕ in atTop,
    flagsBase S z d k extra depth+count z d k*paths z S.degree depth<2^wordBits z d copies := by
  filter_upwards [eventually_append_room d copies (roomFactor d S.degree k extra depth)] with z enough
  apply Nat.lt_of_le_of_lt _ enough
  simp only [flagsBase,firstBase,count_eq,blockSize,paths,roomFactor]
  have pos := Nat.two_pow_pos z
  ring_nf; omega

private theorem before (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (PurchaseCT.config k extra depth (stage i)).start ≤ start S extra depth i := by
  rw [PurchaseCT.config_start]; exact Nat.le_add_right ..

theorem ready (S : PurchaseSampler) (d k extra depth : ℕ) (hd : 1≤d) :
    ∀ᶠ z : ℕ in atTop, ∀ i : Key z d k, Ready S (stage i) (config S extra depth i) := by
  filter_upwards [eventually_ready d k extra depth hd S,room S d k extra depth] with z each fits
  intro i
  have orig := each (stage i)
  have order := before S extra depth i
  have e := (size_le S extra depth i hd).trans (final_after S extra depth i)
  let c := config S extra depth i
  have goalRoom : (board S extra depth i).endAddress<2^wordBits z d copies := by dsimp only [flagsBase] at fits;omega
  have enlarge {b : Bank} (old : b.Fits (wordBits z d copies) (PurchaseCT.config k extra depth (stage i)).start) :
      b.Fits (wordBits z d copies) c.start := ⟨old.1,old.2.1,old.2.2.trans order⟩
  exact ⟨orig.heap,orig.raw,orig.stocks,enlarge orig.threshold,
    ⟨enlarge orig.ct.group,enlarge orig.ct.input,enlarge orig.ct.output⟩,
    orig.wide,orig.directions,orig.degree,orig.sockets,goalRoom⟩

theorem flag_fit (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) (hd : 1≤d)
    (space : flagsBase S z d k extra depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    (flagBank S extra depth i).Fits (wordBits z d copies) (flagsBase S z d k extra depth) := by
  have capacity := ProtocolRAMPurchaseSampler.span_le (paths z S.degree depth)
  have slab := (size_le S extra depth i hd).trans (final_after S extra depth i)
  have addr : PurchaseStage.decisionBase (desc S extra depth i)≤(board S extra depth i).endAddress := Nat.le_add_right ..
  change 0<2^_ ∧ ProtocolRAMPurchaseSampler.span _<2^_ ∧
    PurchaseStage.decisionBase (desc S extra depth i)+ProtocolRAMPurchaseSampler.span _≤_
  dsimp only [flagsBase] at space ⊢
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

end
end Hierarchy.ProtocolRAM.PurchaseFrozen

end OAI
