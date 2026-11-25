import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentWideOriginalCalendarBill

namespace OAI
/-! # Uniform admission and exact word charges of the initial physical tape -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentExterior DescentPackedEpochShelves DescentWideSeedFlags Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B ratio : ℕ)
local notation "a" => localSocketRate G t g
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g

theorem original_initial_dimensions (large : 20 ≤ B) (reserve : 2*a ≤ τ)
    (advert : 2*(a+(τ+κ+4))+Nat.clog 2 G.b*(t+1) ≤ B)
    (tailFit : 0+0+3+(a+5) ≤ τ)
    (widthFit : 2*((2+hostRate t reset*(t+1)+((t+1)*(hostRate t reset+capRate G t g+1)+11)+
      (0+1)+1)+5+a) ≤ B) (bus : 2 ≤ ratio) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M, 2^h ≤ M →
        let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let j:=headChunk G S
        let rest:=headRest G S k (tail τ J)
        let q:=2^j*(G.b^(t*J)*G.b)
        let W:=NativeBranch.binLimit (k:=k) S
        let piece:=h/(16*(q*W))
        let p:=W*piece
        let s:=S.firstWidth G.b p
        let w:=ratio*h
        let R:=S.copies
        10 ≤ h ∧ S.length ≤ M ∧ s ≤ h ∧ 0 < R ∧
          2*DescentSeedRoot.digitsNeeded s ≤ h ∧ 2*unit G.C ≤ h/2 ∧
          DescentExteriorShelf.tableBits j rest s ≤ h/2 ∧ 2^h ≤ 2*(M*R) ∧
          R=2^(j+(j+rest)) ∧ h ≤ 32*((2^j)*s) ∧ 2^J ≤ s ∧
          q*(W*piece) ≤ w ∧ h+1 ≤ w ∧ originalBill S G.C B h*2^J ≤ 2*(M*(R*s)) :=by
  have Bpos:0 < B:=by omega
  filter_upwards [early_native_packing G t f g reset τ B large reserve advert,
    chosen_exterior_head_widths G t f g reset τ B large reserve advert,
    original_calendar_price G t f g reset G.C τ B a tailFit Bpos widthFit,
    eventually_ge_atTop (max 10 (max (2*(t+1)) (4*unit G.C)))] with h packing bits funds threshold
  intro J M lower S k j rest q W piece p s w R
  obtain ⟨_,copies,time,limit,bulk⟩:=packing M
  obtain ⟨seed,port,_⟩:=bits M
  have host:0 < h:=by omega
  have wide:h+1 ≤ w:=by
    have:=Nat.mul_le_mul_right h bus
    dsimp only [w]
    omega
  have first:s ≤ h:=by
    have big:s ≤ 2^j*s:=Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)
    change 16*(2^j*s) ≤ h at limit
    omega
  have floor:S.length ≤ M:=by
    have leLog:Nat.log 2 h ≤ h:=Nat.log_le_self _ _
    have half:2*J ≤ h:=by
      have paid:=Nat.div_mul_le_self (Nat.log 2 h) (2*B)
      have fee:=Nat.mul_le_mul_left J (show 2 ≤ 2*B by omega)
      change J*(2*B) ≤ Nat.log 2 h at paid
      omega
    change (t+1)*J ≤ M
    calc
      _ ≤ 2^(h/2)*2^(h/2) := Nat.mul_le_mul
        ((show t+1 ≤ h/2 by omega).trans Nat.lt_two_pow_self.le)
        ((show J ≤ h/2 by omega).trans Nat.lt_two_pow_self.le)
      _ ≤ 2^h := by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := lower
  have Rpos:0 < R:=by change R=2^(j+(j+rest)) at copies;rw [copies];exact Nat.two_pow_pos _
  have support:2^h ≤ 2*(S.initialSites*R):=lower.trans (by
    change M ≤ 2*(M*R)
    have:=Nat.le_mul_of_pos_right M Rpos
    omega)
  have sockets:2^j ≤ scale J a:=(native_socket_scale G t J f g reset M τ).2.2.1
  have paid:=funds M (2^j) s (Nat.two_pow_pos _) sockets bulk
  have mode:q*(W*piece) ≤ w:=by
    have buy:piece*(16*(q*W)) ≤ h:=Nat.div_mul_le_self ..
    have same:piece*(16*(q*W))=16*(q*(W*piece)):=by ring
    rw [same] at buy
    omega
  exact ⟨by omega,floor,first,Rpos,seed,by omega,port,support,copies,bulk,time,mode,wide,paid⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
