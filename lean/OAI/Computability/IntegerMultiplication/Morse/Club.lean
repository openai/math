import OAI.Computability.IntegerMultiplication.Morse.Pilot

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits
variable {k w t:ℕ} (p:ℕ)(q:Word)(b:ℕ→Grain w)
abbrev Seat := List Dusk.Pair
abbrev Rows := List Seat
abbrev Deck (k t w:ℕ):=Face k → Fin t → Grain w

def slump (x:Fin t→Grain w):Seat:= List.ofFn (fun i=>Dusk.mark (x i))
def card (x:Deck k t w): Rows:=
  (PhaseL k).tab (fun v=> slump (x v))
abbrev card₀ := Grid.Orb × Grid.Orb
abbrev BlockT:=List card₀
abbrev Scroll:=List BlockT
def item (c:B) (v:Face k):Orb:=(tally p,Dusk.mark (get_ q b c v))
def shop (v:Face k):card₀:=(item p q b 0 v,item p q b 1 v)
def rowT (k:ℕ):= (PhaseL k).tab (shop p q b)
def scroll (p:ℕ) (q:Word) : (b:ℕ→Grain w)→ℕ→ Scroll
| _,0=>[]
| b,k+1=> rowT p q b k :: scroll p q (doubleBank b) k
@[simp] theorem scroll_len (k): (scroll p q b k).length=k := by
  induction k generalizing b <;> simp_all [scroll]
@[simp] theorem szT (k): (rowT p q b k).length=2^k := (Series.card ..).trans (phase_size k)
theorem szSlump (x:Fin t→Grain w):(Code.size (slump x))≤ t*(8*(w+1))+1 := by
  let v : (x:Fin t→Grain w)→Fin t→Tree:=fun x i=>send (Dusk.mark (x i))
  have h(x:Fin t→Grain w): stripe (Series.natural t) (v x)=send (slump x):= by
    dsimp only [v]; rw [stripe_eq']; unfold slump Series.tab Series.natural
    dsimp only [Series.fixed,List.finRange]
    simp [List.map_ofFn]
    rfl --?
  unfold Code.size
  rw [← h]
  have u:= stripe_size (Series.natural t) (v x) (8*(w+1)-1) (fun j=>by
    change Code.size (Dusk.mark _)≤_
    rw [Dusk.volume]; omega)
  rw [Series.count_natural,show 8*(w+1)-1+1=8*(w+1) by omega] at u; exact u
-- ledger need const per bit
theorem sheets (x:Deck k t w):
    size (card x) ≤ 16*2^k*(t+1)*(w+1) := by
  change (send ((PhaseL k).tab _)).count≤_
  rw [← stripe_eq']
  calc
    _ ≤ (PhaseL k).count*(t*(8*(w+1))+1+1)+1 :=
      stripe_size _ _ _ (fun j=>szSlump _)
    _ ≤ _ := by
      rw [phase_size]; have h : 0≤t*w*(2^k):=Nat.zero_le _; nlinarith [Nat.pow_pos (n:=k) (by decide:(0:ℕ)<2)]
theorem tea (v:p≤w+1)(k_: Face k)(a):
    size (item p q b a k_) ≤ 12*(w+1) := by
  unfold item
  rw [size_prod,Dusk.volume,size_tally,tally_length]; omega
theorem tariff (v:p≤w+1) (k): size (rowT p q b k)<32*2^k*(w+1) := by
  change (send ((PhaseL k).tab _)).count<_
  rw [← stripe_eq']
  calc
    _ ≤ (PhaseL k).count*(24*(w+1)+2)+1:= stripe_size _ _ (24*(w+1)+1) (fun j=>by
      change size (shop p q b j)≤_
      rw [shop,size_prod]; dsimp only; have x:=tea p q b v j 0; have e:= tea p q b v j 1; omega)
    _ < _:= by rw [phase_size]; nlinarith [Nat.pow_pos (n:=k) (by decide:(0:ℕ)<2)]
theorem grace (v:p≤w+1)(k):
    size (scroll p q b k) ≤ 32*2^k*(w+1) := by
  induction k generalizing b with
  | zero=> simp [scroll]; omega -- simp omega
  | succ k ih=> rw [scroll,size_cons,pow_succ]
                have := ih (doubleBank b)
                have x:= tariff p q b v k; nlinarith
structure Order where
  k:ℕ
  t:ℕ
  w:ℕ
  p:ℕ
  q:Bits.Word
  b:ℕ→Grain w
  x:Deck k t w
  ok:p≤w+1
noncomputable section
open IntegerMultiplication.Morse.Order
def prep (i:Order): Scroll × Rows:=(scroll i.p i.q i.b i.k,card i.x)
def ready(i:Order): Tree:=send (prep i)
def study(i:Order)(x:Deck i.k i.t i.w):Deck i.k i.t i.w:= fun v z=> pulse i.p i.q i.b (fun v=>x v z) v
def cure(i:Order):Rows:=card (study i i.x)
def react(i:Order):Tree:=send (cure i)
abbrev scale_(i:Order):ℕ:=2^i.k*(i.t+1)*(i.w+1)
abbrev pay (i:Order):ℕ:=scale_ i*tax i.w
abbrev lease (i:Order):= (pay i:ℝ)

theorem price0 (i:Order):1≤ scale_ i:= Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)) (by omega)
theorem price1 (i:Order): scale_ i≤pay i:=Nat.le_mul_of_pos_right _ (tax_pos _)
theorem price2 (i:Order):1≤pay i:=(price0 i).trans (price1 i)
theorem price3 (i:Order):1≤lease i:=by exact_mod_cast price2 i
theorem rates (i:Order) (x:Deck i.k i.t i.w):
    size (card x) ≤ 16*scale_ i := (sheets _).trans (le_of_eq (by unfold scale_; ring))
theorem menu (i:Order):
    size (scroll i.p i.q i.b i.k) ≤32*scale_ i := by
  calc
    _ ≤ _:=grace i.p i.q i.b i.ok _
    _ ≤ _ := by unfold scale_; have j : 0≤2^i.k*i.t*i.w:=Nat.zero_le _; nlinarith [Nat.pow_pos (n:=i.k) (by decide:(0:ℕ)<2),Nat.zero_le i.t]
theorem board (i:Order):
    (ready i).count ≤ 50*scale_ i := by
  change size (prep i)≤_
  rw [prep,size_prod]; dsimp only
  have := menu i; have := rates i i.x; have := price0 i; omega
theorem school (i:Order):
    (react i).count ≤ 16*scale_ i:=rates i _
end
end Morse

end IntegerMultiplication
end Computability
end OAI
