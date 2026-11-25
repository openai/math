import OAI.Computability.MultitapeWeakETH.SwitchWord

/-! # Recovering the two observations and the unused outgoing bit at each switch offset -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open IntegerMultiplication Code CNFNetwork CNFNetwork.SyntaxProgram CNFNetwork.SiteCheck
open NearSquareRoot.Benes VPVNP Compression
noncomputable section

abbrev Column := (StageKey × StageKey) × (Tally × Tally × Bits.Word) × FourBanks
abbrev OffsetQuery := Column × Tally
abbrev Row := Bool × Bool × Bool

private def addressBytes (q : OffsetQuery) := q.1.2.1.2.2 ++ field (q.1.2.1.2.1,q.2)

private theorem addressBytes_poly : Poly addressBytes :=
  (show Poly (fun q : OffsetQuery => q.1.2.1.2.2) by fun_prop).app
    ((show Poly (fun q : OffsetQuery => (q.1.2.1.2.1,q.2)) by fun_prop).compose field_poly)

private def chooseBank (q : Bool × Bits.Word × Bits.Word) := bif q.1 then q.2.2 else q.2.1

private theorem chooseBank_poly : Poly chooseBank := Poly.choose (by fun_prop) (by fun_prop) (by fun_prop)

/-- Outgoing register, discarded outgoing bit, and incoming register. The
incoming offset is evaluated at the predecessor's preimage address. -/
def rowAt (q : OffsetQuery) : Row :=
  let addr := addressBytes q
  let out := port (q.1.1.1,addr)
  let prev := move (q.1.1.2,addr)
  let inc := port (q.1.1.2,prev)
  let banks := q.1.2.2
  (Iter.pick false (chooseBank (out,banks.1),q.2),
   Iter.pick false (chooseBank (!out,banks.1),q.2),
   atOffset ((q.1.2.1.1,prev),chooseBank (inc,banks.2)))

theorem rowAt_poly : Poly rowAt := by
  have now := ((show Poly (fun q : OffsetQuery => q.1.1.1) by fun_prop).pair addressBytes_poly).compose port_poly
  have prior : Poly (fun q : OffsetQuery => q.1.1.2) := by fun_prop
  have pre := (prior.pair addressBytes_poly).compose move_poly
  have inc := (prior.pair pre).compose port_poly
  have out : Poly (fun q : OffsetQuery => q.1.2.2.1) := by fun_prop
  have offset (f : OffsetQuery → Bool) (hf : Poly f) := (((hf.pair out).compose chooseBank_poly).pair Easy.snd.poly).compose (Iter.facile false).poly
  have ib := (inc.pair (show Poly (fun q : OffsetQuery => q.1.2.2.2) by fun_prop)).compose chooseBank_poly
  exact (offset _ now).pair ((offset _ (now.compose Iter.negate.poly)).pair
    ((((show Poly (fun q : OffsetQuery => q.1.2.1.1) by fun_prop).pair pre).pair ib).compose atOffset_poly))

def rows (q : Column) := (Iter.lineup (ruler q.2.2.1.1)).map fun i => rowAt (q,i)

theorem rows_poly : Poly rows := by
  have b : Easy (fun q : Column => q.2.2.1.1) := by fun_prop
  exact (Poly.identity.pair ((Easy.ruler b).poly.compose Iter.poly_line)).compose (Poly.push default [] rowAt_poly)

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)
variable (v : site m g) (h : (state stages a g l).network.Half v)

def physicalColumn : Column :=
  let keys (i : Fin (m+2)) := key (g+l) t (stages i).1 (stages i).2
  ((keys v.1,keys ((finRotate _).symm v.1)),(tally g,tally l,laneBytes v.2),
    splitPacket (tally (2^l),PairSimulation.NodeArguments.packed (state stages a g l) v h))

private theorem choose_eq (b : Bool) (f : Bool → Fin (2^l) → Bool) :
    chooseBank (b,List.ofFn (f false),List.ofFn (f true)) = List.ofFn (f b) := by cases b <;> rfl

variable {p : Equiv.Perm (Word (g+l))} (repr : RawRepresents p t)
  (bound : ∀ j, (stages j).2 < g+l)

include repr bound

theorem rowAt_eq (i : Fin (2^l)) :
    rowAt (physicalColumn stages t v h,tally i.val) =
      (emit stages t ha v h i,bank stages ha v h false (!(control stages t v.1 (addressAt v.2 i))) i,
        receive stages t ha v h i) := by
  let prev := (finRotate _).symm v.1
  let x := addressAt v.2 i
  let y := (switchAt stages t prev).symm x
  let q := physicalColumn stages t v h
  have addr : addressBytes (q,tally i.val) = List.ofFn x := by
    rw [bytes_addressAt]
    change laneBytes v.2 ++ field (tally l,tally i.val) = _
    rw [field_eq]
    rfl
  have pre : move (q.1.2,List.ofFn x) = List.ofFn y := move_eq repr _ _ (bound prev) x
  have pc (u : Fin (m+2)) (z : Word (g+l)) :
      port (key (g+l) t (stages u).1 (stages u).2,List.ofFn z) = control stages t u z :=
    port_eq repr _ _ (bound u) z
  have col : q.2.2 = _ := splitPacket_eq stages ha v h
  change rowAt (q,tally i.val) = _
  simp only [rowAt,addr,pre,col]
  change (Iter.pick false (chooseBank (port (key _ _ _ _,_),_),_),
    Iter.pick false (chooseBank (!(port (key _ _ _ _,_)),_),_),
    atOffset ((tally g,List.ofFn y),chooseBank (port (key _ _ _ _,_),_))) = _
  rw [pc,pc]
  simp only [choose_eq,Iter.entry,atOffset_eq,emit_bank,receive_bank]
  rfl

theorem rows_eq : rows (physicalColumn stages t v h) =
    List.ofFn fun i => (emit stages t ha v h i,bank stages ha v h false (!(control stages t v.1 (addressAt v.2 i))) i,
      receive stages t ha v h i) := by
  have len : ruler (physicalColumn stages t v h).2.2.1.1 = tally (2^l) := by
    rw [← recover_tally (ruler _),ruler_length]
    change tally (splitPacket _).1.1.length = _
    rw [splitPacket_eq stages ha,List.length_ofFn]
  simp only [rows,len,Iter.lined,List.map_ofFn,Function.comp_def,rowAt_eq stages t ha v h repr bound]

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
