import OAI.Hierarchy.DescentOrdinaryBookMouthRate
import OAI.Hierarchy.DescentSeedTokenWidths

namespace OAI
/-! The small numerical parameters of every ordinary primitive update satisfy one
bound fixed before selecting the input size, tail length, slack or date. -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentDatedSeedStartup
open DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def primitiveLocalRate (t f g reset : ℕ) :=
  8+3*bookMouthRate G t f g reset+initialDegreeMax t+
    (stageNumbers G t 0 f g reset 0 0).localTokenExponent

private theorem localRate_parts (width dictionary capDigits block cost keys degree tokens : ℕ) :
    let mouth := 2048+width+(dictionary+2)+(8+capDigits)+block+cost+keys+4
    let total := 8+3*mouth+degree+tokens
    8+capDigits ≤ total ∧ width ≤ total := by
  dsimp only
  omega

theorem primitive_date_local (op : RotorSpec) (t f g reset τ B drift degreeMax : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀fund i p degree seats (prior : DatePorts),
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset fund (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let d:=DonorDate.atDate G S g k i p
      let book:=atDate G S op g k i p (tail τ J) drift degree h seats prior
      let bank:=scale J (primitiveLocalRate G t f g reset)
      p≤h → degree≤degreeMax → prior.nodes≤S.retainedNodes → S.firstWidth G.b p≤h →
      d.degree+1≤bank ∧ d.cap≤bank ∧ 2^k≤bank ∧ S.retainedNodes≤bank ∧ prior.nodes≤bank ∧
        printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op≤bank ∧ book.vector.lows≤bank:=by
  filter_upwards [mouth_fields_at G op t f g reset τ B drift degreeMax den,
    DescentDatedSeedStartup.primitive_rate G op B den] with h shape print
  intro fund i p degree seats prior J S k d book bank fit deg count seed
  let c:=primitiveLocalRate G t f g reset
  have raise {a : ℕ} (leq : a≤c) : scale J a≤bank:=
    Nat.pow_le_pow_right (n:=2) (by decide) (Nat.mul_le_mul_right _ leq)
  have scalar {a : ℕ} (leq : a≤c) : a≤bank:=
    leq.trans ((Nat.le_mul_of_pos_right c (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le)
  have dlim : d.degree≤ initialDegreeMax t:=seed_degree t G.b _
  obtain ⟨capPart, widthPart⟩ := localRate_parts
    (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)
    (2^DescentHostDegree.packExponent 20 (initialDegreeMax t)) (((capPeriod G.b t g).map (·+1)).prod)
    G.b G.C G.k (initialDegreeMax t) (stageNumbers G t 0 f g reset 0 0).localTokenExponent
  have caps:=DescentNamedFundedChart.capPrefix G.b t g J i
  have klen : k≤(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)*(J+1):=groupBits_linear ..
  have ptr : S.retainedNodes≤bank:=(S.capacities_scale G).1.trans (raise (by
    change (stageNumbers G t 0 f g reset 0 0).localTokenExponent≤_;dsimp only [c,primitiveLocalRate];omega))
  have hz : S.grainAt G.b p 0≤S.firstWidth G.b p:=Nat.le_mul_of_pos_right _ (by have:=G.paid;omega : 0<G.b)
  refine ⟨(Nat.succ_le_succ dlim).trans (scalar (by dsimp only [c,primitiveLocalRate];omega)),
    caps.trans (raise capPart),?_,ptr,count.trans ptr,
    (print _ _ hz seed).1.trans (raise (by dsimp only [c,primitiveLocalRate];omega)),?_⟩
  · exact (Nat.pow_le_pow_right (n:=2) (by decide) klen).trans (raise widthPart)
  · exact (shape fund i p degree seats prior fit deg).1.trans (raise (by dsimp only [c,primitiveLocalRate];omega))

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
