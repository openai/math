import OAI.Hierarchy.DescentDonorScale

namespace OAI
/-! # Coefficient-independent size limits for every real donor and matching field -/
namespace Hierarchy.DescentCompiler.TerminalScale
namespace AgeBound
variable {ι : Type*} {age r D cap short names units prof : ι→ℕ}

/-- The original cable packing, hit flags, two relative charts, fresh lookup and all
eleven raw subroles fit a single explicitly bounded amount per logical group. -/
def laneAmount (r D cap short names units prof : ℕ) :=
  let ports:=2*cap
  let raw:=1+short*(r+(r*ports+D*r))
  let link:=Nat.clog 2 (D+1)
  let ticket:=Nat.clog 2 (cap+1)
  let cable:=(link+(ticket+(ticket+(ticket+2))))*(r*ports)
  let owner:=((max short (Nat.clog 2 (max r D+1))*3)*r)*(D+1)
  let breadth:=(D+1)^4
  let chart:=Nat.clog 2 (breadth+1)*breadth
  let fresh:=units*((r*cap)*8)
  let total:=((raw+cable)+(owner+chart))+(chart+fresh)
  let bins:=1+D*r
  let entries:=r*bins*ports
  let digit:=max prof (Nat.clog 2 (2+entries+bins+(D+1)*r+r*ports))
  let pairs:=r*entries
  let source:=4+5*(3+1+names)+10*units
  let output:=digit*(1+pairs*12)
  max (max total ((r*cap)*max source ((2+units)*11)))
    (max (1+raw+output+(digit+1)*(pairs*6)) (2*total+1))

theorem lane_amount (rows : AgeBound age r) (degree : AgeBound age D)
    (caps : AgeBound age cap) (raw : AgeBound age short) (labels : AgeBound age names)
    (width : AgeBound age units) (profile : AgeBound age prof) :
    AgeBound age (fun x=>laneAmount (r x) (D x) (cap x) (short x) (names x) (units x) (prof x)) := by
  let c:=AgeBound.const age
  let ports:=(c 2).mul caps
  let roster:=(c 1).add (raw.mul (rows.add ((rows.mul ports).add (degree.mul rows))))
  let link:=(degree.add (c 1)).clog
  let ticket:=(caps.add (c 1)).clog
  let cable:=(link.add (ticket.add (ticket.add (ticket.add (c 2))))).mul (rows.mul ports)
  let owner:=(((raw.maximum (((rows.maximum degree).add (c 1)).clog)).mul (c 3)).mul rows).mul (degree.add (c 1))
  let breadth:=(degree.add (c 1)).pow 4
  let chart:=((breadth.add (c 1)).clog).mul breadth
  let fresh:=width.mul ((rows.mul caps).mul (c 8))
  let total:=((roster.add cable).add (owner.add chart)).add (chart.add fresh)
  let bins:=(c 1).add (degree.mul rows)
  let entries:=(rows.mul bins).mul ports
  let digit:=profile.maximum ((((((c 2).add entries).add bins).add ((degree.add (c 1)).mul rows)).add
    (rows.mul ports)).clog)
  let pairs:=rows.mul entries
  let source:=((c 4).add ((c 5).mul (((c 3).add (c 1)).add labels))).add ((c 10).mul width)
  let output:=digit.mul ((c 1).add (pairs.mul (c 12)))
  exact (total.maximum ((rows.mul caps).mul (source.maximum (((c 2).add width).mul (c 11))))).maximum
    (((((c 1).add roster).add output).add ((digit.add (c 1)).mul (pairs.mul (c 6)))).maximum
      (((c 2).mul total).add (c 1)))

/-- Widths of the literal table indices depend on the true cap, radix and fixed role widths. -/
theorem normalized_amount (rows : AgeBound age r) (degree : AgeBound age D)
    (caps : AgeBound age cap) (raw : AgeBound age short) (labels : AgeBound age names)
    (profile : AgeBound age prof) (b C pad : ℕ) :
    AgeBound age (fun x=>laneAmount (r x) (D x) (cap x) (short x) (names x)
      (Nat.clog 2 (max (cap x*b) (C+1+pad)+1)) (prof x)) := by
  apply lane_amount rows degree caps raw labels _ profile
  exact (((caps.mul (const age b)).maximum (const age (C+1+pad))).add (const age 1)).clog

end AgeBound
end Hierarchy.DescentCompiler.TerminalScale

end OAI
