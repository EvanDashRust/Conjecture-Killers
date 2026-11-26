import Certificate

namespace Selfridge

/-- The positive-part sum and the squared-payoff tail, rounded upward. -/
def crossingFreshBudget : Rat :=
  321245590829925919/1000000000000000000 +
    (2535234506914557167526891/37321044789957361184384) *
      (2048425482480/1000000000000000000 + 300001/360000000000)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem crossing_budget_lt :
    independencePolynomials.toList.all (fun q => decide (0 < q)) = true ∧
    crossingFreshBudget < independencePolynomials[63]! := by decide +kernel

#print axioms crossing_budget_lt
end Selfridge
