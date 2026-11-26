import Std

namespace Selfridge

def stages : List (Nat × Rat) :=
  [(2, 1/9), (4, 0), (8, 1/4), (10, 1/5), (14, 3/7), (16, 3/8),
   (20, 3/10), (26, 1/2), (28, 1/2), (34, 7/17), (38, 7/19), (40, 7/20),
   (44, 7/22), (50, 1/2), (56, 1/2), (58, 1/2), (64, 15/32), (68, 15/34)]

def stage (size : Nat) (δ : Rat) (hits : Nat) (v₀ v₁ : Rat) : Rat :=
  let load : Rat := (2 * ((2 : Nat) ^ hits - 1) : Nat) / (size : Rat)
  let cap := 1 / (1 - δ)
  let adaptiveCap := 1 / (1 - min load δ)
  let increment := (v₁ - v₀) / (size : Rat)
  cap * max 0 (load - δ) + v₀ + cap * increment - (cap - adaptiveCap) * min increment (1 - δ)

def certificate (schedule : List (Nat × Rat)) : Array Rat :=
  schedule.foldr
    (fun (size, δ) future =>
      (List.range (future.size - 1)).toArray.map fun hits =>
        stage size δ hits future[hits]! future[hits + 1]!)
    (Array.replicate (schedule.length + 1) 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem certificate_lt : (certificate stages)[0]! < 9991/10000 := by decide +kernel

/-- Outward-rounded group masses emitted by `harrington_obstruction.py`.
A mask records the old prime coordinates on which a group depends. -/
def groupMassScaled : Array Nat := #[
  0, 34846, 0, 12811, 0, 9345, 1354, 3427,
  0, 70512820513, 97934473214, 24483618304, 39262820700, 17995459435, 24993693730, 6248423433,
  0, 55084745763, 41195857136, 19126647889, 56232344735, 14058086184, 19525119755, 4881279939,
  31073446328, 7768361582, 10789391117, 2697347780, 7930202463, 1982550616, 2753542530, 688385633,
  0, 1968506133, 46478565312, 11619641328, 34161745469, 8540436368, 11861717211, 2965429303,
  18877448012, 4719362003, 6554669468, 1638667367, 4817682054, 1204420514, 1672806274, 418201569,
  14747097291, 3686774323, 5120519908, 1280129977, 3763582128, 940895532, 1306799354, 326699839,
  2079718849, 519929713, 722124603, 180531151, 530761583, 132690396, 184292217, 46073055]

def independencePolynomials : Array Rat :=
  (List.range 63).foldl (fun previous index =>
    let mask := index + 1
    let first := ((List.range 6).find? fun i => mask.testBit i).getD 0
    let bit := 2 ^ first
    let rest := mask - bit
    let polynomial := (List.range (rest + 1)).foldl (fun result subset =>
      if (subset &&& rest) == subset then
        result - (groupMassScaled[subset + bit]! : Rat) / 1000000000000 * previous[rest - subset]!
      else result) previous[rest]!
    previous.push polynomial) #[1]

def harringtonFreshBudget : Rat :=
  315550625847030884/1000000000000000000 +
    (2535234506914557167526891/37321044789957361184384) * (45250986140828/1000000000000000000 + 1/299999)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem harrington_budget_lt :
    independencePolynomials.toList.all (fun q => decide (0 < q)) = true ∧
    harringtonFreshBudget < independencePolynomials[63]! := by decide +kernel

#print axioms certificate_lt
#print axioms harrington_budget_lt
end Selfridge
