import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example : cvetkovic K4 = 1 := by
  unfold cvetkovic K4
  norm_num

end WrittenOnTheWallII.Test
