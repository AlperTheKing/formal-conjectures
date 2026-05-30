import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example : C6.edist (0 : Fin 6) (3 : Fin 6) = 3 := by
  norm_num [C6]

example : maxEccentricity C6 = 3 := by
  unfold maxEccentricity eccentricity
  norm_num [C6]

end WrittenOnTheWallII.Test
