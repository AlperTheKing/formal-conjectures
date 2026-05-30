import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph

namespace WrittenOnTheWallII.Test

example : residue Star5 = 5 := by
  unfold residue
  decide +kernel

end WrittenOnTheWallII.Test
