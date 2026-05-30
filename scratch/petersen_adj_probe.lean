import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example : PetersenGraph.Adj (0 : Fin 10) (1 : Fin 10) := by
  decide +kernel

example : PetersenGraph.Adj (0 : Fin 10) (2 : Fin 10) := by
  decide +kernel

end WrittenOnTheWallII.Test
