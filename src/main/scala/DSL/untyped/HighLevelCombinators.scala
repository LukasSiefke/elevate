package DSL.untyped

import Core._
import HighLevelCombinators._
import apart.arithmetic.ArithExpr


object map {
  def apply(f: Phrase[ExpType -> ExpType]): Phrase[ExpType -> ExpType] =
    λ(x => map(f, x))

  def apply(f: Phrase[ExpType -> ExpType], x: Phrase[ExpType]) =
    Map(null, null, null, f, x)
}

object zip {
  def apply(lhs: Phrase[ExpType], rhs: Phrase[ExpType]) =
    Zip(null, null, null, lhs, rhs)
}

object split {
  def apply(n: ArithExpr): Phrase[ExpType -> ExpType] =
    λ(array => split(n, array))

  def apply(n: ArithExpr, array: Phrase[ExpType]): Split =
    Split(n, null, null, array)
}

object join {
  def apply(): Phrase[ExpType -> ExpType] = λ(array => join(array))

  def apply(array: Phrase[ExpType]): Join = Join(null, null, null, array)
}

object reduce {
  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)]): Phrase[(ExpType x ExpType) -> ExpType] =
    λ((init, array) => reduce(f, init, array))

  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)], init: Phrase[ExpType]): Phrase[ExpType -> ExpType] =
    λ(array => reduce(f, init, array))

  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)], init: Phrase[ExpType],
            array: Phrase[ExpType]): Reduce = {
    Reduce(null, null, null, f, init, array)
  }
}

object reduceSeq {
  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)]): Phrase[(ExpType x ExpType) -> ExpType] =
    λ((init, array) => reduceSeq(f, init, array))

  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)], init: Phrase[ExpType]): Phrase[ExpType -> ExpType] =
    λ(array => reduceSeq(f, init, array))

  def apply(f: Phrase[ExpType -> (ExpType -> ExpType)],
            init: Phrase[ExpType],
            array: Phrase[ExpType]) =
    ReduceSeq(null, null, null, f, init, array)
}

object iterate {
  def apply(k: ArithExpr, f: Phrase[`(nat)->`[ExpType -> ExpType]]): Phrase[ExpType -> ExpType] =
    λ(array => iterate(k, f, array))

  def apply(k: ArithExpr,
            f: Phrase[`(nat)->`[ExpType -> ExpType]],
            array: Phrase[ExpType]): Iterate =
    Iterate(null, null, k, null, f, array)
}

object gather {
  def apply(idxF: (ArithExpr, DataType) => ArithExpr) = λ(array =>
    Gather(null, null, idxF, array)
  )
}