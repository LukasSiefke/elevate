package elevate.rise.rules

import elevate.core.{Failure, RewriteResult, Strategy, Success}
import elevate.rise.Rise
import rise.core._
import rise.core.primitives._
import rise.core.TypedDSL._

object lowering {

  // Straight-forward Lowering

  case object mapSeq extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case m@Map() => Success(MapSeq()(m.t) :: e.t)
      case _       => Failure(mapSeq)
    }
    override def toString = "mapSeq"
  }

  case object mapStream extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case m@Map() => Success(MapStream()(m.t) :: e.t)
      case _       => Failure(mapStream)
    }
    override def toString = "mapStream"
  }

  case object iterateStream extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case m@Map() => Success(IterateStream()(m.t) :: e.t)
      case _       => Failure(iterateStream)
    }
    override def toString = "iterateStream"
  }

  case object mapSeqUnroll extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case m@Map() => Success(MapSeqUnroll()(m.t) :: e.t)
      case _       => Failure(mapSeqUnroll)
    }
    override def toString = "mapSeqUnroll"
  }

  case class mapGlobal(dim: Int = 0) extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case Map() => Success(rise.OpenCL.TypedDSL.mapGlobal(dim) :: e.t)
      case _       => Failure(mapGlobal(dim))
    }
    override def toString = "mapGlobal"
  }

  case object reduceSeq extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case Reduce() => Success(TypedDSL.reduceSeq :: e.t)
      case _        => Failure(reduceSeq)
    }
    override def toString = "reduceSeq"
  }

  // todo shall we allow lowering from an already lowered reduceSeq?
  case object reduceSeqUnroll extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case Reduce() | ReduceSeq() => Success(TypedDSL.reduceSeqUnroll :: e.t)
      case _                      => Failure(reduceSeqUnroll)
    }
    override def toString = "reduceSeqUnroll"
  }

  // Specialized Lowering

  // only transforms maps which contain ForeignFunctions or mapSeqs
  case object mapSeqCompute extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      // (mapSeq λη1. (my_abs η1))
      case App(m @ Map(), l @ Lambda(_, App(ForeignFunction(_), _))) => Success(app(TypedDSL.mapSeq :: m.t, l) :: e.t)
      // (map λη1. ((mapSeq λη2. (my_abs η2)) η1))
      case App(m @ Map(), l @ Lambda(_, App(App(MapSeq(), _), _))) => Success(app(TypedDSL.mapSeq :: m.t, l) :: e.t)
      case _ => Failure(mapSeqCompute)
    }
    override def toString = "mapSeqCompute"
  }

  case class slideSeq(rot: SlideSeq.Rotate, write_dt: Expr) extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case Slide() => Success(nFun(sz => nFun(sp =>
        TypedDSL.slideSeq(rot)(sz)(sp)(untyped(write_dt))
      )) :: e.t)
      case _ => Failure(slideSeq(rot, write_dt))
    }
    override def toString = s"slideSeq($rot, $write_dt)"
  }

  // writing to memory

  // TODO: think about more complex cases
  case object mapSeqUnrollWrite extends Strategy[Rise] {
    import rise.core.types._
    def apply(e: Rise): RewriteResult[Rise] = e.t match {
      case ArrayType(_, _: BasicType) =>
        Success(app(TypedDSL.mapSeqUnroll(fun(x => x)), typed(e)) :: e.t)
      case _ =>
        Failure(mapSeqUnrollWrite)
    }
  }
}